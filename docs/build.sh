#!/usr/bin/env bash
# Build the audited-surface docs site and emit a self-contained single-page HTML site.
# Usage:
#   docs/build.sh            build once
#   docs/build.sh --serve    build once, then serve
#   docs/build.sh --watch    build + serve, then rebuild and live-reload on source changes
#   docs/build.sh --pdf      build the PDF instead of the site (needs xelatex + latexmk)
# Override the start port with PORT=NNNN.
set -euo pipefail
cd "$(dirname "$0")/.."             # repo root

OUT=docs/_out
HTML="$OUT/html-single"
TEX="$OUT/tex"

build_once() {
  lake build docs
  rm -rf "$OUT"
  lake exe docs --output "$OUT"
  # Ship the image assets alongside the page (Verso references them relatively).
  find docs/assets -type f -exec cp {} "$HTML/" \;
}

# Emit Verso's TeX output and compile it with xelatex (required: the preamble uses
# `fontspec`). Two fixups bridge the gap between Verso's TeX and this machine:
#   * figures are SVGs, which LaTeX cannot include — convert them to PDF;
#   * the mono font is requested by family name, which fontspec resolves through the OS font
#     manager; that doesn't know TeX Live's copy, so load the shipped files by name instead.
build_pdf() {
  lake build docs
  rm -rf "$OUT"
  lake exe docs --output "$OUT" --with-tex --without-html-single

  if command -v rsvg-convert >/dev/null 2>&1; then
    find docs/assets -name '*.svg' -exec sh -c \
      'rsvg-convert -f pdf -o "$1/$(basename "$2" .svg).pdf" "$2"' _ "$TEX" {} \;
    perl -0pi -e 's{\\includegraphics\{"([^"]+)\.svg"\}}
                   {\\includegraphics[width=\\textwidth]{$1.pdf}}g' "$TEX/main.tex"
  else
    echo "warning: rsvg-convert not found — building without the SVG figures" >&2
    perl -0pi -e 's{\\includegraphics\{"[^"]+\.svg"\}}{\\emph{[figure omitted]}}g' "$TEX/main.tex"
  fi
  find docs/assets -type f ! -name '*.svg' -exec cp {} "$TEX/" \;

  mono='\setmonofont{DejaVuSansMono.ttf}[BoldFont=DejaVuSansMono-Bold.ttf,'
  mono+='ItalicFont=DejaVuSansMono-Oblique.ttf,BoldItalicFont=DejaVuSansMono-BoldOblique.ttf]'
  MONO="$mono" perl -0pi -e 's{\\setmonofont\{DejaVu Sans Mono\}}{$ENV{MONO}}e' "$TEX/main.tex"

  if ! command -v latexmk >/dev/null 2>&1 || ! command -v xelatex >/dev/null 2>&1; then
    echo "Wrote $TEX/main.tex — install a LaTeX distribution (xelatex + latexmk) to compile it"
    return 0
  fi
  # Quiet on success; on failure the captured log is the diagnosis.
  if ! (cd "$TEX" && latexmk -xelatex -halt-on-error -interaction=nonstopmode main.tex) \
      >"$OUT/latex.log" 2>&1; then
    cat "$OUT/latex.log" >&2
    echo "PDF build failed — see $TEX/main.log" >&2
    exit 1
  fi
  echo "Wrote $TEX/main.pdf"
}

# First free port at or above ${PORT:-8017}, so a leftover server doesn't cause
# "Address already in use".
pick_port() {
  python3 - "${PORT:-8017}" <<'PY'
import socket, sys
p = int(sys.argv[1])
while p < 65536:
    with socket.socket() as s:
        if s.connect_ex(("127.0.0.1", p)) != 0:
            print(p); break
    p += 1
else:
    sys.exit("no free port found")
PY
}

# md5 over the *contents* of the sources a rebuild depends on: the doc sources and image
# assets, plus the audited files (directly under ApcOptimizer/) whose docstrings the page
# splices. Hashing contents (not mtimes) means swapping an image is noticed.
watch_sig() {
  python3 - <<'PY'
import os, hashlib
h = hashlib.md5()
exts = (".lean", ".svg", ".png", ".jpg", ".jpeg", ".gif", ".webp")
paths = []
for dp, _, fs in os.walk("docs"):
    if os.sep + "_out" in dp + os.sep:
        continue
    paths += [os.path.join(dp, f) for f in fs if f.endswith(exts)]
paths += [os.path.join("ApcOptimizer", f)
          for f in os.listdir("ApcOptimizer") if f.endswith(".lean")]
for p in sorted(paths):
    try:
        with open(p, "rb") as fh:
            h.update(p.encode()); h.update(fh.read())
    except OSError:
        pass
print(h.hexdigest())
PY
}

# Add a tiny live-reload poller to the generated page (watch mode only): it polls
# reload.txt and reloads when the token changes. Re-run after every rebuild, since
# index.html is regenerated each time.
inject_reload() {
  cat > "$HTML/__reload.js" <<'JS'
(async () => {
  let v = null;
  for (;;) {
    try {
      const r = await fetch("reload.txt", { cache: "no-store" });
      // Only a 200 is a real token. Mid-rebuild the file is briefly missing;
      // fetch does NOT throw on 404, so we must ignore non-OK responses rather
      // than mistake the error body for a changed token and reload too early.
      if (r.ok) {
        const t = await r.text();
        if (v !== null && t !== v) { location.reload(); return; }
        v = t;
      }
    } catch (_) { /* network hiccup; keep polling */ }
    await new Promise((r) => setTimeout(r, 1000));
  }
})();
JS
  # Inject the poller first; write the token LAST, so the token only changes once
  # the fully regenerated page is in place.
  perl -0pi -e 's{</body>}{  <script src="__reload.js"></script>\n</body>}' "$HTML/index.html"
  python3 -c 'import time; print(time.time_ns())' > "$HTML/reload.txt"
}

if [ "${1:-}" = "--pdf" ]; then
  build_pdf
  exit 0
fi

build_once
echo "Wrote $HTML/index.html"

case "${1:-}" in
  --serve)
    PORT=$(pick_port)
    echo "Serving on http://127.0.0.1:$PORT (Ctrl-C to stop)"
    exec python3 -m http.server "$PORT" --bind 127.0.0.1 --directory "$HTML"
    ;;
  --watch)
    inject_reload
    PORT=$(pick_port)
    python3 -m http.server "$PORT" --bind 127.0.0.1 --directory "$HTML" >/dev/null 2>&1 &
    srv=$!
    trap 'kill "$srv" 2>/dev/null' EXIT INT TERM
    echo "Serving on http://127.0.0.1:$PORT — watching for changes (Ctrl-C to stop)"
    last=$(watch_sig)
    while sleep 1; do
      cur=$(watch_sig)
      [ "$cur" = "$last" ] && continue
      echo "$(date +%H:%M:%S) change detected — rebuilding…"
      if build_once; then
        inject_reload
        echo "$(date +%H:%M:%S) reloaded."
      else
        echo "$(date +%H:%M:%S) build failed — fix the error and save again."
      fi
      last=$(watch_sig)
    done
    ;;
esac
