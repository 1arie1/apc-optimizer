#!/usr/bin/env bash
# Build the audited-surface docs site and emit a self-contained single-page HTML site.
# Usage:
#   docs/build.sh            build once
#   docs/build.sh --serve    build once, then serve
#   docs/build.sh --watch    build + serve, then rebuild and live-reload on source changes
# Override the start port with PORT=NNNN.
set -euo pipefail
cd "$(dirname "$0")/.."             # repo root

OUT=docs/_out
HTML="$OUT/html-single"

build_once() {
  # Render the trust-map figure from its Graphviz source (skips if `dot` is absent).
  if command -v dot >/dev/null 2>&1; then
    dot -Tsvg docs/assets/trust.dot -o docs/assets/trust.svg
  fi
  lake build docs
  rm -rf "$OUT"
  lake exe docs --output "$OUT"
  # Ship image assets alongside the page (Verso references them relatively).
  find docs/assets -type f \( -name '*.svg' -o -name '*.png' -o -name '*.jpg' \
    -o -name '*.jpeg' -o -name '*.gif' -o -name '*.webp' \) -exec cp {} "$HTML/" \;
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

# md5 over the mtimes of the sources a rebuild depends on: the doc sources, plus the
# audited files (directly under ApcOptimizer/) whose docstrings the page splices.
watch_sig() {
  python3 - <<'PY'
import os, hashlib
h = hashlib.md5()
paths = []
for dp, _, fs in os.walk("docs"):
    if os.sep + "_out" in dp + os.sep:
        continue
    paths += [os.path.join(dp, f) for f in fs if f.endswith((".lean", ".dot"))]
paths += [os.path.join("ApcOptimizer", f)
          for f in os.listdir("ApcOptimizer") if f.endswith(".lean")]
for p in sorted(paths):
    try:
        h.update(p.encode()); h.update(str(os.path.getmtime(p)).encode())
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
