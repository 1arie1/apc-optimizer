# Docs: the audited-surface site

A [Verso](https://github.com/leanprover/verso) document that renders the audited surface of
`apc-optimizer` as a single-page, cross-linked site, splicing the real definitions and theorem
statements live from the compiled source. Published at
<https://powdr-labs.github.io/apc-optimizer/>.

`docs/build.sh --pdf` builds a PDF (`docs/_out/tex/apc_optimizer.pdf`) from Verso's TeX output
instead of the site; it needs `xelatex` and `latexmk` (plus `rsvg-convert` for the figures), and
stops after writing `main.tex` if they are missing.

Build and serve locally with `docs/build.sh --serve` (or `--watch` to rebuild and live-reload on
save); it serves at <http://127.0.0.1:8017>. Serving over HTTP is required — opening `index.html`
as a `file://` URL breaks the hover tooltips and search, which fetch JSON at runtime.
