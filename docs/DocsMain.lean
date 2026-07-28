import VersoManual
import Docs

open Verso.Genre Manual

open Verso.Output.Html in
def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .immediately
  emitHtmlMulti := .no
  -- Widen the content column so 80-column code blocks fit without horizontal scroll (Verso's
  -- default `--verso-content-max-width` is 47rem). Overridden here rather than in `book.css`,
  -- which is regenerated from the Verso package on every build.
  extraHead := #[{{
    <style>":root { --verso-content-max-width: 56rem !important; }"</style>
  }}]

def main (args : List String) : IO UInt32 :=
  manualMain (%doc Docs) (options := args) (config := config)
