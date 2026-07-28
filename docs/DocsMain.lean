import VersoManual
import Docs

open Verso.Genre Manual

open Verso.Output.Html in
def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .immediately
  emitHtmlMulti := .no
  extraHead := #[{{
    <link rel="stylesheet" href="theme.css"/>
  }}]

def main (args : List String) : IO UInt32 :=
  manualMain (%doc Docs) (options := args) (config := config)
