import VersoManual
import Docs.Bibliography

open Lean (ToJson FromJson)
open Verso Doc Elab Genre Manual
open Verso.Genre.Manual Verso.Genre.Manual.Bibliography
open Verso.ArgParse

namespace Docs

-- Numbered citation. Renders a superscript reference number inline (via the margin-note counter)
-- and drops the full reference into the margin — no inline author or year. Because the only margin
-- notes in this document are citations, the numbers run sequentially in document order.
inline_extension Inline.citeNum (citations : List Citable) where
  data := ToJson.toJson citations
  traverse _ _ _ := pure none
  extraCss := [Marginalia.css]
  toHtml :=
    open Verso.Output.Html in
    some <| fun go _ data _content => do
      match FromJson.fromJson? data with
      | .error _ => pure .empty
      | .ok (cs : List Citable) => do
        let notes ← cs.toArray.mapM (fun c => return Marginalia.html (← Citable.bibHtml go c))
        pure (notes.foldl (· ++ ·) .empty)
  toTeX :=
    open Verso.Output.TeX in
    some <| fun go _ data _content => do
      match FromJson.fromJson? data with
      | .error _ => pure .empty
      | .ok (cs : List Citable) => do
        let notes ← cs.toArray.mapM (fun c => return Marginalia.TeX (← Citable.bibTeX go c))
        pure (notes.foldl (· ++ ·) .empty)

/-- `{citeNum foo bar}` — cite one or more references as numbered margin notes. -/
@[role]
def citeNum : RoleExpanderOf CiteConfig
  | config, _ => do
    let xs := config.citations.map Lean.mkIdent |>.toArray
    ``(Doc.Inline.other (Inline.citeNum ([$xs,*] : List Citable)) #[])

end Docs
