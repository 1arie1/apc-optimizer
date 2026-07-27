import VersoManual
import Docs.Bibliography

open Lean (ToJson FromJson)
open Verso Doc Elab Genre Manual
open Verso.Genre.Manual Verso.Genre.Manual.Bibliography
open Verso.ArgParse
open Verso.Output Verso.Doc.Html

namespace Docs

open Verso.Output.Html in
/-- Join rendered authors as "A", "A and B", or "A, B and C". -/
private def joinAndHtml (xs : Array Html) : Html := Id.run do
  if xs.isEmpty then return .empty
  let mut out := xs[0]!
  for i in [1:xs.size] do
    out := out ++ (if i + 1 == xs.size then {{" and "}} else {{", "}}) ++ xs[i]!
  return out

open Verso.Output.Html in
/-- Clean reference HTML: like Verso's `Citable.bibHtml`, but omits empty `volume`/`number`, so
    blog/eprint entries (no volume/number/pages) don't render a dangling ". ". Non-`Article` refs
    fall back to `bibHtml`. -/
def refHtml {m : Type → Type} [Monad m]
    (go : Doc.Inline Manual → HtmlT Manual m Html) : Citable → HtmlT Manual m Html
  | .article p => do
      let auth := joinAndHtml (← p.authors.mapM go)
      let ym : Html ← match p.month with
        | some mo => do let mh ← go mo; pure {{ {{mh}} " " s!"{p.year}" }}
        | .none => pure {{ s!"{p.year}" }}
      let titleH ← go p.title
      let titleLinked : Html := match p.url with
        | some u => {{ <a href={{u}}> "“" {{titleH}} "”" </a> }}
        | .none => {{ "“" {{titleH}} "”" }}
      let journalH ← go p.journal
      let tail : Html ← match p.pages with
        | some (x, y) => do
            let vh ← go p.volume
            let nh ← go p.number
            pure {{ ", " <strong>{{vh}}</strong> "(" {{nh}} "), pp. " s!"{x}–{y}" "." }}
        | .none => pure {{ "." }}
      pure {{ <span class="citation"> {{auth}} " (" {{ym}} "). " {{titleLinked}} ". " <em>{{journalH}}</em> {{tail}} </span> }}
  | c => Citable.bibHtml go c

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
        let notes ← cs.toArray.mapM (fun c => return Marginalia.html (← refHtml go c))
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
