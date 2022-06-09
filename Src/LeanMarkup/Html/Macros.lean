-- NOTE: This file is basically a copy of DocGen4/Output/ToHtmlFormat.lean
--        It is going to be used as a starting point

import Lean.Parser

namespace LeanMarkup.Html

declare_syntax_cat markupElement
declare_syntax_cat markupChild

open Lean
open Parser PrettyPrinter

inductive Html where
  | element : String → Bool → Array (String × String) → Array Html → Html
  | text : String → Html
  deriving Repr, BEq, Inhabited

-- To String
def attributesToString (attrs : Array (String × String)) :String :=
  attrs.foldl (λ acc (k, v) => acc ++ " " ++ k ++ "=\"" ++ v ++ "\"") ""

-- TODO: Termination proof
partial def Html.toStringAux : Html → String
| element tag false attrs #[text s] => s!"<{tag}{attributesToString attrs}>{s}</{tag}>\n"
| element tag false attrs #[child] => s!"<{tag}{attributesToString attrs}>\n{child.toStringAux}</{tag}>\n"
| element tag false attrs children => s!"<{tag}{attributesToString attrs}>\n{children.foldl (· ++ toStringAux ·) ""}</{tag}>\n"
| element tag true attrs children => s!"<{tag}{attributesToString attrs}>{children.foldl (· ++ toStringAux ·) ""}</{tag}>"
| text s => s

def Html.toString (html : Html) : String :=
  html.toStringAux.trimRight

instance : ToString Html :=
  ⟨Html.toString⟩
---

instance : Coe String Html := ⟨Html.text⟩

-- TextCharacter : SourceCharacter but not one of {, <, > or }
def markupText : Parser :=
  withAntiquot (mkAntiquot "markupText" `markupText) {
    fn := fun c s =>
      let startPos := s.pos
      let s := takeWhile1Fn (not ∘ "[{<>}]$".contains) "expected markup text" c s
      mkNodeToken `markupText startPos c s }

@[combinatorFormatter LeanMarkup.Html.markupText]
def markupText.formatter : Formatter := pure ()

@[combinatorParenthesizer LeanMarkup.Html.markupText]
def markupText.parenthesizer : Parenthesizer := pure ()

syntax markupAttrName   := rawIdent <|> str
syntax markupAttrVal    := str <|> group("{" term "}")
syntax markupSimpleAttr := markupAttrName "=" markupAttrVal
syntax markupAttrSpread := "[" term "]"
syntax markupAttr       := markupSimpleAttr <|> markupAttrSpread

syntax "<" rawIdent markupAttr* "/>" : markupElement
syntax "<" rawIdent markupAttr* ">" markupChild* "</" rawIdent ">" : markupElement

syntax markupText    : markupChild
syntax "{" term "}"  : markupChild
syntax "[" term "]"  : markupChild
syntax markupElement : markupChild

scoped syntax:max markupElement : term


def translateAttrs (attrs : Array Syntax) : MacroM Syntax := do
  let mut as ← `(#[])
  for attr in attrs do
    as ← match attr with
    | `(markupAttr| $name:markupAttrName = $value:markupAttrVal) =>
      let name ← match name with
        | `(markupAttrName| $name:str) => pure name
        | `(markupAttrName| $name:ident) => pure $ quote (toString name.getId)
        | _ => Macro.throwUnsupported
      let value ← match value with
        | `(markupAttrVal| {$value}) => pure value
        | `(markupAttrVal| $value:str) => pure value
        | _ => Macro.throwUnsupported
      `(($as).push ($name, ($value : String)))
    | `(markupAttr| [$t]) => `($as ++ ($t : Array (String × String)))
    | _ => Macro.throwUnsupported
  return as


macro_rules
  | `(<$tag $attrs* />) => do
    `(Html.element $(quote (toString tag.getId)) true $(← translateAttrs attrs) #[])
  | `(<$tagOpen $attrs* >$children*</$tagClose>) => do
    unless tagOpen.getId == tagClose.getId do
      withRef tagClose <| Macro.throwError s!"expected </{tagOpen.getId}>"
    let mut cs ← `(#[])
    for child in children do
      cs ← match child with
      | `(markupChild| $t:markupText)    => `(($cs).push (Html.text $(quote t[0].getAtomVal!)))
      -- TODO(WN): elab as list of children if type is `t Html` where `Foldable t`
      | `(markupChild| {$t})             => `(($cs).push ($t : Html))
      | `(markupChild| [$t])             => `($cs ++ ($t : Array Html))
      | `(markupChild| $e:markupElement) => `(($cs).push ($e:markupElement : Html))
      | _                                => Macro.throwUnsupported
    `(Html.element $(quote tagOpen.getId.toString) false $(← translateAttrs attrs) $cs)

end LeanMarkup.Html