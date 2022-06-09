import LeanMarkup.Html.Macros

open scoped LeanMarkup.Html

def html := <A/>

def main : IO Unit :=
  IO.println s!"Hello {html} markup!"
