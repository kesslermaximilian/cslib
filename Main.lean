import VersoSlides
import Slides

open VersoSlides

def theoremsCss : CssFile where
  filename := "theorems.css"
  contents := ⟨include_str "theorems.css"⟩

def main : IO UInt32 :=
  slidesMain
    (config := { theme := "black", slideNumber := true, transition := "slide", width := 1300, extraCss := #[theoremsCss] })
    (doc := %doc Slides)
