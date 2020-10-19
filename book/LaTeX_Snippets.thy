theory LaTeX_Snippets
  imports
    "../Logic/Intuitionistic/Implication_Logic"
    "HOL-Library.LaTeXsugar"
begin

text (in implication_logic) \<open>
 \DefineSnippet{Axiom K}{
   @{thm [display] implication_logic.axiom_k}
 }%EndSnippet
 \DefineSnippet{Axiom S}{
   @{thm [display] implication_logic.axiom_s}
 }%EndSnippet
 \DefineSnippet{Modus Ponens}{
   @{thm [mode=Rule] implication_logic.modus_ponens} {\sc MP}
 }%EndSnippet
\<close>

end
