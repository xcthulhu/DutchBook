theory LaTeX_Snippets
  imports
    "../Logic/Intuitionistic/Implication_Logic"
    "HOL-Library.LaTeXsugar"
begin

text (in Implication_Logic) \<open>
 \DefineSnippet{Axiom K}{
   @{thm [display] Implication_Logic.Axiom_K}
 }%EndSnippet
 \DefineSnippet{Axiom S}{
   @{thm [display] Implication_Logic.Axiom_S}
 }%EndSnippet
 \DefineSnippet{Modus Ponens}{
   @{thm [mode=Rule] Implication_Logic.Modus_Ponens} {\sc MP}
 }%EndSnippet
\<close>

end
