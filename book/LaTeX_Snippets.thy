theory LaTeX_Snippets
  imports
    "../Logic/Intuitionistic/Implicational/Implicational_Intuitionistic_Logic"
    "~~/src/HOL/Library/LaTeXsugar"
begin

text (in Implicational_Intuitionistic_Logic) \<open>
 \DefineSnippet{Axiom K}{
   @{thm [display] Implicational_Intuitionistic_Logic.Axiom_K}
 }%EndSnippet
 \DefineSnippet{Axiom S}{
   @{thm [display] Implicational_Intuitionistic_Logic.Axiom_S}
 }%EndSnippet
 \DefineSnippet{Modus Ponens}{
   @{thm [mode=Rule] Implicational_Intuitionistic_Logic.Modus_Ponens} {\sc MP}
 }%EndSnippet
\<close>

end
