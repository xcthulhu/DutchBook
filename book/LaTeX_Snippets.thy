theory LaTeX_Snippets
  imports
    "../Logic/Intuitionistic/Implicational/Implicational_Intuitionistic_Logic"
    "~~/src/HOL/Library/LaTeXsugar"
begin

text (in Minimal_Logic) \<open>
 \DefineSnippet{Axiom K}{
   @{thm [display] Minimal_Logic.Axiom_1}
 }%EndSnippet
 \DefineSnippet{Axiom S}{
   @{thm [display] Minimal_Logic.Axiom_2}
 }%EndSnippet
 \DefineSnippet{Modus Ponens}{
   @{thm [mode=Rule] Minimal_Logic.Modus_Ponens} {\sc MP}
 }%EndSnippet
\<close>

end
