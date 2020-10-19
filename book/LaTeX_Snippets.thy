theory LaTeX_Snippets
  imports
    "../Logic/Intuitionistic/implication_logic"
    "HOL-Library.LaTeXsugar"
begin

text (in implication_logic) \<open>
 \DefineSnippet{Axiom K}{
   @{thm [display] implication_logic.axiom_k}
 }%EndSnippet
 \DefineSnippet{Axiom S}{
   @{thm [display] implication_logic.Axiom_S}
 }%EndSnippet
 \DefineSnippet{Modus Ponens}{
   @{thm [mode=Rule] implication_logic.Modus_Ponens} {\sc MP}
 }%EndSnippet
\<close>

end
