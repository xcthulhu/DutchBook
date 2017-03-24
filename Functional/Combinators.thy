subsection \<open>Combinator Logic\<close>

theory Combinators
  imports "../Logic/Formula"
begin

subsection \<open>Definition\<close>

text \<open>Below the definition for the type {@typ "'x SKCombinator} is provided.\<close>
  
datatype 'x SKCombinator =
    Variable_Combinator 'x                                 ("\<^bold>\<langle>_\<^bold>\<rangle>" [100] 100)
  | S_Combinator                                           ("\<^bold>S")
  | K_Combinator                                           ("\<^bold>K")
  | Apply_Combinators "'x SKCombinator" "'x SKCombinator"  (infixl "\<cdot>" 75)

subsection \<open>Typing\<close>    

text \<open>The fragment of the {@typ 'x SKCombinator} types without {@term Variable} terms
      can be given \emph{simple types}:\<close>

inductive Simply_Typed_SKCombinator :: "'x SKCombinator \<Rightarrow> 'a Formula \<Rightarrow> bool" (infix "\<Colon>" 65)
where
    S_type           : "\<^bold>S \<Colon> (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<chi>"
  | K_type           : "\<^bold>K \<Colon> \<phi> \<rightarrow> \<psi> \<rightarrow> \<phi>"
  | Application_type : "E\<^sub>1 \<Colon> \<phi> \<rightarrow> \<psi> \<Longrightarrow> E\<^sub>2 \<Colon> \<phi> \<Longrightarrow> E\<^sub>1 \<cdot> E\<^sub>2 \<Colon> \<psi>"

subsection \<open>\<lambda>-Abstraction\<close>
    
text \<open>Here a simple embedding of the \<lambda>-calculus into combinator logic is presented.\<close>

text \<open>
TODO: Use bibtex

The embedding follows David Turner's "Another Algorithm for Bracket Abstraction". 
      The Journal of Symbolic Logic. 44: 267–270. doi:10.2307/2273733\<close>

text \<open>To avoid exponential blowup, abstraction over combinators where the abstracted variable
      is not free is simplified using the $\mathbf{K}$ combinator.\<close>

fun free_variables_in_SKCombinator :: "'x SKCombinator \<Rightarrow> 'x set" ("free\<^sub>S\<^sub>K")
  where
    "free\<^sub>S\<^sub>K (\<^bold>\<langle>x\<^bold>\<rangle>) = {x}"
  | "free\<^sub>S\<^sub>K \<^bold>S = {}"
  | "free\<^sub>S\<^sub>K \<^bold>K = {}"
  | "free\<^sub>S\<^sub>K (E\<^sub>1 \<cdot> E\<^sub>2) = (free\<^sub>S\<^sub>K E\<^sub>1) \<union> (free\<^sub>S\<^sub>K E\<^sub>2)"
  
fun Turner_abstraction :: "'x \<Rightarrow> 'x SKCombinator  \<Rightarrow> 'x SKCombinator" ("\<^bold>\<lambda> _. _" [90,90] 90) 
  where
    "\<^bold>\<lambda> x. (E\<^sub>1 \<cdot> E\<^sub>2) = (if (x \<in> free\<^sub>S\<^sub>K (E\<^sub>1 \<cdot> E\<^sub>2)) then \<^bold>S \<cdot> (\<^bold>\<lambda> x. E\<^sub>1) \<cdot> (\<^bold>\<lambda> x. E\<^sub>2) else \<^bold>K \<cdot> (E\<^sub>1 \<cdot> E\<^sub>2))"
  | "\<^bold>\<lambda> x. X = (if (X = \<^bold>\<langle>x\<^bold>\<rangle>) then \<^bold>S \<cdot> \<^bold>K \<cdot> \<^bold>K else \<^bold>K \<cdot> X)"

subsection \<open>Common Combinators\<close>

text \<open>Using \<lambda>-abstraction, various common combinators can be expressed.  
      TODO: Cite Haskell Curry's PhD thesis.\<close>  

text \<open>Automated deduction machinary for \<lambda>-abstraction functions more efficiently when making
      use of the following convenience type:\<close>
  
datatype NamedVariable = 
    XVariable  ("\<^bold>x")
  | YVariable  ("\<^bold>y")
  | ZVariable  ("\<^bold>z")
  | FVariable  ("\<^bold>f")
  | GVariable  ("\<^bold>g")

text \<open>A useful lemma is the type of the \emph{identity} combinator, designated by $\mathbf{I}$
      in the literature.\<close>     
    
lemma Identity_type: "\<^bold>S \<cdot> \<^bold>K \<cdot> \<^bold>K \<Colon> \<phi> \<rightarrow> \<phi>"
  using K_type S_type Application_type by blast 

text \<open>Another significant combinator is the $\mathbf{C}$ combinator, which is referred to as
      \texttt{flip} in Haskell.\<close>    

lemma C_type: "\<^bold>\<lambda> \<^bold>f. \<^bold>\<lambda> \<^bold>x. \<^bold>\<lambda> \<^bold>y. (\<^bold>\<langle>\<^bold>f\<^bold>\<rangle> \<cdot> \<^bold>\<langle>\<^bold>y\<^bold>\<rangle> \<cdot> \<^bold>\<langle>\<^bold>x\<^bold>\<rangle>) \<Colon> (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> \<psi> \<rightarrow> \<phi> \<rightarrow> \<chi>"
  apply (simp)
  by (meson Identity_type Simply_Typed_SKCombinator.simps)

text \<open>The final combinator given is the $\mathbf{W}$ combinator.\<close>    

lemma W_type: "\<^bold>\<lambda> \<^bold>f. \<^bold>\<lambda> \<^bold>x. (\<^bold>\<langle>\<^bold>f\<^bold>\<rangle> \<cdot> \<^bold>\<langle>\<^bold>x\<^bold>\<rangle> \<cdot> \<^bold>\<langle>\<^bold>x\<^bold>\<rangle>) \<Colon> (\<phi> \<rightarrow> \<phi> \<rightarrow> \<chi>) \<rightarrow> \<phi> \<rightarrow> \<chi>"
  apply (simp)
  by (meson Identity_type Simply_Typed_SKCombinator.simps)
  
end