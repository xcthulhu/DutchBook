subsection \<open>Combinator Logic\<close>

theory Combinator
  imports Main
begin

subsection \<open>Definition\<close>

text \<open>Below the definition for the type {@typ "'x SKCombinator} is provided.\<close>
  
datatype 'x SKCombinator =
    Variable_Combinator 'x                                 ("\<^bold>\<langle>_\<^bold>\<rangle>" [100] 100)
  | S_Combinator                                           ("\<^bold>S")
  | K_Combinator                                           ("\<^bold>K")
  | Apply_Combinators "'x SKCombinator" "'x SKCombinator"  (infixl "\<^bold>\<cdot>" 75)

subsection \<open>Typing\<close>
  
text \<open>The fragment of the {@typ 'x SKCombinator} types without {@term Variable} terms
      can be given \emph{simple types}:\<close>

datatype 'a Combinator_Simple_Type = 
    Arrow "'a Combinator_Simple_Type" "'a Combinator_Simple_Type"   (infixr "\<^bold>\<Rightarrow>" 70)
  | Atom 'a    
  
inductive Simply_Typed_SKCombinator :: "'x SKCombinator \<Rightarrow> 'a Combinator_Simple_Type \<Rightarrow> bool" (infix "\<^bold>\<Colon>" 65)
where
    S_type           : "\<^bold>S \<^bold>\<Colon> (\<phi> \<^bold>\<Rightarrow> \<psi> \<^bold>\<Rightarrow> \<chi>) \<^bold>\<Rightarrow> (\<phi> \<^bold>\<Rightarrow> \<psi>) \<^bold>\<Rightarrow> \<phi> \<^bold>\<Rightarrow> \<chi>"
  | K_type           : "\<^bold>K \<^bold>\<Colon> \<phi> \<^bold>\<Rightarrow> \<psi> \<^bold>\<Rightarrow> \<phi>"
  | Application_type : "E\<^sub>1 \<^bold>\<Colon> \<phi> \<^bold>\<Rightarrow> \<psi> \<Longrightarrow> E\<^sub>2 \<^bold>\<Colon> \<phi> \<Longrightarrow> E\<^sub>1 \<^bold>\<cdot> E\<^sub>2 \<^bold>\<Colon> \<psi>"

subsection \<open>\<lambda>-Abstraction\<close>
    
text \<open>Here a simple embedding of the \<lambda>-calculus into combinator logic is presented.\<close>

text \<open>
TODO: Use bibtex

The embedding follows David Turner's "Another Algorithm for Bracket Abstraction". 
      The Journal of Symbolic Logic. 44: 267–270. doi:10.2307/2273733\<close>

text \<open>To avoid exponential blowup, abstraction over combinators where the abstracted variable
      is not free is simplified using the $\mathbf{K}$ combinator.\<close>

primrec free_variables_in_SKCombinator :: "'x SKCombinator \<Rightarrow> 'x set" ("free\<^sub>S\<^sub>K")
  where
    "free\<^sub>S\<^sub>K (\<^bold>\<langle>x\<^bold>\<rangle>) = {x}"
  | "free\<^sub>S\<^sub>K \<^bold>S = {}"
  | "free\<^sub>S\<^sub>K \<^bold>K = {}"
  | "free\<^sub>S\<^sub>K (E\<^sub>1 \<^bold>\<cdot> E\<^sub>2) = (free\<^sub>S\<^sub>K E\<^sub>1) \<union> (free\<^sub>S\<^sub>K E\<^sub>2)"
  
fun Turner_Abstraction :: "'x \<Rightarrow> 'x SKCombinator \<Rightarrow> 'x SKCombinator" ("\<^bold>\<lambda> _. _" [90,90] 90) 
  where
    "\<^bold>\<lambda> x. (E\<^sub>1 \<^bold>\<cdot> E\<^sub>2) = (if (x \<in> free\<^sub>S\<^sub>K (E\<^sub>1 \<^bold>\<cdot> E\<^sub>2)) then \<^bold>S \<^bold>\<cdot> (\<^bold>\<lambda> x. E\<^sub>1) \<^bold>\<cdot> (\<^bold>\<lambda> x. E\<^sub>2) else \<^bold>K \<^bold>\<cdot> (E\<^sub>1 \<^bold>\<cdot> E\<^sub>2))"
  | "\<^bold>\<lambda> x. X = (if (X = \<^bold>\<langle>x\<^bold>\<rangle>) then \<^bold>S \<^bold>\<cdot> \<^bold>K \<^bold>\<cdot> \<^bold>K else \<^bold>K \<^bold>\<cdot> X)"

subsection \<open>Common Combinators\<close>

text \<open>Using \<lambda>-abstraction, various common combinators can be expressed.  
      TODO: Cite Haskell Curry's PhD thesis.\<close>  

text \<open>Automated deduction machinary for \<lambda>-abstraction functions more efficiently when making
      use of the following convenience type:\<close>
  
datatype Named_Variable =
    XVariable  ("\<^bold>x")
  | YVariable  ("\<^bold>y")
  | FVariable  ("\<^bold>f")

text \<open>A useful lemma is the type of the \emph{identity} combinator, designated by $\mathbf{I}$
      in the literature.\<close>     
    
lemma Identity_type: "\<^bold>S \<^bold>\<cdot> \<^bold>K \<^bold>\<cdot> \<^bold>K \<^bold>\<Colon> \<phi> \<^bold>\<Rightarrow> \<phi>"
  using K_type S_type Application_type by blast 

text \<open>Another significant combinator is the $\mathbf{C}$ combinator, which is referred to as
      \texttt{flip} in Haskell.\<close>    

lemma C_type: "\<^bold>\<lambda> \<^bold>f. \<^bold>\<lambda> \<^bold>x. \<^bold>\<lambda> \<^bold>y. (\<^bold>\<langle>\<^bold>f\<^bold>\<rangle> \<^bold>\<cdot> \<^bold>\<langle>\<^bold>y\<^bold>\<rangle> \<^bold>\<cdot> \<^bold>\<langle>\<^bold>x\<^bold>\<rangle>) \<^bold>\<Colon> (\<phi> \<^bold>\<Rightarrow> \<psi> \<^bold>\<Rightarrow> \<chi>) \<^bold>\<Rightarrow> \<psi> \<^bold>\<Rightarrow> \<phi> \<^bold>\<Rightarrow> \<chi>"
  by (simp, meson Identity_type Simply_Typed_SKCombinator.simps)

text \<open>The final combinator given is the $\mathbf{W}$ combinator.\<close>    

lemma W_type: "\<^bold>\<lambda> \<^bold>f. \<^bold>\<lambda> \<^bold>x. (\<^bold>\<langle>\<^bold>f\<^bold>\<rangle> \<^bold>\<cdot> \<^bold>\<langle>\<^bold>x\<^bold>\<rangle> \<^bold>\<cdot> \<^bold>\<langle>\<^bold>x\<^bold>\<rangle>) \<^bold>\<Colon> (\<phi> \<^bold>\<Rightarrow> \<phi> \<^bold>\<Rightarrow> \<chi>) \<^bold>\<Rightarrow> \<phi> \<^bold>\<Rightarrow> \<chi>"
  by (simp, meson Identity_type Simply_Typed_SKCombinator.simps)
  
end
