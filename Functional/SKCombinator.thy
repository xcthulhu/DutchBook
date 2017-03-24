theory SKCombinator
  imports "../Logic/Formula"
begin

subsection \<open>Definitions\<close>

text \<open>Below the definition for the type {@typ "'x SKCombinator} is provided.\<close>
  
datatype 'x SKCombinator =
    Variable 'x                                ("\<langle>_\<rangle>" [100] 100)
  | S
  | K
  | Apply "'x SKCombinator" "'x SKCombinator"  (infixl "\<cdot>" 75)
 
text \<open>The fragment of the {@typ 'x SKCombinator} types without {@term Variable} terms
      can naturally be given \emph{simple types}.\<close>

inductive Simply_Typed_SKCombinator :: "'x SKCombinator \<Rightarrow> 'a Formula \<Rightarrow> bool" (infix "\<Colon>" 65)
where
    S_type      : "S \<Colon> (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<chi>"
  | K_type      : "K \<Colon> \<phi> \<rightarrow> \<psi> \<rightarrow> \<phi>"
  | application : "E\<^sub>1 \<Colon> \<phi> \<rightarrow> \<psi> \<Longrightarrow> E\<^sub>2 \<Colon> \<phi> \<Longrightarrow> E\<^sub>1 \<cdot> E\<^sub>2 \<Colon> \<psi>"

subsection \<open>Free Variables and Pure Combinators\<close>

text \<open>The free variables in a {@typ "'x SKCombinator"} are those which occur in a 
      {@term Variable} subexpression.\<close>
    
fun free_variables_in_SKCombinator :: "'x SKCombinator \<Rightarrow> 'x set" ("free\<^sub>S\<^sub>K")
  where
    "free\<^sub>S\<^sub>K (\<langle>x\<rangle>) = {x}"
  | "free\<^sub>S\<^sub>K S = {}"
  | "free\<^sub>S\<^sub>K K = {}"
  | "free\<^sub>S\<^sub>K (E\<^sub>1 \<cdot> E\<^sub>2) = (free\<^sub>S\<^sub>K E\<^sub>1) \<union> (free\<^sub>S\<^sub>K E\<^sub>2)"

text \<open>The \emph{pure} combinators are the common fragment of all
      {@typ "'x SKCombinator"} types, and are precisely those combinators with no free variables.\<close>    
    
inductive_set pure_SKCombinators :: "'x SKCombinator set" ("pure\<^sub>S\<^sub>K") where
    K_pure[intro!]: "K \<in> pure\<^sub>S\<^sub>K"
  | S_pure[intro!]: "S \<in> pure\<^sub>S\<^sub>K"
  | Application_pure[intro!]: "E\<^sub>1 \<in> pure\<^sub>S\<^sub>K \<Longrightarrow> E\<^sub>2 \<in> pure\<^sub>S\<^sub>K \<Longrightarrow> E\<^sub>1 \<cdot> E\<^sub>2 \<in> pure\<^sub>S\<^sub>K"

lemma pure_is_bounded: "X \<in> pure\<^sub>S\<^sub>K \<Longrightarrow> free\<^sub>S\<^sub>K X = {}"
proof (induct rule: pure_SKCombinators.induct)
  case K_pure thus ?case by simp
  next case S_pure thus ?case by simp
  next case Application_pure thus ?case by simp
qed
    
lemma bounded_is_pure: "free\<^sub>S\<^sub>K X = {} \<Longrightarrow> X \<in> pure\<^sub>S\<^sub>K"
proof (induct X)
  case Variable show ?case using Variable.prems by auto
  next case S show ?case by blast
  next case K show ?case by blast
  next case Apply show ?case
      using Apply.hyps(1) Apply.hyps(2) Apply.prems by auto
qed

lemma pure_equivalence: "X \<in> pure\<^sub>S\<^sub>K \<equiv> free\<^sub>S\<^sub>K X = {}"
  by (smt bounded_is_pure pure_is_bounded)

text \<open>Every typed combinator is \emph{pure}, and every \emph{pure} combinator has a typing.\<close>

lemma typed_combinators_are_pure : "X \<Colon> \<phi> \<Longrightarrow> X \<in> pure\<^sub>S\<^sub>K"
  proof (induct rule: Simply_Typed_SKCombinator.induct)
    case S_type then show ?case by (simp add: pure_SKCombinators.S_pure) 
    next case K_type then show ?case by (simp add: pure_SKCombinators.K_pure) 
    next case application then show ?case by blast 
qed

lemma hidden_application_type: "X \<cdot> Y \<Colon> \<phi> \<Longrightarrow> \<exists> \<psi>. X \<Colon> \<psi> \<rightarrow> \<phi>"
  using Simply_Typed_SKCombinator.simps by fastforce
    
text \<open>Here \emph{bracket abstraction} is presented, which is a kind of embedding of the \<lambda>-calculus 
      into combinator logic.\<close>

text \<open>See Turner, David A. "Another Algorithm for Bracket Abstraction". 
      The Journal of Symbolic Logic. 44: 267–270. doi:10.2307/2273733\<close>

text \<open>To avoid exponential blowup, abstraction over combinators where the abstracted variable
      is not free is simplified using the {@term K} combinator.\<close>
    
    
fun turner_abstraction :: "'x \<Rightarrow> 'x SKCombinator  \<Rightarrow> 'x SKCombinator" ("\<^bold>\<lambda> _. _" [90,90] 90) 
  where
    "\<^bold>\<lambda> x. (E\<^sub>1 \<cdot> E\<^sub>2) = (if (x \<in> free\<^sub>S\<^sub>K (E\<^sub>1 \<cdot> E\<^sub>2)) then S \<cdot> (\<^bold>\<lambda> x. E\<^sub>1) \<cdot> (\<^bold>\<lambda> x. E\<^sub>2) else K \<cdot> (E\<^sub>1 \<cdot> E\<^sub>2))"
  | "\<^bold>\<lambda> x. X = (if (X = \<langle>x\<rangle>) then S \<cdot> K \<cdot> K else K \<cdot> X)"

datatype NamedVariable = 
    XVariable  ("\<^bold>x")
  | YVariable  ("\<^bold>y")
  | ZVariable  ("\<^bold>z")
  | FVariable  ("\<^bold>f")
  | GVariable  ("\<^bold>g")

lemma Identity_type: "S \<cdot> K \<cdot> K \<Colon> \<phi> \<rightarrow> \<phi>"
  using K_type S_type application by blast 
   
lemma "\<^bold>\<lambda> \<^bold>f. \<^bold>\<lambda> \<^bold>x. \<langle>\<^bold>f\<rangle> \<Colon> \<phi> \<rightarrow> \<psi> \<rightarrow> \<phi>"
  apply (simp)
  by (meson Simply_Typed_SKCombinator.simps)

lemma "\<^bold>\<lambda> \<^bold>f. \<^bold>\<lambda> \<^bold>x. \<^bold>\<lambda> \<^bold>y. (\<langle>\<^bold>f\<rangle> \<cdot> \<langle>\<^bold>y\<rangle> \<cdot> \<langle>\<^bold>x\<rangle>) \<Colon> (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> \<psi> \<rightarrow> \<phi> \<rightarrow> \<chi>"
  apply (simp)
  by (meson Identity_type Simply_Typed_SKCombinator.simps)

end