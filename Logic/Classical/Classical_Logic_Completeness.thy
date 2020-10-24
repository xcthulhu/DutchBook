(*:maxLineLen=78:*)

section \<open> Classical Soundness and Completeness \label{sec:classical-propositional-calculus} \<close>

theory Classical_Logic_Completeness
  imports Classical_Logic
begin

sledgehammer_params [smt_proofs = false]

subsection \<open> Syntax \<close>

datatype 'a classical_propositional_formula =
      Falsum ("\<^bold>\<bottom>")
    | Proposition 'a ("\<^bold>\<langle> _ \<^bold>\<rangle>" [45])
    | Implication "'a classical_propositional_formula"
                  "'a classical_propositional_formula" (infixr "\<^bold>\<rightarrow>" 70)

subsection \<open> Propositional Calculus \<close>

named_theorems classical_propositional_calculus
  "Rules for the Propositional Calculus"

inductive classical_propositional_calculus ::
  "'a classical_propositional_formula \<Rightarrow> bool" ("\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p _" [60] 55)
  where
     axiom_k [classical_propositional_calculus]:
       "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<^bold>\<rightarrow> \<psi> \<^bold>\<rightarrow> \<phi>"
   | axiom_s [classical_propositional_calculus]:
       "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<phi> \<^bold>\<rightarrow> \<psi> \<^bold>\<rightarrow> \<chi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> \<phi> \<^bold>\<rightarrow> \<chi>"
   | double_negation [classical_propositional_calculus]:
       "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ((\<phi> \<^bold>\<rightarrow> \<^bold>\<bottom>) \<^bold>\<rightarrow> \<^bold>\<bottom>) \<^bold>\<rightarrow> \<phi>"
   | modus_ponens [classical_propositional_calculus]:
        "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<^bold>\<rightarrow> \<psi> \<Longrightarrow> \<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<Longrightarrow> \<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<psi>"

instantiation classical_propositional_formula
  :: (type) classical_logic
begin
definition [simp]: "\<bottom> = \<^bold>\<bottom>"
definition [simp]: "\<turnstile> \<phi> = \<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
definition [simp]: "\<phi> \<rightarrow> \<psi> = \<phi> \<^bold>\<rightarrow> \<psi>"
instance by standard (simp add: classical_propositional_calculus)+
end

subsection \<open> Propositional Semantics \<close>

primrec classical_propositional_semantics ::
  "'a set \<Rightarrow> 'a classical_propositional_formula \<Rightarrow> bool"
  (infix "\<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p" 65)
  where
       "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p Proposition p = (p \<in> \<MM>)"
    |  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<^bold>\<rightarrow> \<psi> = (\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<longrightarrow> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<psi>)"
    |  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<^bold>\<bottom> = False"

theorem classical_propositional_calculus_soundness:
  "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<Longrightarrow> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
  by (induct rule: classical_propositional_calculus.induct, simp+)

subsection \<open> Propositional Soundness and Completeness \<close>

definition strong_classical_propositional_deduction ::
  "'a classical_propositional_formula set
    \<Rightarrow> 'a classical_propositional_formula \<Rightarrow> bool"
  (infix "\<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p" 65)
  where
    [simp]: "\<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<equiv> \<Gamma> \<tturnstile> \<phi>"

definition strong_classical_propositional_tarski_truth ::
  "'a classical_propositional_formula set
    \<Rightarrow> 'a classical_propositional_formula \<Rightarrow> bool"
  (infix "\<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p" 65)
  where
    [simp]: "\<Gamma> \<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<equiv> \<forall> \<MM>.(\<forall> \<gamma> \<in> \<Gamma>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<gamma>) \<longrightarrow> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"

definition theory_propositions ::
  "'a classical_propositional_formula set \<Rightarrow> 'a set" ("\<^bold>\<lbrace> _ \<^bold>\<rbrace>" [50])
  where
    [simp]: "\<^bold>\<lbrace> \<Gamma> \<^bold>\<rbrace> = {p . \<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p Proposition p}"

lemma truth_lemma:
  assumes "MCS \<Gamma>"
  shows "\<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<equiv> \<^bold>\<lbrace> \<Gamma> \<^bold>\<rbrace> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
proof (induct \<phi>)
  case Falsum
  then show ?case using assms by auto
next
  case (Proposition x)
  then show ?case by simp
next
  case (Implication \<psi> \<chi>)
  thus ?case
    unfolding strong_classical_propositional_deduction_def
    by (metis 
          assms
          maximally_consistent_set_def
          formula_maximally_consistent_set_def_implication
          classical_propositional_semantics.simps(2)
          implication_classical_propositional_formula_def
          set_deduction_modus_ponens
          set_deduction_reflection)
qed

theorem classical_propositional_calculus_strong_soundness_and_completeness:
  "\<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> = \<Gamma> \<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
proof -
  have soundness: "\<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<Longrightarrow> \<Gamma> \<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
  proof -
    assume "\<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
    from this obtain \<Gamma>' where \<Gamma>': "set \<Gamma>' \<subseteq> \<Gamma>" "\<Gamma>' :\<turnstile> \<phi>"
    by (simp add: set_deduction_def, blast)
    {
      fix \<MM>
      assume "\<forall> \<gamma> \<in> \<Gamma>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<gamma>"
      hence "\<forall> \<gamma> \<in> set \<Gamma>'. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<gamma>" using \<Gamma>'(1) by auto
      hence "\<forall> \<phi>. \<Gamma>' :\<turnstile> \<phi> \<longrightarrow> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
      proof (induct \<Gamma>')
        case Nil
        then show ?case
          by (simp add: classical_propositional_calculus_soundness
                        list_deduction_def)
      next
        case (Cons \<psi> \<Gamma>')
        thus ?case using list_deduction_theorem by fastforce
      qed
      with \<Gamma>'(2) have "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>" by blast
    }
    thus "\<Gamma> \<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
      using strong_classical_propositional_tarski_truth_def by blast
  qed
  have completeness: "\<Gamma> \<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<Longrightarrow> \<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
  proof (erule contrapos_pp)
    assume "\<not> \<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
    hence "\<exists> \<MM>. (\<forall> \<gamma> \<in> \<Gamma>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<gamma>) \<and> \<not> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
    proof -
      from \<open>\<not> \<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>\<close> obtain \<Omega> where \<Omega>: "\<Gamma> \<subseteq> \<Omega>" "\<phi>-MCS \<Omega>"
        by (meson formula_consistent_def
                  formula_maximally_consistent_extension
                  strong_classical_propositional_deduction_def)
      hence "(\<phi> \<rightarrow> \<bottom>) \<in> \<Omega>"
        using formula_maximally_consistent_set_def_negation by blast
      hence "\<not> \<^bold>\<lbrace> \<Omega> \<^bold>\<rbrace> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
        using \<Omega>
              formula_consistent_def
              formula_maximal_consistency
              formula_maximally_consistent_set_def_def
              truth_lemma
        unfolding strong_classical_propositional_deduction_def
        by blast
      moreover have "\<forall> \<gamma> \<in> \<Gamma>. \<^bold>\<lbrace> \<Omega> \<^bold>\<rbrace> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<gamma>"
        using formula_maximal_consistency truth_lemma \<Omega> set_deduction_reflection
        unfolding strong_classical_propositional_deduction_def
        by blast
      ultimately show ?thesis by auto
    qed
    thus "\<not> \<Gamma> \<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
      unfolding strong_classical_propositional_tarski_truth_def
      by simp
  qed
  from soundness completeness show "\<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> = \<Gamma> \<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
    by linarith
qed

theorem classical_propositional_calculus_soundness_and_completeness:
  "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> = (\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>)"
  using classical_propositional_calculus_soundness [where \<phi>="\<phi>"]
        classical_propositional_calculus_strong_soundness_and_completeness
          [where \<phi>="\<phi>" and \<Gamma>="{}"]
        strong_classical_propositional_deduction_def [where \<phi>="\<phi>" and \<Gamma>="{}"]
        strong_classical_propositional_tarski_truth_def [where \<phi>="\<phi>" and \<Gamma>="{}"]
        deduction_classical_propositional_formula_def [where \<phi>="\<phi>"]
        set_deduction_base_theory [where \<phi>="\<phi>"]
  by metis

instantiation classical_propositional_formula
  :: (type) Consistent_classical_logic
begin
instance by standard
  (simp add: classical_propositional_calculus_soundness_and_completeness)
end

primrec (in classical_logic)
   classical_propositional_formula_embedding
   :: "'a classical_propositional_formula \<Rightarrow> 'a" ("\<^bold>\<lparr> _ \<^bold>\<rparr>" [50]) where
     "\<^bold>\<lparr> \<^bold>\<langle> p \<^bold>\<rangle> \<^bold>\<rparr> = p"
   | "\<^bold>\<lparr> \<phi> \<^bold>\<rightarrow> \<psi> \<^bold>\<rparr> = \<^bold>\<lparr> \<phi> \<^bold>\<rparr> \<rightarrow> \<^bold>\<lparr> \<psi> \<^bold>\<rparr>"
   | "\<^bold>\<lparr> \<^bold>\<bottom> \<^bold>\<rparr> = \<bottom>"

theorem (in classical_logic) propositional_calculus:
  "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<Longrightarrow> \<turnstile> \<^bold>\<lparr> \<phi> \<^bold>\<rparr>"
  by (induct rule: classical_propositional_calculus.induct,
      (simp add: axiom_k axiom_s double_negation modus_ponens)+)

theorem (in classical_logic) propositional_semantics:
  "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<Longrightarrow> \<turnstile> \<^bold>\<lparr> \<phi> \<^bold>\<rparr>"
  by (simp add: 
        classical_propositional_calculus_soundness_and_completeness
        propositional_calculus)

end
