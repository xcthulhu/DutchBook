theory Weakly_Additive_Logical_Probability
  imports "../../../Logic/Proof/Classical/Classical_Propositional_Connectives"
begin

sledgehammer_params [smt_proofs = false]

class Weakly_Additive_Logical_Probability = Classical_Propositional_Logic +
  fixes Pr :: "'a \<Rightarrow> real"
  assumes Non_Negative: "Pr \<phi> \<ge> 0"
  assumes Unity: "\<turnstile> \<phi> \<Longrightarrow> Pr \<phi> = 1"
  assumes Additivity: "\<turnstile> \<sim> (\<phi> \<sqinter> \<psi>) \<Longrightarrow> Pr (\<phi> \<squnion> \<psi>) = Pr \<phi> + Pr \<psi>"

lemma (in Weakly_Additive_Logical_Probability) Alternate_Additivity:
  "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom> \<Longrightarrow> Pr (\<phi> \<squnion> \<psi>) = Pr \<phi> + Pr \<psi>"
  by (metis Additivity
            Double_Negation_converse
            Modus_Ponens
            conjunction_def
            negation_def)

lemma (in Weakly_Additive_Logical_Probability) falsum_zero_probability:
  "Pr \<bottom> = 0"
  by (metis add_cancel_left_right
            Additivity
            Ex_Falso_Quodlibet
            Unity
            bivalence
            conjunction_right_elimination
            negation_def)

lemma (in Weakly_Additive_Logical_Probability) consistency: "\<not> \<turnstile> \<bottom>"
  using Unity falsum_zero_probability by auto

lemma (in Weakly_Additive_Logical_Probability) falsum_implication_zero_probability:
  "\<turnstile> \<phi> \<rightarrow> \<bottom> \<Longrightarrow> Pr \<phi> = 0"
proof -
  assume "\<turnstile> \<phi> \<rightarrow> \<bottom>"
  moreover have "\<forall>\<phi> \<psi>. \<not> \<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom> \<or> Pr \<psi> + - 1 * Pr (\<phi> \<squnion> \<psi>) + Pr \<phi> = 0"
    by (simp add: Alternate_Additivity)
  then have "Pr \<phi> + - 1 * Pr (\<sim> \<phi> \<squnion> \<phi>) + Pr (\<sim> \<phi>) = 0"
    by (meson Alternate_Additivity negation_elimination)
  ultimately show ?thesis
    using Unity bivalence negation_def by auto
qed

lemma (in Weakly_Additive_Logical_Probability) complementation:
  "Pr (\<sim> \<phi>) = 1 - Pr \<phi>"
  by (metis Alternate_Additivity
            Unity
            bivalence
            negation_elimination
            add.commute
            add_diff_cancel_left')

lemma (in Weakly_Additive_Logical_Probability) unity_upper_bound:
  "Pr \<phi> \<le> 1"
  by (metis (no_types) diff_ge_0_iff_ge Non_Negative complementation)

lemma (in Weakly_Additive_Logical_Probability) monotonicity:
  "\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> Pr \<phi> \<le> Pr \<psi>"
proof -
  assume "\<turnstile> \<phi> \<rightarrow> \<psi>"
  hence "\<turnstile> \<sim> (\<phi> \<sqinter> \<sim> \<psi>)"
    unfolding negation_def conjunction_def
    by (metis conjunction_def
              exclusion_contrapositive_equivalence
              negation_def
              weak_biconditional_weaken)
  hence "Pr (\<phi> \<squnion> \<sim> \<psi>) = Pr \<phi> + Pr (\<sim> \<psi>)"
    by (simp add: Additivity)
  hence "Pr \<phi> + Pr (\<sim> \<psi>) \<le> 1"
    by (metis unity_upper_bound)
  hence "Pr \<phi> + 1 - Pr \<psi> \<le> 1"
    by (simp add: complementation)
  thus ?thesis by linarith
qed

lemma (in Weakly_Additive_Logical_Probability) biconditional_equivalence:
  "\<turnstile> \<phi> \<leftrightarrow> \<psi> \<Longrightarrow> Pr \<phi> = Pr \<psi>"
  by (meson eq_iff
            Modus_Ponens
            biconditional_left_elimination
            biconditional_right_elimination
            monotonicity)

lemma (in Weakly_Additive_Logical_Probability) sum_rule:
  "Pr (\<phi> \<squnion> \<psi>) + Pr (\<phi> \<sqinter> \<psi>) = Pr \<phi> + Pr \<psi>"
proof -
  have "\<turnstile> (\<phi> \<squnion> \<psi>) \<leftrightarrow> (\<phi> \<squnion> \<psi> \<setminus> (\<phi> \<sqinter> \<psi>))"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>))"
      unfolding Classical_Propositional_Logic_class.subtraction_def
                Minimal_Logic_With_Falsum_class.negation_def
                Classical_Propositional_Logic_class.biconditional_def
                Classical_Propositional_Logic_class.conjunction_def
                Classical_Propositional_Logic_class.disjunction_def
      by simp
    hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis by simp
  qed
  moreover have "\<turnstile> \<phi> \<rightarrow> (\<psi> \<setminus> (\<phi> \<sqinter> \<psi>)) \<rightarrow> \<bottom>"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<rightarrow> \<bottom>"
      unfolding Classical_Propositional_Logic_class.subtraction_def
                Minimal_Logic_With_Falsum_class.negation_def
                Classical_Propositional_Logic_class.biconditional_def
                Classical_Propositional_Logic_class.conjunction_def
                Classical_Propositional_Logic_class.disjunction_def
      by simp
    hence "\<turnstile> \<^bold>\<lparr> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<rightarrow> \<bottom> \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis by simp
  qed
  hence "Pr (\<phi> \<squnion> \<psi>) = Pr \<phi> + Pr (\<psi> \<setminus> (\<phi> \<sqinter> \<psi>))"
    using Alternate_Additivity biconditional_equivalence calculation by auto
  moreover have "\<turnstile> \<psi> \<leftrightarrow> (\<psi> \<setminus> (\<phi> \<sqinter> \<psi>) \<squnion> (\<phi> \<sqinter> \<psi>))"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>))"
      unfolding Classical_Propositional_Logic_class.subtraction_def
                Minimal_Logic_With_Falsum_class.negation_def
                Classical_Propositional_Logic_class.biconditional_def
                Classical_Propositional_Logic_class.conjunction_def
                Classical_Propositional_Logic_class.disjunction_def
      by auto
    hence "\<turnstile> \<^bold>\<lparr> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis by simp
  qed
  moreover have "\<turnstile> (\<psi> \<setminus> (\<phi> \<sqinter> \<psi>)) \<rightarrow> (\<phi> \<sqinter> \<psi>) \<rightarrow> \<bottom>"
    unfolding subtraction_def negation_def conjunction_def
    using conjunction_def conjunction_right_elimination by auto
  hence "Pr \<psi> = Pr (\<psi> \<setminus> (\<phi> \<sqinter> \<psi>)) + Pr (\<phi> \<sqinter> \<psi>)"
    using Alternate_Additivity biconditional_equivalence calculation by auto
  ultimately show ?thesis
    by simp
qed

lemma (in Weakly_Additive_Logical_Probability) subtraction_identity:
  "Pr (\<phi> \<setminus> \<psi>) = Pr \<phi> - Pr (\<phi> \<sqinter> \<psi>)"
proof -
  have "\<turnstile> \<phi> \<leftrightarrow> ((\<phi> \<setminus> \<psi>) \<squnion> (\<phi> \<sqinter> \<psi>))"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<setminus> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>))"
      unfolding Classical_Propositional_Logic_class.subtraction_def
                Minimal_Logic_With_Falsum_class.negation_def
                Classical_Propositional_Logic_class.biconditional_def
                Classical_Propositional_Logic_class.conjunction_def
                Classical_Propositional_Logic_class.disjunction_def
      by (simp, blast)
    hence "\<turnstile> \<^bold>\<lparr> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<setminus> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
      using propositional_semantics by blast
    thus ?thesis by simp
  qed
  hence "Pr \<phi>  = Pr ((\<phi> \<setminus> \<psi>) \<squnion> (\<phi> \<sqinter> \<psi>))"
    using biconditional_equivalence
    by simp
  moreover have "\<turnstile> \<sim>((\<phi> \<setminus> \<psi>) \<sqinter> (\<phi> \<sqinter> \<psi>))"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<sim>((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<setminus> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>))"
      unfolding Classical_Propositional_Logic_class.subtraction_def
                Minimal_Logic_With_Falsum_class.negation_def
                Classical_Propositional_Logic_class.conjunction_def
                Classical_Propositional_Logic_class.disjunction_def
      by simp
    hence "\<turnstile> \<^bold>\<lparr> \<sim>((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<setminus> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
      using propositional_semantics by blast
    thus ?thesis by simp
  qed
  ultimately show ?thesis
    using Additivity
    by auto
qed

lemma (in Weakly_Additive_Logical_Probability) disjunction_sum_inequality:
  "Pr (\<phi> \<squnion> \<psi>) \<le> Pr \<phi> + Pr \<psi>"
proof -
  have "Pr (\<phi> \<squnion> \<psi>) + Pr (\<phi> \<sqinter> \<psi>) = Pr \<phi> + Pr \<psi>"
       "0 \<le> Pr (\<phi> \<sqinter> \<psi>)"
    by (simp add: sum_rule, simp add: Non_Negative)
  thus ?thesis by linarith
qed

lemma (in Weakly_Additive_Logical_Probability) arbitrary_disjunction_list_summation_inequality:
  "Pr (\<Squnion> \<Phi>) \<le> (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>)"
proof (induct \<Phi>)
  case Nil
  then show ?case by (simp add: falsum_zero_probability)
next
  case (Cons \<phi> \<Phi>)
  have "Pr (\<Squnion> (\<phi> # \<Phi>)) \<le> Pr \<phi> + Pr (\<Squnion> \<Phi>)"
    using disjunction_sum_inequality
    by simp
  with Cons have "Pr (\<Squnion> (\<phi> # \<Phi>)) \<le> Pr \<phi> + (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>)" by linarith
  then show ?case by simp
qed

lemma (in Weakly_Additive_Logical_Probability) implication_list_summation_inequality:
  assumes "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
  shows "Pr \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. Pr \<psi>)"
  using assms arbitrary_disjunction_list_summation_inequality monotonicity order_trans
  by blast

lemma (in Weakly_Additive_Logical_Probability) arbitrary_disjunction_set_summation_inequality:
  "Pr (\<Squnion> \<Phi>) \<le> (\<Sum>\<phi> \<in> set \<Phi>. Pr \<phi>)"
  by (metis arbitrary_disjunction_list_summation_inequality
            arbitrary_disjunction_remdups
            biconditional_equivalence
            sum.set_conv_list)

lemma (in Weakly_Additive_Logical_Probability) implication_set_summation_inequality:
  assumes "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
  shows "Pr \<phi> \<le> (\<Sum>\<psi> \<in> set \<Psi>. Pr \<psi>)"
  using assms arbitrary_disjunction_set_summation_inequality monotonicity order_trans
  by blast

definition (in Classical_Propositional_Logic) Weakly_Additive_Probabilities :: "('a \<Rightarrow> real) set"
  where "Weakly_Additive_Probabilities =
         {Pr. class.Weakly_Additive_Logical_Probability (\<lambda> \<phi>. \<turnstile> \<phi>) (op \<rightarrow>) \<bottom> Pr }"

definition (in Classical_Propositional_Logic) Binary_Probabilities :: "('a \<Rightarrow> real) set"
  where "Binary_Probabilities =
         {Pr.   class.Weakly_Additive_Logical_Probability (\<lambda> \<phi>. \<turnstile> \<phi>) (op \<rightarrow>) \<bottom> Pr
              \<and> (\<forall>x. Pr x = 0 \<or> Pr x = 1)}"

lemma (in Classical_Propositional_Logic) Binary_Probabilities_subset:
  "Binary_Probabilities \<subseteq> Weakly_Additive_Probabilities"
  unfolding Weakly_Additive_Probabilities_def Binary_Probabilities_def
  by fastforce

lemma (in Classical_Propositional_Logic) MCS_Binary_Weakly_Additive_Logical_Probability:
  assumes "MCS \<Omega>"
    shows "(\<lambda> \<chi>. if \<chi>\<in>\<Omega> then (1 :: real) else 0) \<in> Binary_Probabilities"
      (is "?Pr \<in> Binary_Probabilities")
proof -
  have "class.Weakly_Additive_Logical_Probability (\<lambda> \<phi>. \<turnstile> \<phi>) (op \<rightarrow>) \<bottom> ?Pr"
  proof (standard, simp,
         meson assms
               Formula_Maximally_Consistent_Set_reflection
               Maximally_Consistent_Set_def
               set_deduction_weaken)
     fix \<phi> \<psi>
     assume "\<turnstile> \<sim> (\<phi> \<sqinter> \<psi>)"
     hence "\<phi> \<sqinter> \<psi> \<notin> \<Omega>"
       by (metis assms
                 Formula_Consistent_def
                 Formula_Maximally_Consistent_Set_def
                 Maximally_Consistent_Set_def
                 conjunction_def
                 conjunction_negation_identity
                 set_deduction_modus_ponens
                 set_deduction_reflection
                 set_deduction_weaken
                 weak_biconditional_weaken)
     hence "\<phi> \<notin> \<Omega> \<or> \<psi> \<notin> \<Omega>"
       using assms
             Formula_Maximally_Consistent_Set_reflection
             Maximally_Consistent_Set_def
             conjunction_set_deduction_equivalence
       by meson

     have "\<phi> \<squnion> \<psi> \<in> \<Omega> = (\<phi> \<in> \<Omega> \<or> \<psi> \<in> \<Omega>)"
       by (metis \<open>\<phi> \<sqinter> \<psi> \<notin> \<Omega>\<close>
                 assms
                 Formula_Maximally_Consistent_Set_implication
                 Maximally_Consistent_Set_def
                 conjunction_def
                 disjunction_def)
     show "(if \<phi> \<squnion> \<psi> \<in> \<Omega> then (1::real) else 0)
         = (if \<phi> \<in> \<Omega> then (1::real) else 0) + (if \<psi> \<in> \<Omega> then (1::real) else 0)"
     proof (cases "\<phi> \<squnion> \<psi> \<in> \<Omega>")
       case True
       hence \<diamondsuit>: "1 = (if \<phi> \<squnion> \<psi> \<in> \<Omega> then (1::real) else 0)" by simp
       show ?thesis
       proof (cases "\<phi> \<in> \<Omega>")
         case True
         hence "\<psi> \<notin> \<Omega>"
           using \<open>\<phi> \<notin> \<Omega> \<or> \<psi> \<notin> \<Omega>\<close>
           by blast
         have "(if \<phi> \<squnion> \<psi> \<in> \<Omega> then 1 else 0) = (1::real)" using \<diamondsuit> by simp
         also have "... = 1 + (0::real)" by linarith
         also have "... = (if \<phi> \<in> \<Omega> then 1 else 0) + (if \<psi> \<in> \<Omega> then 1 else 0)"
           using \<open>\<psi> \<notin> \<Omega>\<close> \<open>\<phi> \<in> \<Omega>\<close> by simp
         finally show ?thesis .
       next
         case False
         hence "\<psi> \<in> \<Omega>"
           using \<open>\<phi> \<squnion> \<psi> \<in> \<Omega>\<close> \<open>(\<phi> \<squnion> \<psi> \<in> \<Omega>) = (\<phi> \<in> \<Omega> \<or> \<psi> \<in> \<Omega>)\<close>
           by blast
         have "(if \<phi> \<squnion> \<psi> \<in> \<Omega> then 1 else 0) = (1::real)" using \<diamondsuit> by simp
         also have "... = (0::real) + 1" by linarith
         also have "... = (if \<phi> \<in> \<Omega> then 1 else 0) + (if \<psi> \<in> \<Omega> then 1 else 0)"
           using \<open>\<psi> \<in> \<Omega>\<close> \<open>\<phi> \<notin> \<Omega>\<close> by simp
         finally show ?thesis .
       qed
     next
       case False
       moreover from this have "\<phi> \<notin> \<Omega>" "\<psi> \<notin> \<Omega>"
         using \<open>(\<phi> \<squnion> \<psi> \<in> \<Omega>) = (\<phi> \<in> \<Omega> \<or> \<psi> \<in> \<Omega>)\<close> by blast+
       ultimately show ?thesis by simp
     qed
  qed
  thus ?thesis
    unfolding Binary_Probabilities_def
    by simp
qed

lemma (in Classical_Propositional_Logic) arbitrary_disjunction_exclusion_MCS:
  assumes "MCS \<Omega>"
  shows "\<Squnion> \<Psi> \<notin> \<Omega> \<equiv> \<forall> \<psi> \<in> set \<Psi>. \<psi> \<notin> \<Omega>"
proof (induct \<Psi>)
  case Nil
  then show ?case
    using assms
          Formula_Consistent_def
          Formula_Maximally_Consistent_Set_def
          Maximally_Consistent_Set_def
          set_deduction_reflection
    by (simp, blast)
next
  case (Cons \<psi> \<Psi>)
  have "\<Squnion> (\<psi> # \<Psi>) \<notin> \<Omega> = (\<psi> \<notin> \<Omega> \<and> \<Squnion> \<Psi> \<notin> \<Omega>)"
    by (simp add: disjunction_def,
        meson assms
              Formula_Consistent_def
              Formula_Maximally_Consistent_Set_def
              Formula_Maximally_Consistent_Set_implication
              Maximally_Consistent_Set_def
              set_deduction_reflection)
  thus ?case using Cons.hyps by simp
qed

end
