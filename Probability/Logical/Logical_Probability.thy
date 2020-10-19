(*:maxLineLen=78:*)

chapter \<open> Probability Logic \label{chapter:probability} \<close>

theory Logical_Probability
  imports
    "../../Logic/Classical/Classical_Connectives"
    HOL.Real
begin

sledgehammer_params [smt_proofs = false]

section \<open> Definition of Probability Logic \label{sec:definition-of-probability-logic} \<close>

text \<open> TODO: Hailperin "Probability Valued Logic", Kolmogorov "Elementary Theory of Probability" \<close>

class logical_probability = classical_logic +
  fixes Pr :: "'a \<Rightarrow> real"
  assumes Non_Negative: "Pr \<phi> \<ge> 0"
  assumes Unity: "\<turnstile> \<phi> \<Longrightarrow> Pr \<phi> = 1"
  assumes Implicational_Additivity:
    "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom> \<Longrightarrow> Pr ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>) = Pr \<phi> + Pr \<psi>"

subsection \<open> Why Finitely Additive Logic? \<close>

text \<open> TODO: cite Tarski, argue we won't be able to use SMT solvers. \<close>

text \<open> TODO: Discuss the value of traditional probability theory and cite Bouffon's needle. @{cite eberlBuffonNeedleProblem2017}\<close>

subsection \<open> Basic Properties of Probability Logic \<close>

lemma (in logical_probability) Additivity:
  assumes "\<turnstile> \<sim> (\<phi> \<sqinter> \<psi>)"
  shows "Pr (\<phi> \<squnion> \<psi>) = Pr \<phi> + Pr \<psi>"
  using assms
  unfolding disjunction_def
            conjunction_def
            negation_def
  by (simp add: Implicational_Additivity)

lemma (in logical_probability) Alternate_Additivity:
  assumes "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom>"
  shows "Pr (\<phi> \<squnion> \<psi>) = Pr \<phi> + Pr \<psi>"
  using assms
  by (metis Additivity
            Double_Negation_converse
            modus_ponens
            conjunction_def
            negation_def)

lemma (in logical_probability) complementation:
  "Pr (\<sim> \<phi>) = 1 - Pr \<phi>"
  by (metis Alternate_Additivity
            Unity
            bivalence
            negation_elimination
            add.commute
            add_diff_cancel_left')

lemma (in logical_probability) unity_upper_bound:
  "Pr \<phi> \<le> 1"
  by (metis (no_types) diff_ge_0_iff_ge Non_Negative complementation)

subsection \<open> Alternate Definition \<close>

text \<open> Alternate axiomatization of logical probability following Brian Weatherson in
        https://doi.org/10.1305/ndjfl/1082637807 \<close>

class Weatherson_Probability = classical_logic +
  fixes Pr :: "'a \<Rightarrow> real"
  assumes Thesis: "Pr \<top> = 1"
  assumes Antithesis: "Pr \<bottom> = 0"
  assumes Monotonicity: "\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> Pr \<phi> \<le> Pr \<psi>"
  assumes Sum_Rule: "Pr \<phi> + Pr \<psi> = Pr (\<phi> \<sqinter> \<psi>) + Pr (\<phi> \<squnion> \<psi>)"

sublocale Weatherson_Probability \<subseteq> logical_probability
proof
  fix \<phi>
  have "\<turnstile> \<bottom> \<rightarrow> \<phi>"
    by (simp add: Ex_Falso_Quodlibet)
  thus "0 \<le> Pr \<phi>"
    using Antithesis Monotonicity by fastforce
next
  fix \<phi>
  assume "\<turnstile> \<phi>"
  thus "Pr \<phi> = 1"
    by (metis Thesis
              Monotonicity
              eq_iff
              axiom_k
              Ex_Falso_Quodlibet
              modus_ponens
              verum_def)
next
  fix \<phi> \<psi>
  assume "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom>"
  thus "Pr ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>) = Pr \<phi> + Pr \<psi>"
    by (metis add.left_neutral
              eq_iff
              Antithesis
              Ex_Falso_Quodlibet
              Monotonicity
              Sum_Rule
              conjunction_negation_identity
              disjunction_def
              negation_def
              weak_biconditional_weaken)
qed

lemma (in logical_probability) monotonicity:
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

lemma (in logical_probability) biconditional_equivalence:
  "\<turnstile> \<phi> \<leftrightarrow> \<psi> \<Longrightarrow> Pr \<phi> = Pr \<psi>"
  by (meson eq_iff
            modus_ponens
            biconditional_left_elimination
            biconditional_right_elimination
            monotonicity)

lemma (in logical_probability) sum_rule:
  "Pr (\<phi> \<squnion> \<psi>) + Pr (\<phi> \<sqinter> \<psi>) = Pr \<phi> + Pr \<psi>"
proof -
  have "\<turnstile> (\<phi> \<squnion> \<psi>) \<leftrightarrow> (\<phi> \<squnion> \<psi> \<setminus> (\<phi> \<sqinter> \<psi>))"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>))"
      unfolding classical_logic_class.subtraction_def
                classical_logic_class.negation_def
                classical_logic_class.biconditional_def
                classical_logic_class.conjunction_def
                classical_logic_class.disjunction_def
      by simp
    hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis by simp
  qed
  moreover have "\<turnstile> \<phi> \<rightarrow> (\<psi> \<setminus> (\<phi> \<sqinter> \<psi>)) \<rightarrow> \<bottom>"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<rightarrow> \<bottom>"
      unfolding classical_logic_class.subtraction_def
                classical_logic_class.negation_def
                classical_logic_class.biconditional_def
                classical_logic_class.conjunction_def
                classical_logic_class.disjunction_def
      by simp
    hence "\<turnstile> \<^bold>\<lparr> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<rightarrow> \<bottom> \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis by simp
  qed
  hence "Pr (\<phi> \<squnion> \<psi>) = Pr \<phi> + Pr (\<psi> \<setminus> (\<phi> \<sqinter> \<psi>))"
    using Alternate_Additivity biconditional_equivalence calculation by auto
  moreover have "\<turnstile> \<psi> \<leftrightarrow> (\<psi> \<setminus> (\<phi> \<sqinter> \<psi>) \<squnion> (\<phi> \<sqinter> \<psi>))"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>))"
      unfolding classical_logic_class.subtraction_def
                classical_logic_class.negation_def
                classical_logic_class.biconditional_def
                classical_logic_class.conjunction_def
                classical_logic_class.disjunction_def
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

sublocale logical_probability \<subseteq> Weatherson_Probability
proof
  show "Pr \<top> = 1"
    by (simp add: Unity)
next
  show "Pr \<bottom> = 0"
    by (metis add_cancel_left_right
            Additivity
            Ex_Falso_Quodlibet
            Unity
            bivalence
            conjunction_right_elimination
            negation_def)
next
  fix \<phi> \<psi>
  assume "\<turnstile> \<phi> \<rightarrow> \<psi>"
  thus "Pr \<phi> \<le> Pr \<psi>"
    using monotonicity
    by auto
next
  fix \<phi> \<psi>
  show "Pr \<phi> + Pr \<psi> = Pr (\<phi> \<sqinter> \<psi>) + Pr (\<phi> \<squnion> \<psi>)"
    by (metis sum_rule add.commute)
qed

sublocale logical_probability \<subseteq> Consistent_classical_logic
proof
  show "\<not> \<turnstile> \<bottom>" using Unity Antithesis by auto
qed

lemma (in logical_probability) subtraction_identity:
  "Pr (\<phi> \<setminus> \<psi>) = Pr \<phi> - Pr (\<phi> \<sqinter> \<psi>)"
proof -
  have "\<turnstile> \<phi> \<leftrightarrow> ((\<phi> \<setminus> \<psi>) \<squnion> (\<phi> \<sqinter> \<psi>))"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<setminus> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>))"
      unfolding classical_logic_class.subtraction_def
                classical_logic_class.negation_def
                classical_logic_class.biconditional_def
                classical_logic_class.conjunction_def
                classical_logic_class.disjunction_def
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
      unfolding classical_logic_class.subtraction_def
                classical_logic_class.negation_def
                classical_logic_class.conjunction_def
                classical_logic_class.disjunction_def
      by simp
    hence "\<turnstile> \<^bold>\<lparr> \<sim>((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<setminus> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
      using propositional_semantics by blast
    thus ?thesis by simp
  qed
  ultimately show ?thesis
    using Additivity
    by auto
qed

lemma (in logical_probability) disjunction_sum_inequality:
  "Pr (\<phi> \<squnion> \<psi>) \<le> Pr \<phi> + Pr \<psi>"
proof -
  have "Pr (\<phi> \<squnion> \<psi>) + Pr (\<phi> \<sqinter> \<psi>) = Pr \<phi> + Pr \<psi>"
       "0 \<le> Pr (\<phi> \<sqinter> \<psi>)"
    by (simp add: sum_rule, simp add: Non_Negative)
  thus ?thesis by linarith
qed

lemma (in logical_probability) arbitrary_disjunction_list_summation_inequality:
  "Pr (\<Squnion> \<Phi>) \<le> (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>)"
proof (induct \<Phi>)
  case Nil
  then show ?case by (simp add: Antithesis)
next
  case (Cons \<phi> \<Phi>)
  have "Pr (\<Squnion> (\<phi> # \<Phi>)) \<le> Pr \<phi> + Pr (\<Squnion> \<Phi>)"
    using disjunction_sum_inequality
    by simp
  with Cons have "Pr (\<Squnion> (\<phi> # \<Phi>)) \<le> Pr \<phi> + (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>)" by linarith
  then show ?case by simp
qed

lemma (in logical_probability) implication_list_summation_inequality:
  assumes "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
  shows "Pr \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. Pr \<psi>)"
  using assms arbitrary_disjunction_list_summation_inequality monotonicity order_trans
  by blast

lemma (in logical_probability) arbitrary_disjunction_set_summation_inequality:
  "Pr (\<Squnion> \<Phi>) \<le> (\<Sum>\<phi> \<in> set \<Phi>. Pr \<phi>)"
  by (metis arbitrary_disjunction_list_summation_inequality
            arbitrary_disjunction_remdups
            biconditional_equivalence
            sum.set_conv_list)

lemma (in logical_probability) implication_set_summation_inequality:
  assumes "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
  shows "Pr \<phi> \<le> (\<Sum>\<psi> \<in> set \<Psi>. Pr \<psi>)"
  using assms arbitrary_disjunction_set_summation_inequality monotonicity order_trans
  by blast

definition (in classical_logic) logical_probabilities :: "('a \<Rightarrow> real) set"
  where "logical_probabilities =
         {Pr. class.logical_probability (\<lambda> \<phi>. \<turnstile> \<phi>) (\<rightarrow>) \<bottom> Pr }"

definition (in classical_logic) Dirac_Measures :: "('a \<Rightarrow> real) set"
  where "Dirac_Measures =
         { Pr.   class.logical_probability (\<lambda> \<phi>. \<turnstile> \<phi>) (\<rightarrow>) \<bottom> Pr
               \<and> (\<forall>x. Pr x = 0 \<or> Pr x = 1) }"

lemma (in classical_logic) Dirac_Measures_subset:
  "Dirac_Measures \<subseteq> logical_probabilities"
  unfolding logical_probabilities_def Dirac_Measures_def
  by fastforce

lemma (in classical_logic) MCS_Dirac_Measure:
  assumes "MCS \<Omega>"
    shows "(\<lambda> \<chi>. if \<chi>\<in>\<Omega> then (1 :: real) else 0) \<in> Dirac_Measures"
      (is "?Pr \<in> Dirac_Measures")
proof -
  have "class.logical_probability (\<lambda> \<phi>. \<turnstile> \<phi>) (\<rightarrow>) \<bottom> ?Pr"
  proof (standard, simp,
         meson assms
               formula_maximally_consistent_set_reflection
               Maximally_Consistent_Set_def
               set_deduction_weaken)
     fix \<phi> \<psi>
     assume "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom>"
     hence "\<turnstile> \<sim> (\<phi> \<sqinter> \<psi>)"
       by (simp add: conjunction_def negation_def)
     hence "\<phi> \<sqinter> \<psi> \<notin> \<Omega>"
       by (metis assms
                 formula_consistent_def
                 formula_maximally_consistent_set_def
                 Maximally_Consistent_Set_def
                 conjunction_def
                 conjunction_negation_identity
                 set_deduction_modus_ponens
                 set_deduction_reflection
                 set_deduction_weaken
                 weak_biconditional_weaken)
     hence "\<phi> \<notin> \<Omega> \<or> \<psi> \<notin> \<Omega>"
       using assms
             formula_maximally_consistent_set_reflection
             Maximally_Consistent_Set_def
             conjunction_set_deduction_equivalence
       by meson

     have "\<phi> \<squnion> \<psi> \<in> \<Omega> = (\<phi> \<in> \<Omega> \<or> \<psi> \<in> \<Omega>)"
       by (metis \<open>\<phi> \<sqinter> \<psi> \<notin> \<Omega>\<close>
                 assms
                 formula_maximally_consistent_set_implication
                 Maximally_Consistent_Set_def
                 conjunction_def
                 disjunction_def)
     have "?Pr (\<phi> \<squnion> \<psi>) = ?Pr \<phi> + ?Pr \<psi>"
     proof (cases "\<phi> \<squnion> \<psi> \<in> \<Omega>")
       case True
       hence \<diamondsuit>: "1 = ?Pr (\<phi> \<squnion> \<psi>)" by simp
       show ?thesis
       proof (cases "\<phi> \<in> \<Omega>")
         case True
         hence "\<psi> \<notin> \<Omega>"
           using \<open>\<phi> \<notin> \<Omega> \<or> \<psi> \<notin> \<Omega>\<close>
           by blast
         have "?Pr (\<phi> \<squnion> \<psi>) = (1::real)" using \<diamondsuit> by simp
         also have "... = 1 + (0::real)" by linarith
         also have "... = ?Pr \<phi> + ?Pr \<psi>"
           using \<open>\<psi> \<notin> \<Omega>\<close> \<open>\<phi> \<in> \<Omega>\<close> by simp
         finally show ?thesis .
       next
         case False
         hence "\<psi> \<in> \<Omega>"
           using \<open>\<phi> \<squnion> \<psi> \<in> \<Omega>\<close> \<open>(\<phi> \<squnion> \<psi> \<in> \<Omega>) = (\<phi> \<in> \<Omega> \<or> \<psi> \<in> \<Omega>)\<close>
           by blast
         have "?Pr (\<phi> \<squnion> \<psi>) = (1::real)" using \<diamondsuit> by simp
         also have "... = (0::real) + 1" by linarith
         also have "... = ?Pr \<phi> + ?Pr \<psi>"
           using \<open>\<psi> \<in> \<Omega>\<close> \<open>\<phi> \<notin> \<Omega>\<close> by simp
         finally show ?thesis .
       qed
     next
       case False
       moreover from this have "\<phi> \<notin> \<Omega>" "\<psi> \<notin> \<Omega>"
         using \<open>(\<phi> \<squnion> \<psi> \<in> \<Omega>) = (\<phi> \<in> \<Omega> \<or> \<psi> \<in> \<Omega>)\<close> by blast+
       ultimately show ?thesis by simp
     qed
     thus "?Pr ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>) = ?Pr \<phi> + ?Pr \<psi>"
       unfolding disjunction_def .
  qed
  thus ?thesis
    unfolding Dirac_Measures_def
    by simp
qed

lemma (in classical_logic) arbitrary_disjunction_exclusion_MCS:
  assumes "MCS \<Omega>"
  shows "\<Squnion> \<Psi> \<notin> \<Omega> \<equiv> \<forall> \<psi> \<in> set \<Psi>. \<psi> \<notin> \<Omega>"
proof (induct \<Psi>)
  case Nil
  then show ?case
    using assms
          formula_consistent_def
          formula_maximally_consistent_set_def
          Maximally_Consistent_Set_def
          set_deduction_reflection
    by (simp, blast)
next
  case (Cons \<psi> \<Psi>)
  have "\<Squnion> (\<psi> # \<Psi>) \<notin> \<Omega> = (\<psi> \<notin> \<Omega> \<and> \<Squnion> \<Psi> \<notin> \<Omega>)"
    by (simp add: disjunction_def,
        meson assms
              formula_consistent_def
              formula_maximally_consistent_set_def
              formula_maximally_consistent_set_implication
              Maximally_Consistent_Set_def
              set_deduction_reflection)
  thus ?case using Cons.hyps by simp
qed



end
