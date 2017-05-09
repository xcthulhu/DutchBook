theory Weakly_Additive_Logical_Probability
  imports "../../../Logic/Proof/Classical/Classical_Propositional_Connectives" 
          Real
begin
  
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
  by (smt Alternate_Additivity Unity bivalence negation_def negation_elimination)
  
lemma (in Weakly_Additive_Logical_Probability) complementation:
  "Pr (\<sim> \<phi>) = 1 - Pr \<phi>"
  by (smt Alternate_Additivity Unity bivalence negation_elimination)

lemma (in Weakly_Additive_Logical_Probability) unity_upper_bound:
  "Pr \<phi> \<le> 1"
  by (smt Non_Negative complementation)
    
lemma (in Weakly_Additive_Logical_Probability) monotonicity:
  "\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> Pr \<phi> \<le> Pr \<psi>"
  by (smt Alternate_Additivity 
          Modus_Ponens 
          complementation 
          flip_hypothetical_syllogism 
          negation_def 
          unity_upper_bound)
           
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
    by smt
qed
  
end
