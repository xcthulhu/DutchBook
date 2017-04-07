theory Probability
  imports "Logic/Proof/Boolean_Propositional_Connectives" "Real"
begin

class Probability = Boolean_Propositional_Logic +
  fixes Pr :: "'a \<Rightarrow> real"
  assumes Non_Negative: "Pr \<phi> \<ge> 0"
  assumes Unity: "\<turnstile> \<phi> \<Longrightarrow> Pr \<phi> = 1"
  assumes Additivity: "\<turnstile> \<sim> (\<phi> \<sqinter> \<psi>) \<Longrightarrow> Pr (\<phi> \<squnion> \<psi>) = Pr \<phi> + Pr \<psi>"
    
lemma (in Probability) Alternate_Additivity:
  "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom> \<Longrightarrow> Pr (\<phi> \<squnion> \<psi>) = Pr \<phi> + Pr \<psi>"
  by (metis Additivity 
            Double_Negation_converse 
            Modus_Ponens 
            conjunction_def 
            negation_def)
    
lemma (in Probability) falsum_zero_probability:
  "Pr \<bottom> = 0"
  by (metis add_cancel_left_right 
            Additivity 
            Ex_Falso_Quodlibet 
            Unity 
            bivalence 
            conjunction_right_elimination 
            negation_def)

lemma (in Probability) falsum_implication_zero_probability:
  "\<turnstile> \<phi> \<rightarrow> \<bottom> \<Longrightarrow> Pr \<phi> = 0"
  by (smt Alternate_Additivity Unity bivalence negation_def negation_elimination)
  
lemma (in Probability) complementation:
  "Pr (\<sim> \<phi>) = 1 - Pr \<phi>"
  by (smt Alternate_Additivity Unity bivalence negation_elimination)

lemma (in Probability) unity_upper_bound:
  "Pr \<phi> \<le> 1"
  by (smt Non_Negative complementation)
    
lemma (in Probability) monotonicity:
  "\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> Pr \<phi> \<le> Pr \<psi>"
  by (smt Alternate_Additivity 
          Modus_Ponens 
          complementation 
          flip_hypothetical_syllogism 
          negation_def 
          unity_upper_bound)

theorem Probabilistic_Boolean_Propositional_Calculus_Inquality_Completeness:
  "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<rightarrow> \<psi> \<equiv> \<forall> Pr. class.Probability (\<lambda> \<phi>. \<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>) (op \<^bold>\<rightarrow>) \<^bold>\<bottom> Pr \<longrightarrow>  Pr \<phi> \<le> Pr \<psi>"
proof -
  {
    fix Pr :: "'a Boolean_Propositional_Formula \<Rightarrow> real"
    assume "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<rightarrow> \<psi>"
    hence "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<^bold>\<rightarrow> \<psi>" by simp 
    moreover assume "class.Probability (\<lambda> \<phi>. \<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>) (op \<^bold>\<rightarrow>) \<^bold>\<bottom> Pr"
    ultimately have "Pr \<phi> \<le> Pr \<psi>"
      using Probability.Probability.monotonicity
      by smt
  }
  moreover
  {
    assume "\<not> \<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<rightarrow> \<psi>"
    from this obtain \<MM> where \<MM>: "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>" "\<not> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p  \<psi>"
      using Boolean_Propositional_Calculus_Soundness_And_Completeness by fastforce
    let ?Pr = "\<lambda> \<chi>. if (\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<chi>) then (1 :: real) else 0 "
    have "\<not> (?Pr \<phi> \<le> ?Pr \<psi>)" using \<MM> by simp
    moreover
    interpret Boolean_Propositional_Logic "(\<lambda> \<phi>. \<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>)" "(op \<^bold>\<rightarrow>)" "\<^bold>\<bottom>"
      by (standard, simp add: Boolean_Propositional_Calculus.Axiom_1,
                    simp add: Boolean_Propositional_Calculus.Axiom_2,
                    simp add: Boolean_Propositional_Calculus.Modus_Ponens,
                    simp add: Boolean_Propositional_Calculus.Double_Negation)
    have  "class.Probability (\<lambda> \<phi>. \<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>) (op \<^bold>\<rightarrow>) \<^bold>\<bottom> ?Pr"
    by (standard, simp add: Boolean_Propositional_Calculus.Axiom_1,
                  simp add: Boolean_Propositional_Calculus.Axiom_2,
                  simp add: Boolean_Propositional_Calculus.Modus_Ponens,
                  simp add: Boolean_Propositional_Calculus.Double_Negation,
                  simp,
                  simp add: Boolean_Propositional_Calculus_Soundness,
                  simp add: negation_def conjunction_def disjunction_def 
                            Boolean_Propositional_Calculus_Soundness_And_Completeness)
   ultimately have 
      "\<exists> Pr. class.Probability (\<lambda> \<phi>. \<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>) (op \<^bold>\<rightarrow>) \<^bold>\<bottom> Pr \<and> \<not> (Pr \<phi> \<le> Pr \<psi>)"
      by blast
  }
  ultimately show   
    "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<rightarrow> \<psi> \<equiv> \<forall> Pr. class.Probability (\<lambda> \<phi>. \<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>) (op \<^bold>\<rightarrow>) \<^bold>\<bottom> Pr \<longrightarrow> Pr \<phi> \<le> Pr \<psi>"
    by smt
qed        
        
lemma (in Probability) biconditional_equivalence:
  "\<turnstile> \<phi> \<leftrightarrow> \<psi> \<Longrightarrow> Pr \<phi> = Pr \<psi>"
  by (meson eq_iff 
            Modus_Ponens 
            biconditional_left_elimination 
            biconditional_right_elimination 
            monotonicity)
          
lemma (in Probability) sum_rule:
  "Pr (\<phi> \<squnion> \<psi>) + Pr (\<phi> \<sqinter> \<psi>) = Pr \<phi> + Pr \<psi>"
proof -
  have "\<turnstile> (\<phi> \<squnion> \<psi>) \<leftrightarrow> (\<phi> \<squnion> \<psi> \<setminus> (\<phi> \<sqinter> \<psi>))"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>))"
      unfolding Boolean_Propositional_Logic_class.subtraction_def
                Minimal_Logic_With_Falsum_class.negation_def
                Boolean_Propositional_Logic_class.biconditional_def 
                Boolean_Propositional_Logic_class.conjunction_def
                Boolean_Propositional_Logic_class.disjunction_def
      by simp
    hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis by simp
  qed
  moreover have "\<turnstile> \<phi> \<rightarrow> (\<psi> \<setminus> (\<phi> \<sqinter> \<psi>)) \<rightarrow> \<bottom>"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<rightarrow> \<bottom>"
      unfolding Boolean_Propositional_Logic_class.subtraction_def
                Minimal_Logic_With_Falsum_class.negation_def
                Boolean_Propositional_Logic_class.biconditional_def 
                Boolean_Propositional_Logic_class.conjunction_def
                Boolean_Propositional_Logic_class.disjunction_def
      by simp
    hence "\<turnstile> \<^bold>\<lparr> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<rightarrow> \<bottom> \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis by simp
  qed
  hence "Pr (\<phi> \<squnion> \<psi>) = Pr \<phi> + Pr (\<psi> \<setminus> (\<phi> \<sqinter> \<psi>))"
    using Alternate_Additivity biconditional_equivalence calculation by auto
  moreover have "\<turnstile> \<psi> \<leftrightarrow> (\<psi> \<setminus> (\<phi> \<sqinter> \<psi>) \<squnion> (\<phi> \<sqinter> \<psi>))"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>))"
      unfolding Boolean_Propositional_Logic_class.subtraction_def
                Minimal_Logic_With_Falsum_class.negation_def
                Boolean_Propositional_Logic_class.biconditional_def 
                Boolean_Propositional_Logic_class.conjunction_def
                Boolean_Propositional_Logic_class.disjunction_def
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

end