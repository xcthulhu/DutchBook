theory Elementary_Probability_Completeness
  imports Probability
begin

definition (in Classical_Propositional_Logic) Binary_Probabilities :: "('a \<Rightarrow> real) set"
  where "Binary_Probabilities = 
         {Pr. class.Probability (\<lambda> \<phi>. \<turnstile> \<phi>) (op \<rightarrow>) \<bottom> Pr \<and> (\<forall>x. Pr x = 0 \<or> Pr x = 1)}" 

lemma (in Classical_Propositional_Logic) MCS_Binary_Probability:
  assumes "MCS \<Omega>"
    shows "(\<lambda> \<chi>. if \<chi>\<in>\<Omega> then (1 :: real) else 0) \<in> Binary_Probabilities"
      (is "?Pr \<in> Binary_Probabilities")
proof -
  have "class.Probability (\<lambda> \<phi>. \<turnstile> \<phi>) (op \<rightarrow>) \<bottom> ?Pr"
      by (standard,
          simp,
          meson assms
                Formula_Maximally_Consistent_Set_reflection 
                Maximally_Consistent_Set_def 
                set_deduction_weaken,
         smt assms
             Formula_Consistent_def 
             Formula_Maximally_Consistent_Set_def 
             Formula_Maximally_Consistent_Set_implication 
             Formula_Maximally_Consistent_Set_reflection 
             Maximally_Consistent_Set_def 
             conjunction_def 
             disjunction_def 
             negation_def 
             set_deduction_weaken)
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
  have "\<Squnion> (\<psi> # \<Psi>) \<notin> \<Omega> \<equiv> \<psi> \<notin> \<Omega> \<and> \<Squnion> \<Psi> \<notin> \<Omega>"
    by (simp add: disjunction_def, 
        smt assms 
            Formula_Consistent_def 
            Formula_Maximally_Consistent_Set_def
            Formula_Maximally_Consistent_Set_implication
            Maximally_Consistent_Set_def 
            set_deduction_reflection)
  thus ?case using Cons.hyps by simp
qed  
  
lemma (in Probability) arbitrary_disjunction_list_summation_inequality:
  "Pr (\<Squnion> \<Phi>) \<le> (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>)"
  by (induct \<Phi>, 
      simp, smt falsum_zero_probability, 
      simp, smt Non_Negative sum_rule sum_list.Cons)
  
lemma (in Probability) implication_list_summation_inequality:
  assumes "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
  shows "Pr \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. Pr \<psi>)"
  using assms arbitrary_disjunction_list_summation_inequality monotonicity order_trans 
  by blast
    
theorem (in Classical_Propositional_Logic) List_Summation_Completeness:
  "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi> \<equiv> \<forall> Pr \<in> Binary_Probabilities. Pr \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. Pr \<psi>)"
proof -
  {
    fix Pr :: "'a \<Rightarrow> real"
    assume "Pr \<in> Binary_Probabilities"
    from this interpret Probability "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(op \<rightarrow>)" "\<bottom>" "Pr"
      unfolding Binary_Probabilities_def
      by auto
    assume "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
    hence "Pr \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. Pr \<psi>)"
      using implication_list_summation_inequality
      by auto
  }
  moreover {
    assume "\<not> \<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
    from this obtain \<Omega> where \<Omega>: "MCS \<Omega>" "\<phi> \<in> \<Omega>" "\<Squnion> \<Psi> \<notin> \<Omega>"
      by (meson insert_subset 
                Formula_Consistent_def 
                Formula_Maximal_Consistency 
                Formula_Maximally_Consistent_Extension 
                Formula_Maximally_Consistent_Set_def 
                set_deduction_base_theory 
                set_deduction_reflection 
                set_deduction_theorem)
    hence"\<forall> \<psi> \<in> set \<Psi>. \<psi> \<notin> \<Omega>"
      using arbitrary_disjunction_exclusion_MCS by blast
    let ?Pr = "\<lambda> \<chi>. if \<chi>\<in>\<Omega> then (1 :: real) else 0"
    from \<open>\<forall> \<psi> \<in> set \<Psi>. \<psi> \<notin> \<Omega>\<close> have "(\<Sum>\<psi>\<leftarrow>\<Psi>. ?Pr \<psi>) = 0"
      by (induct \<Psi>, simp, simp)
    hence "\<not> ?Pr \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. ?Pr \<psi>)"
      by (simp add: \<Omega>(2))
    hence
      "\<exists> Pr \<in> Binary_Probabilities. \<not> (Pr \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. Pr \<psi>))"
      using \<Omega>(1) MCS_Binary_Probability by auto
  }
  ultimately show 
    "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi> \<equiv> \<forall> Pr \<in> Binary_Probabilities. Pr \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. Pr \<psi>)"
    by smt
qed
    
lemma (in Probability) arbitrary_disjunction_set_summation_inequality:
  "Pr (\<Squnion> \<Phi>) \<le> (\<Sum>\<phi> \<in> set \<Phi>. Pr \<phi>)"
  by (metis arbitrary_disjunction_list_summation_inequality 
            arbitrary_disjunction_remdups
            biconditional_equivalence 
            sum.set_conv_list) 

lemma (in Probability) implication_set_summation_inequality:
  assumes "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
  shows "Pr \<phi> \<le> (\<Sum>\<psi> \<in> set \<Psi>. Pr \<psi>)"
  using assms arbitrary_disjunction_set_summation_inequality monotonicity order_trans 
  by blast

theorem (in Classical_Propositional_Logic) Set_Summation_Completeness:
  "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi> \<equiv> \<forall> Pr \<in> Binary_Probabilities. Pr \<phi> \<le> (\<Sum>\<psi>\<in> set \<Psi>. Pr \<psi>)"
  by (smt List_Summation_Completeness 
          Modus_Ponens 
          arbitrary_disjunction_remdups 
          biconditional_left_elimination 
          biconditional_right_elimination 
          hypothetical_syllogism 
          sum.set_conv_list)
  
lemma (in Probability) exclusive_sum_list_identity:
  assumes "\<turnstile> exclusive \<Phi>"
  shows "Pr (\<Squnion> \<Phi>) = (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>)"
  using assms
proof (induct \<Phi>)
  case Nil
  then show ?case by (simp add: falsum_zero_probability) 
next
  case (Cons \<phi> \<Phi>)
  assume "\<turnstile> exclusive (\<phi> # \<Phi>)"
  hence "\<turnstile> \<sim> (\<phi> \<sqinter> \<Squnion> \<Phi>)" "\<turnstile> exclusive \<Phi>" by simp+
  hence "Pr(\<Squnion>(\<phi> # \<Phi>)) = Pr \<phi> + Pr (\<Squnion> \<Phi>)"  
        "Pr (\<Squnion> \<Phi>) = (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>)" using Cons.hyps Additivity by auto
  hence "Pr(\<Squnion>(\<phi> # \<Phi>)) = Pr \<phi> + (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>)" by auto
  thus ?case by simp
qed  
  
lemma sum_list_monotone:
  fixes f :: "'a \<Rightarrow> real"
  assumes "\<forall> x. f x \<ge> 0"
     and  "set \<Phi> \<subseteq> set \<Psi>"
     and  "distinct \<Phi>"
   shows "(\<Sum>\<phi>\<leftarrow>\<Phi>. f \<phi>) \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. f \<psi>)"
  using assms
proof -
  assume "\<forall> x. f x \<ge> 0"
  have "\<forall>\<Phi>. set \<Phi> \<subseteq> set \<Psi> \<longrightarrow> distinct \<Phi> \<longrightarrow> (\<Sum>\<phi>\<leftarrow>\<Phi>. f \<phi>) \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. f \<psi>)"
  proof (induct \<Psi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<psi> \<Psi>)
    {
      fix \<Phi>
      assume "set \<Phi> \<subseteq> set (\<psi> # \<Psi>)"
         and "distinct \<Phi>"
      have "(\<Sum>\<phi>\<leftarrow>\<Phi>. f \<phi>) \<le> (\<Sum>\<psi>'\<leftarrow>(\<psi> # \<Psi>). f \<psi>')"
      proof -
        {
          assume "\<psi> \<notin> set \<Phi>"
          with \<open>set \<Phi> \<subseteq> set (\<psi> # \<Psi>)\<close> have "set \<Phi> \<subseteq> set \<Psi>" by auto
          hence "(\<Sum>\<phi>\<leftarrow>\<Phi>. f \<phi>) \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. f \<psi>)" 
            using Cons.hyps \<open>distinct \<Phi>\<close> by auto
          hence ?thesis
            using \<open>\<forall> x. f x \<ge> 0\<close> by (simp, smt)
        }
        moreover
        {
          assume "\<psi> \<in> set \<Phi>"
          from \<open>\<psi> \<in> set \<Phi>\<close> have "set \<Phi> = insert \<psi> (set (removeAll \<psi> \<Phi>))"
            by auto
          with \<open>set \<Phi> \<subseteq> set (\<psi> # \<Psi>)\<close> have "set (removeAll \<psi> \<Phi>) \<subseteq> set \<Psi>"
            by (metis insert_subset list.simps(15) set_removeAll subset_insert_iff)
          moreover from \<open>distinct \<Phi>\<close> have "distinct (removeAll \<psi> \<Phi>)"
            by (meson distinct_removeAll)
          ultimately have "(\<Sum>\<phi>\<leftarrow>(removeAll \<psi> \<Phi>). f \<phi>) \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. f \<psi>)"
            using Cons.hyps
            by simp
          moreover from \<open>\<psi> \<in> set \<Phi>\<close> \<open>distinct \<Phi>\<close> 
          have "(\<Sum>\<phi>\<leftarrow>\<Phi>. f \<phi>) = f \<psi> + (\<Sum>\<phi>\<leftarrow>(removeAll \<psi> \<Phi>). f \<phi>)"
            using distinct_remove1_removeAll sum_list_map_remove1 by fastforce
          ultimately have ?thesis using \<open>\<forall> x. f x \<ge> 0\<close>
            by simp
        }
        ultimately show ?thesis by blast
      qed
    }        
    thus ?case by blast       
  qed
  moreover assume "set \<Phi> \<subseteq> set \<Psi>" and "distinct \<Phi>"
  ultimately show ?thesis by blast
qed

lemma count_remove_all_sum_list:
  fixes f :: "'a \<Rightarrow> real"
  shows "real (count_list xs x) * f x + (\<Sum>x'\<leftarrow>(removeAll x xs). f x') = (\<Sum>x\<leftarrow>xs. f x)"
    by (induct xs, simp, simp, smt semiring_normalization_rules(3))

theorem (in Classical_Propositional_Logic) Exclusive_Implication_Completeness:
  "\<turnstile> exclusive \<Phi> \<and>  \<turnstile> \<Squnion> \<Phi> \<rightarrow> \<psi> \<equiv> \<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> Pr \<psi>"
proof -
  {
    fix Pr
    assume "Pr \<in> Binary_Probabilities"
    from this interpret Probability "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(op \<rightarrow>)" "\<bottom>" "Pr"
      unfolding Binary_Probabilities_def
      by simp
    assume "\<turnstile> exclusive \<Phi>" "\<turnstile> \<Squnion> \<Phi> \<rightarrow> \<psi>"
    hence "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> Pr \<psi>"
      using exclusive_sum_list_identity monotonicity by fastforce
  }
  moreover
  {
    assume "\<not> \<turnstile> exclusive \<Phi>"
    hence "(\<exists> \<phi> \<in> set \<Phi>. \<exists> \<psi> \<in> set \<Phi>. \<phi> \<noteq> \<psi> \<and> \<not> \<turnstile> \<sim> (\<phi> \<sqinter> \<psi>)) \<or> (\<exists> \<phi> \<in> duplicates \<Phi>. \<not> \<turnstile> \<sim> \<phi>)"
      using exclusive_equivalence set_deduction_base_theory by blast
    hence "\<not> (\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> Pr \<psi>)"
    proof (elim disjE)
      assume "\<exists> \<phi> \<in> set \<Phi>. \<exists> \<chi> \<in> set \<Phi>. \<phi> \<noteq> \<chi> \<and> \<not> \<turnstile> \<sim> (\<phi> \<sqinter> \<chi>)"
      from this obtain \<phi> and \<chi> 
        where \<phi>\<chi>_properties: "\<phi> \<in> set \<Phi>" "\<chi> \<in> set \<Phi>" "\<phi> \<noteq> \<chi>" "\<not> \<turnstile> \<sim> (\<phi> \<sqinter> \<chi>)"
        by blast
      from this obtain \<Omega> where \<Omega>: "MCS \<Omega>" "\<sim> (\<phi> \<sqinter> \<chi>) \<notin> \<Omega>"
        by (meson insert_subset 
                Formula_Consistent_def 
                Formula_Maximal_Consistency 
                Formula_Maximally_Consistent_Extension 
                Formula_Maximally_Consistent_Set_def 
                set_deduction_base_theory 
                set_deduction_reflection 
                set_deduction_theorem)
      let ?Pr = "\<lambda> \<chi>. if \<chi>\<in>\<Omega> then (1 :: real) else 0"
      from \<Omega> have "\<phi> \<in> \<Omega>" "\<chi> \<in> \<Omega>"
         by (metis Formula_Maximally_Consistent_Set_implication 
                   Maximally_Consistent_Set_def 
                   conjunction_def 
                   negation_def)+
      with \<phi>\<chi>_properties have "(\<Sum>\<phi>\<leftarrow>[\<phi>, \<chi>]. ?Pr \<phi>) = 2" 
                              "set [\<phi>, \<chi>] \<subseteq> set \<Phi>" 
                              "distinct [\<phi>, \<chi>]" 
                              "\<forall>\<phi>. ?Pr \<phi> \<ge> 0" 
         by simp+
      hence "(\<Sum>\<phi>\<leftarrow>\<Phi>. ?Pr \<phi>) \<ge> 2" using sum_list_monotone by metis
      hence "\<not> (\<Sum>\<phi>\<leftarrow>\<Phi>. ?Pr \<phi>) \<le> ?Pr (\<psi>)" by auto
      thus ?thesis
        using \<Omega>(1) MCS_Binary_Probability
        by auto
    next
      assume "\<exists> \<phi> \<in> duplicates \<Phi>. \<not> \<turnstile> \<sim> \<phi>"
      from this obtain \<phi> where \<phi>: "\<phi> \<in> duplicates \<Phi>" "\<not> \<turnstile> \<sim> \<phi>"
        using exclusive_equivalence [where \<Gamma>="{}"] set_deduction_base_theory 
        by blast
      from \<phi> obtain \<Omega> where \<Omega>: "MCS \<Omega>" "\<sim> \<phi> \<notin> \<Omega>"
        by (meson insert_subset 
                  Formula_Consistent_def 
                  Formula_Maximal_Consistency 
                  Formula_Maximally_Consistent_Extension 
                  Formula_Maximally_Consistent_Set_def 
                  set_deduction_base_theory 
                  set_deduction_reflection 
                  set_deduction_theorem)
      hence "\<phi> \<in> \<Omega>"
        using negation_def by auto
      let ?Pr = "\<lambda> \<chi>. if \<chi>\<in>\<Omega> then (1 :: real) else 0"
      from \<phi> have "count_list \<Phi> \<phi> \<ge> 2" using duplicates_alt_def [where xs="\<Phi>"]
        by blast
      hence "real (count_list \<Phi> \<phi>) * ?Pr \<phi> \<ge> 2" using \<open>\<phi> \<in> \<Omega>\<close> by simp
      moreover
      {
        fix \<Psi>
        have "(\<Sum>\<phi>\<leftarrow>\<Psi>. ?Pr \<phi>) \<ge> 0" by (induct \<Psi>, simp, simp)
      }
      ultimately have "real (count_list \<Phi> \<phi>) * ?Pr \<phi> + (\<Sum> \<phi> \<leftarrow> (removeAll \<phi> \<Phi>). ?Pr \<phi>) \<ge> 2" by smt
      hence "(\<Sum>\<phi>\<leftarrow>\<Phi>. ?Pr \<phi>) \<ge> 2" by (metis count_remove_all_sum_list)
      hence "\<not> (\<Sum>\<phi>\<leftarrow>\<Phi>. ?Pr \<phi>) \<le> ?Pr (\<psi>)" by auto
      thus ?thesis
        using \<Omega>(1) MCS_Binary_Probability
        by auto
    qed
  }
  moreover
  {
    assume "\<not> \<turnstile> \<Squnion> \<Phi> \<rightarrow> \<psi>"
    from this obtain \<Omega> \<phi> where \<Omega>: "MCS \<Omega>" 
                            and \<psi>: "\<psi> \<notin> \<Omega>" 
                            and \<phi>: "\<phi> \<in> set \<Phi>" "\<phi> \<in> \<Omega>"
      by (meson insert_subset 
                Formula_Consistent_def 
                Formula_Maximal_Consistency 
                Formula_Maximally_Consistent_Extension 
                Formula_Maximally_Consistent_Set_def 
                arbitrary_disjunction_exclusion_MCS
                set_deduction_base_theory 
                set_deduction_reflection 
                set_deduction_theorem)
    let ?Pr = "\<lambda> \<chi>. if \<chi>\<in>\<Omega> then (1 :: real) else 0"
    from \<phi> have "(\<Sum>\<phi>\<leftarrow>\<Phi>. ?Pr \<phi>) \<ge> 1"
      by (induct \<Phi>, simp, simp, smt sum_list_0 sum_list_mono)
    hence "\<not> (\<Sum>\<phi>\<leftarrow>\<Phi>. ?Pr \<phi>) \<le> ?Pr (\<psi>)" using \<psi> by auto
    hence "\<not> (\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> Pr \<psi>)"
      using \<Omega>(1) MCS_Binary_Probability
      by auto
  }
  ultimately show 
    "\<turnstile> exclusive \<Phi> \<and>  \<turnstile> \<Squnion> \<Phi> \<rightarrow> \<psi> \<equiv> \<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> Pr \<psi>"
    by smt
qed
    
(* TODO: Weaken to Weak Probabilities *)    
theorem (in Classical_Propositional_Logic) Inquality_Completeness:
  "\<turnstile> \<phi> \<rightarrow> \<psi> \<equiv> \<forall> Pr \<in> Binary_Probabilities. Pr \<phi> \<le> Pr \<psi>"
proof -
  have "\<turnstile> exclusive [\<phi>]"
    by (simp add: conjunction_right_elimination negation_def verum_tautology)
  hence "\<turnstile> exclusive [\<phi>] \<and>  \<turnstile> \<Squnion> [\<phi>] \<rightarrow> \<psi> \<equiv> \<turnstile> \<phi> \<rightarrow> \<psi>"
    by (smt Arbitrary_Disjunction.simps(1) 
            Arbitrary_Disjunction.simps(2) 
            biconditional_weaken 
            disjunction_def 
            implication_equivalence 
            negation_def 
            set_deduction_base_theory)
  thus "\<turnstile> \<phi> \<rightarrow> \<psi> \<equiv> \<forall> Pr \<in> Binary_Probabilities. Pr \<phi> \<le> Pr \<psi>"
    using Exclusive_Implication_Completeness [where \<Phi>="[\<phi>]"] 
    by auto
qed

theorem (in Classical_Propositional_Logic) Exclusive_List_Summation_Completeness:
  "\<turnstile> exclusive \<Phi> \<equiv> \<forall> Pr \<in> Binary_Probabilities. Pr (\<Squnion> \<Phi>) = (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>)"
proof -
  have "\<turnstile> exclusive \<Phi> \<and> \<turnstile> \<Squnion> \<Phi> \<rightarrow> \<Squnion> \<Phi> \<equiv> \<turnstile> exclusive \<Phi>"
    by (simp add: Inquality_Completeness)
  hence "\<turnstile> exclusive \<Phi> \<equiv> \<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> Pr (\<Squnion> \<Phi>)"
    by (simp add: Exclusive_Implication_Completeness)
  moreover have "\<forall> Pr \<in> Binary_Probabilities. Pr (\<Squnion> \<Phi>) \<le> (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>)"
      using Inquality_Completeness List_Summation_Completeness by blast
  ultimately show "\<turnstile> exclusive \<Phi> \<equiv> \<forall> Pr \<in> Binary_Probabilities. Pr (\<Squnion> \<Phi>) = (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>)"
    by smt
qed

theorem (in Classical_Propositional_Logic) Exclusive_Set_Summation_Completeness:
  "\<turnstile> exclusive (remdups \<Phi>) \<equiv> \<forall> Pr \<in> Binary_Probabilities. Pr (\<Squnion> \<Phi>) = (\<Sum>\<phi> \<in> set \<Phi>. Pr \<phi>)"
  by (smt eq_iff 
          Exclusive_List_Summation_Completeness 
          Inquality_Completeness 
          arbitrary_disjunction_monotone 
          set_remdups 
          sum.set_conv_list)
  
lemma (in Probability) exclusive_list_set_inequality:
  assumes "\<turnstile> exclusive \<Phi>"
  shows "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) = (\<Sum>\<phi>\<in>set \<Phi>. Pr \<phi>)"
  by (smt assms 
          distinct_remdups 
          Non_Negative 
          arbitrary_disjunction_set_summation_inequality 
          exclusive_sum_list_identity 
          set_eq_subset 
          set_remdups 
          sum.set_conv_list 
          sum_list_monotone)

end