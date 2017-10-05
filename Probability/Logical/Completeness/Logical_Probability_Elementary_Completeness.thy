theory Logical_Probability_Elementary_Completeness
  imports "../Weakly_Additive/Weakly_Additive_Logical_Probability"
begin

sledgehammer_params [smt_proofs = false]
    
theorem (in Classical_Propositional_Logic) List_Summation_Completeness:
  "(\<forall> Pr \<in> Binary_Probabilities. Pr \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. Pr \<psi>)) = \<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
proof -
  {
    fix Pr :: "'a \<Rightarrow> real"
    assume "Pr \<in> Binary_Probabilities"
    from this interpret Weakly_Additive_Logical_Probability "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(op \<rightarrow>)" "\<bottom>" "Pr"
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
      using \<Omega>(1) MCS_Binary_Weakly_Additive_Logical_Probability by auto
  }
  ultimately show ?thesis by blast
qed

theorem (in Classical_Propositional_Logic) Set_Summation_Completeness:
  "(\<forall> Pr \<in> Binary_Probabilities. Pr \<phi> \<le> (\<Sum>\<psi>\<in> set \<Psi>. Pr \<psi>)) = \<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
  by (metis List_Summation_Completeness 
            Modus_Ponens 
            arbitrary_disjunction_remdups 
            biconditional_left_elimination 
            biconditional_right_elimination 
            hypothetical_syllogism 
            sum.set_conv_list)
 
lemma (in Weakly_Additive_Logical_Probability) exclusive_sum_list_identity:
  assumes "\<turnstile> \<Coprod> \<Phi>"
  shows "Pr (\<Squnion> \<Phi>) = (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>)"
  using assms
proof (induct \<Phi>)
  case Nil
  then show ?case by (simp add: falsum_zero_probability) 
next
  case (Cons \<phi> \<Phi>)
  assume "\<turnstile> \<Coprod> (\<phi> # \<Phi>)"
  hence "\<turnstile> \<sim> (\<phi> \<sqinter> \<Squnion> \<Phi>)" "\<turnstile> \<Coprod> \<Phi>" by simp+
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
          moreover have "f \<psi> \<ge> 0" using \<open>\<forall> x. f x \<ge> 0\<close> by metis
          ultimately have ?thesis by simp 
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
  by (induct xs, simp, simp,
      metis (no_types, hide_lams)
            semiring_normalization_rules(3)
            add.commute
            add.left_commute)

theorem (in Classical_Propositional_Logic) Exclusive_Implication_Completeness:
  "(\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> Pr \<psi>) = (\<turnstile> \<Coprod> \<Phi> \<and>  \<turnstile> \<Squnion> \<Phi> \<rightarrow> \<psi>)"
proof -
  {
    fix Pr
    assume "Pr \<in> Binary_Probabilities"
    from this interpret Weakly_Additive_Logical_Probability "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(op \<rightarrow>)" "\<bottom>" "Pr"
      unfolding Binary_Probabilities_def
      by simp
    assume "\<turnstile> \<Coprod> \<Phi>" "\<turnstile> \<Squnion> \<Phi> \<rightarrow> \<psi>"
    hence "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> Pr \<psi>"
      using exclusive_sum_list_identity monotonicity by fastforce
  }
  moreover
  {
    assume "\<not> \<turnstile> \<Coprod> \<Phi>"
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
        using \<Omega>(1) MCS_Binary_Weakly_Additive_Logical_Probability
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
      moreover have "(0::real) \<le> (\<Sum>a\<leftarrow>removeAll \<phi> \<Phi>. if a \<in> \<Omega> then 1 else 0)"
          using \<open>\<And>\<Psi>. 0 \<le> (\<Sum>\<phi>\<leftarrow>\<Psi>. if \<phi> \<in> \<Omega> then 1 else 0)\<close> by presburger
      ultimately have "real (count_list \<Phi> \<phi>) * ?Pr \<phi> + (\<Sum> \<phi> \<leftarrow> (removeAll \<phi> \<Phi>). ?Pr \<phi>) \<ge> 2"
          using \<open>2 \<le> real (count_list \<Phi> \<phi>) * (if \<phi> \<in> \<Omega> then 1 else 0)\<close> by linarith
      hence "(\<Sum>\<phi>\<leftarrow>\<Phi>. ?Pr \<phi>) \<ge> 2" by (metis count_remove_all_sum_list)
      hence "\<not> (\<Sum>\<phi>\<leftarrow>\<Phi>. ?Pr \<phi>) \<le> ?Pr (\<psi>)" by auto
      thus ?thesis
        using \<Omega>(1) MCS_Binary_Weakly_Additive_Logical_Probability
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
    proof (induct \<Phi>)
      case Nil
      then show ?case by simp
    next
      case (Cons \<phi>' \<Phi>)
      obtain f :: "real list \<Rightarrow> real" where f: 
        "\<forall>rs. f rs \<in> set rs \<and> \<not> 0 \<le> f rs \<or> 0 \<le> sum_list rs"
        using sum_list_nonneg by moura
      moreover have "f (map ?Pr \<Phi>) \<notin> set (map ?Pr \<Phi>) \<or> 0 \<le> f (map ?Pr \<Phi>)"
        by fastforce
      ultimately show ?case
        by (simp, metis Cons.hyps Cons.prems(1) \<phi>(2) set_ConsD)
    qed
    hence "\<not> (\<Sum>\<phi>\<leftarrow>\<Phi>. ?Pr \<phi>) \<le> ?Pr (\<psi>)" using \<psi> by auto
    hence "\<not> (\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> Pr \<psi>)"
      using \<Omega>(1) MCS_Binary_Weakly_Additive_Logical_Probability
      by auto
  }
  ultimately show ?thesis by blast
qed

theorem (in Classical_Propositional_Logic) Inequality_Completeness:
  "(\<forall> Pr \<in> Binary_Probabilities. Pr \<phi> \<le> Pr \<psi>) = \<turnstile> \<phi> \<rightarrow> \<psi>"
proof -
  have "\<turnstile> \<Coprod> [\<phi>]"
    by (simp add: conjunction_right_elimination negation_def)
  hence "(\<turnstile> \<Coprod> [\<phi>] \<and>  \<turnstile> \<Squnion> [\<phi>] \<rightarrow> \<psi>) = \<turnstile> \<phi> \<rightarrow> \<psi>"
    by (metis Arbitrary_Disjunction.simps(1) 
              Arbitrary_Disjunction.simps(2) 
              disjunction_def implication_equivalence 
              negation_def 
              weak_biconditional_weaken)
  thus ?thesis
    using Exclusive_Implication_Completeness [where \<Phi>="[\<phi>]"] 
    by auto
qed

theorem (in Classical_Propositional_Logic) Exclusive_List_Summation_Completeness:
  "(\<forall> Pr \<in> Binary_Probabilities. Pr (\<Squnion> \<Phi>) = (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>)) = \<turnstile> \<Coprod> \<Phi>"
proof -
  have "\<turnstile> \<Coprod> \<Phi> \<and> \<turnstile> \<Squnion> \<Phi> \<rightarrow> \<Squnion> \<Phi> \<equiv> \<turnstile> \<Coprod> \<Phi>"
    by (simp add: trivial_implication)
  hence "\<turnstile> \<Coprod> \<Phi> \<equiv> \<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> Pr (\<Squnion> \<Phi>)"
    by (simp add: Exclusive_Implication_Completeness)
  moreover have "\<forall> Pr \<in> Binary_Probabilities. Pr (\<Squnion> \<Phi>) \<le> (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>)"
    using Inequality_Completeness List_Summation_Completeness by blast
  ultimately show ?thesis
    by fastforce  
qed

theorem (in Classical_Propositional_Logic) Exclusive_Set_Summation_Completeness:
  "(\<forall> Pr \<in> Binary_Probabilities. Pr (\<Squnion> \<Phi>) = (\<Sum>\<phi> \<in> set \<Phi>. Pr \<phi>)) = \<turnstile> \<Coprod> (remdups \<Phi>)"
  by (metis (mono_tags, hide_lams) 
            eq_iff 
            Exclusive_Implication_Completeness 
            Set_Summation_Completeness 
            trivial_implication 
            set_remdups 
            sum.set_conv_list)
  
lemma (in Weakly_Additive_Logical_Probability) exclusive_list_set_inequality:
  assumes "\<turnstile> \<Coprod> \<Phi>"
  shows "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) = (\<Sum>\<phi>\<in>set \<Phi>. Pr \<phi>)"
proof -
  have "distinct (remdups \<Phi>)" using distinct_remdups by auto
  hence "duplicates (remdups \<Phi>) = {}"
    by (induct "\<Phi>", simp+)
  moreover have "set (remdups \<Phi>) = set \<Phi>"
    by (induct "\<Phi>", simp, simp add: insert_absorb)
  moreover have "(\<forall>\<phi>\<in>duplicates \<Phi>. \<turnstile> \<sim> \<phi>) 
               \<and> (\<forall> \<phi> \<in> set \<Phi>. \<forall> \<psi> \<in> set \<Phi>. (\<phi> \<noteq> \<psi>) \<longrightarrow> \<turnstile> \<sim> (\<phi> \<sqinter> \<psi>))"
    using assms
          exclusive_elimination1
          exclusive_elimination2
          set_deduction_base_theory 
    by blast
  ultimately have 
    "(\<forall>\<phi>\<in>duplicates (remdups \<Phi>). \<turnstile> \<sim> \<phi>) 
   \<and> (\<forall> \<phi> \<in> set (remdups \<Phi>). \<forall> \<psi> \<in> set (remdups \<Phi>). (\<phi> \<noteq> \<psi>) \<longrightarrow> \<turnstile> \<sim> (\<phi> \<sqinter> \<psi>))"
    by auto
  hence "\<turnstile> \<Coprod> (remdups \<Phi>)"
    by (meson exclusive_equivalence set_deduction_base_theory)
  hence "(\<Sum>\<phi>\<in>set \<Phi>. Pr \<phi>) = Pr (\<Squnion> \<Phi>)"
    by (metis arbitrary_disjunction_remdups 
              biconditional_equivalence 
              exclusive_sum_list_identity 
              sum.set_conv_list)
  moreover have "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) = Pr (\<Squnion> \<Phi>)"
    by (simp add: assms exclusive_sum_list_identity)
  ultimately show ?thesis by metis
qed

end
