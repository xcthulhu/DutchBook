section {* Boolean Propositional Logic *}
  
theory Boolean_Propositional_Logic
  imports Minimal_Logic
begin

text {* This theory presents \emph{boolean propositional logic}, which is 
        a classical logic without quantifiers. *}

subsection {* Axiomatization *}

text {* Minimal logic is given by the following Hilbert-style axiom system: *}
  
class Boolean_Propositional_Logic = Minimal_Logic_With_Falsum +
  assumes Double_Negation: "\<turnstile> ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>) \<rightarrow> \<phi>"

subsection {* Common Rules *}

lemma (in Boolean_Propositional_Logic) Ex_Falso_Quodlibet: "\<turnstile> \<bottom> \<rightarrow> \<phi>"
  using Axiom_1 Double_Negation Modus_Ponens hypothetical_syllogism by blast

lemma (in Boolean_Propositional_Logic) Contraposition:
  "\<turnstile> ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> (\<psi> \<rightarrow> \<bottom>)) \<rightarrow> \<psi> \<rightarrow> \<phi>"
proof -
  have "[\<phi> \<rightarrow> \<bottom>, \<psi>, (\<phi> \<rightarrow> \<bottom>) \<rightarrow> (\<psi> \<rightarrow> \<bottom>)] :\<turnstile> \<bottom>"
    using flip_implication list_deduction_theorem list_implication.simps(1)
    unfolding list_deduction_def
    by presburger
  hence "[\<psi>, (\<phi> \<rightarrow> \<bottom>) \<rightarrow> (\<psi> \<rightarrow> \<bottom>)] :\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>"
    using list_deduction_theorem by blast
  hence "[\<psi>, (\<phi> \<rightarrow> \<bottom>) \<rightarrow> (\<psi> \<rightarrow> \<bottom>)] :\<turnstile> \<phi>" 
    using Double_Negation list_deduction_weaken list_deduction_modus_ponens
    by blast
  thus ?thesis
    using list_deduction_base_theory list_deduction_theorem by blast
qed

lemma (in Boolean_Propositional_Logic) Double_Negation_converse: "\<turnstile> \<phi> \<rightarrow> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>"
  by (meson Axiom_1 Modus_Ponens flip_implication)
  
lemma (in Boolean_Propositional_Logic) The_Principle_of_Pseudo_Scotus: "\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<phi> \<rightarrow> \<psi>"
  using Ex_Falso_Quodlibet Modus_Ponens hypothetical_syllogism by blast
    
lemma (in Boolean_Propositional_Logic) Peirces_law: "\<turnstile> ((\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>) \<rightarrow> \<phi>"
proof -
  have "[\<phi> \<rightarrow> \<bottom>, (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>] :\<turnstile> \<phi> \<rightarrow> \<psi>"
    using The_Principle_of_Pseudo_Scotus list_deduction_theorem list_deduction_weaken by blast
  hence "[\<phi> \<rightarrow> \<bottom>, (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>] :\<turnstile> \<phi>"
    by (meson list.set_intros(1) 
              list_deduction_reflection 
              list_deduction_modus_ponens 
              set_subset_Cons 
              subsetCE)
  hence "[\<phi> \<rightarrow> \<bottom>, (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>] :\<turnstile> \<bottom>"
    by (meson list.set_intros(1) list_deduction_modus_ponens list_deduction_reflection)
  hence "[(\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>] :\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>"
    using list_deduction_theorem by blast
  hence "[(\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>] :\<turnstile> \<phi>"
    using Double_Negation list_deduction_modus_ponens list_deduction_weaken by blast
  thus ?thesis
    using list_deduction_def
    by auto
qed

lemma (in Boolean_Propositional_Logic) excluded_middle_elimination:
  "\<turnstile> (\<phi> \<rightarrow> \<psi>) \<rightarrow> ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>) \<rightarrow> \<psi>"
proof -
  let ?\<Gamma> = "[\<psi> \<rightarrow> \<bottom>, \<phi> \<rightarrow> \<psi>, (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>]"
  have "?\<Gamma> :\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>"
       "?\<Gamma> :\<turnstile> \<psi> \<rightarrow> \<bottom>"
    by (simp add: list_deduction_reflection)+
  hence "?\<Gamma> :\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>"
    by (meson flip_hypothetical_syllogism 
              list_deduction_base_theory 
              list_deduction_monotonic 
              list_deduction_theorem 
              set_subset_Cons)
  hence "?\<Gamma> :\<turnstile> \<phi>"
    using Double_Negation 
          list_deduction_modus_ponens 
          list_deduction_weaken 
    by blast
  hence "?\<Gamma> :\<turnstile> \<psi>"
    by (meson list.set_intros(1) 
              list_deduction_modus_ponens 
              list_deduction_reflection 
              set_subset_Cons subsetCE)
  hence "[\<phi> \<rightarrow> \<psi>, (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>] :\<turnstile> \<psi>"
    using Peirces_law 
          list_deduction_modus_ponens 
          list_deduction_theorem 
          list_deduction_weaken 
    by blast
  thus ?thesis
    unfolding list_deduction_def
    by simp   
qed
          
subsection {* Maximally Consistent Sets *}

definition (in Minimal_Logic) 
  Formula_Consistent :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" ("_-Consistent _" [100] 100) where 
    [simp]: "\<phi>-Consistent \<Gamma> \<equiv> ~ (\<Gamma> \<tturnstile> \<phi>)"    
    
lemma (in Minimal_Logic) Formula_Consistent_Extension:
  assumes "\<phi>-Consistent \<Gamma>" 
  shows "(\<phi>-Consistent insert \<psi> \<Gamma>) \<or> (\<phi>-Consistent insert (\<psi> \<rightarrow> \<phi>) \<Gamma>)"
proof -
  {
    assume "~ \<phi>-Consistent insert \<psi> \<Gamma>"
    hence "\<Gamma> \<tturnstile> \<psi> \<rightarrow> \<phi>" 
      using set_deduction_theorem 
      unfolding Formula_Consistent_def
      by simp
    hence "\<phi>-Consistent insert (\<psi> \<rightarrow> \<phi>) \<Gamma>"
     by (smt Un_absorb assms Formula_Consistent_def set_deduction_cut_rule)
  }
  thus ?thesis by blast
qed

definition (in Minimal_Logic) 
  Formula_Maximally_Consistent_Set :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" ("_-MCS _" [100] 100) where
   [simp]: "\<phi>-MCS \<Gamma> \<equiv> (\<phi>-Consistent \<Gamma>) \<and> (\<forall> \<psi>. \<psi> \<in> \<Gamma> \<or> (\<psi> \<rightarrow> \<phi>) \<in> \<Gamma>)"
  
theorem (in Minimal_Logic) Formula_Maximally_Consistent_Extension:
  assumes "\<phi>-Consistent \<Gamma>" 
  shows "\<exists> \<Omega>. (\<phi>-MCS \<Omega>) \<and> \<Gamma> \<subseteq> \<Omega>"
proof -
  let ?\<Gamma>_Extensions = "{\<Sigma>. (\<phi>-Consistent \<Sigma>) \<and> \<Gamma> \<subseteq> \<Sigma>}"
  have "\<exists> \<Omega> \<in> ?\<Gamma>_Extensions. \<forall>\<Sigma> \<in> ?\<Gamma>_Extensions. \<Omega> \<subseteq> \<Sigma> \<longrightarrow> \<Sigma> = \<Omega>"
  proof (rule subset_Zorn)
    fix \<C> :: "'a set set" 
    assume subset_chain_\<C>: "subset.chain ?\<Gamma>_Extensions \<C>"
    hence \<C>:  "\<forall> \<Sigma> \<in> \<C>. \<Gamma> \<subseteq> \<Sigma>" "\<forall> \<Sigma> \<in> \<C>. \<phi>-Consistent \<Sigma>"
      unfolding subset.chain_def by blast+
    show "\<exists> \<Omega> \<in> ?\<Gamma>_Extensions. \<forall> \<Sigma> \<in> \<C>. \<Sigma> \<subseteq> \<Omega>"
    proof cases
      assume "\<C> = {}" thus ?thesis using assms by blast
    next
      let ?\<Omega> = "\<Union> \<C>"
      assume "\<C> \<noteq> {}"
      hence "\<Gamma> \<subseteq> ?\<Omega>" by (simp add: \<C>(1) less_eq_Sup)
      moreover have "\<phi>-Consistent ?\<Omega>"
      proof -
        {
          assume "~ \<phi>-Consistent ?\<Omega>"
          then obtain \<omega> where \<omega>: "finite \<omega>" "\<omega> \<subseteq> ?\<Omega>" "~ \<phi>-Consistent \<omega>"
            unfolding Formula_Consistent_def 
                      set_deduction_def 
            by auto
          from \<omega>(1) \<omega>(2) have "\<exists> \<Sigma> \<in> \<C>. \<omega> \<subseteq> \<Sigma>" 
          proof (induct \<omega> rule: finite_induct)
            case empty thus ?case using \<open>\<C> \<noteq> {}\<close> by blast 
          next
            case (insert \<psi> \<omega>)
            from this obtain \<Sigma>\<^sub>1 \<Sigma>\<^sub>2 where 
              \<Sigma>\<^sub>1: "\<omega> \<subseteq> \<Sigma>\<^sub>1" "\<Sigma>\<^sub>1 \<in> \<C>" and 
              \<Sigma>\<^sub>2: "\<psi> \<in> \<Sigma>\<^sub>2" "\<Sigma>\<^sub>2 \<in> \<C>"
              by auto
            hence "\<Sigma>\<^sub>1 \<subseteq> \<Sigma>\<^sub>2 \<or> \<Sigma>\<^sub>2 \<subseteq> \<Sigma>\<^sub>1" 
              using subset_chain_\<C> 
              unfolding subset.chain_def
              by blast
            hence "(insert \<psi> \<omega>) \<subseteq> \<Sigma>\<^sub>1 \<or> (insert \<psi> \<omega>) \<subseteq> \<Sigma>\<^sub>2" using \<Sigma>\<^sub>1 \<Sigma>\<^sub>2 by blast
            thus ?case using \<Sigma>\<^sub>1 \<Sigma>\<^sub>2 by blast
          qed
          hence "\<exists> \<Sigma> \<in> \<C>. (\<phi>-Consistent \<Sigma>) \<and> ~ (\<phi>-Consistent \<Sigma>)" 
            using \<C>(2) \<omega>(3)
            unfolding Formula_Consistent_def 
                      set_deduction_def
            by auto
          hence "False" by auto
        } 
        thus ?thesis by blast
      qed
      ultimately show ?thesis by blast
    qed
  qed
  then obtain \<Omega> where \<Omega>: "\<Omega> \<in> ?\<Gamma>_Extensions" 
                          "\<forall>\<Sigma> \<in> ?\<Gamma>_Extensions. \<Omega> \<subseteq> \<Sigma> \<longrightarrow> \<Sigma> = \<Omega>" by auto+ 
  {
    fix \<psi>
    have "(\<phi>-Consistent insert \<psi> \<Omega>) \<or> (\<phi>-Consistent insert (\<psi> \<rightarrow> \<phi>) \<Omega>)"
         "\<Gamma> \<subseteq> insert \<psi> \<Omega>"
         "\<Gamma> \<subseteq> insert (\<psi> \<rightarrow> \<phi>) \<Omega>"
      using \<Omega>(1) Formula_Consistent_Extension Formula_Consistent_def by auto
    hence "insert \<psi> \<Omega> \<in> ?\<Gamma>_Extensions \<or> insert (\<psi> \<rightarrow> \<phi>) \<Omega> \<in> ?\<Gamma>_Extensions" by blast
    hence "\<psi> \<in> \<Omega> \<or> (\<psi> \<rightarrow> \<phi>) \<in> \<Omega>" using \<Omega>(2) by blast
  }
  thus ?thesis using \<Omega>(1) unfolding Formula_Maximally_Consistent_Set_def by blast
qed

lemma (in Minimal_Logic) Formula_Maximally_Consistent_Set_reflection:
  "\<phi>-MCS \<Gamma> \<Longrightarrow> \<psi> \<in> \<Gamma> \<equiv> \<Gamma> \<tturnstile> \<psi>"
proof -
  assume "\<phi>-MCS \<Gamma>"
  {
    assume "\<Gamma> \<tturnstile> \<psi>"
    moreover from \<open>\<phi>-MCS \<Gamma>\<close> have "\<psi> \<in> \<Gamma> \<or> (\<psi> \<rightarrow> \<phi>) \<in> \<Gamma>" "~ \<Gamma> \<tturnstile> \<phi>" 
      unfolding Formula_Maximally_Consistent_Set_def Formula_Consistent_def 
      by auto
    ultimately have "\<psi> \<in> \<Gamma>" 
      using set_deduction_reflection set_deduction_modus_ponens
      by smt
  }
  thus "\<psi> \<in> \<Gamma> \<equiv> \<Gamma> \<tturnstile> \<psi>"
    using set_deduction_reflection
    by smt
qed
  
definition (in Boolean_Propositional_Logic) 
  Consistent :: "'a set \<Rightarrow> bool" where 
    [simp]: "Consistent \<Gamma> \<equiv> \<bottom>-Consistent \<Gamma>"  
  
definition (in Boolean_Propositional_Logic) 
  Maximally_Consistent_Set :: "'a set \<Rightarrow> bool" ("MCS") where
    [simp]: "MCS \<Gamma> \<equiv> \<bottom>-MCS \<Gamma>"

lemma (in Boolean_Propositional_Logic) Formula_Maximal_Consistent_Set_negation:
  "\<phi>-MCS \<Gamma> \<Longrightarrow> \<phi> \<rightarrow> \<bottom> \<in> \<Gamma>"
proof -
  assume "\<phi>-MCS \<Gamma>"
  {
    assume "\<phi> \<rightarrow> \<bottom> \<notin> \<Gamma>"
    hence "(\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<phi> \<in> \<Gamma>"
      using \<open>\<phi>-MCS \<Gamma>\<close>
      unfolding Formula_Maximally_Consistent_Set_def
      by blast
    hence "\<Gamma> \<tturnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<phi>"
      using set_deduction_reflection
      by simp
    hence "\<Gamma> \<tturnstile> \<phi>"
      using Peirces_law 
            set_deduction_modus_ponens 
            set_deduction_weaken
         by smt
    hence "False" 
      using \<open>\<phi>-MCS \<Gamma>\<close>
      unfolding Formula_Maximally_Consistent_Set_def
                Formula_Consistent_def
      by simp
  }
  thus ?thesis by blast
qed
  
lemma (in Boolean_Propositional_Logic) Formula_Maximal_Consistency:
  "\<exists>\<phi>. \<phi>-MCS \<Gamma> \<equiv> MCS \<Gamma>"
proof -
  {
    fix \<phi>
    have "\<phi>-MCS \<Gamma> \<Longrightarrow> MCS \<Gamma>"
    proof -
      assume "\<phi>-MCS \<Gamma>"
      have "Consistent \<Gamma>"
        using \<open>\<phi>-MCS \<Gamma>\<close>
              Ex_Falso_Quodlibet [where \<phi>="\<phi>"]
              set_deduction_weaken [where \<Gamma>="\<Gamma>"]
              set_deduction_modus_ponens 
        unfolding Formula_Maximally_Consistent_Set_def
                  Consistent_def
                  Formula_Consistent_def
        by smt
      moreover {
        fix \<psi>
        have "\<psi> \<rightarrow> \<bottom> \<notin> \<Gamma> \<Longrightarrow> \<psi> \<in> \<Gamma>"
        proof -
          assume "\<psi> \<rightarrow> \<bottom> \<notin> \<Gamma>"
          hence "(\<psi> \<rightarrow> \<bottom>) \<rightarrow> \<phi> \<in> \<Gamma>"
            using \<open>\<phi>-MCS \<Gamma>\<close> 
            unfolding Formula_Maximally_Consistent_Set_def 
            by blast
          hence "\<Gamma> \<tturnstile> (\<psi> \<rightarrow> \<bottom>) \<rightarrow> \<phi>"
            using set_deduction_reflection
            by simp
          also have "\<Gamma> \<tturnstile> \<phi> \<rightarrow> \<bottom>"
            using \<open>\<phi>-MCS \<Gamma>\<close> 
                  Formula_Maximal_Consistent_Set_negation
                  set_deduction_reflection
            by simp
          hence "\<Gamma> \<tturnstile> (\<psi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>"
            using calculation
                  hypothetical_syllogism [where \<phi>="\<psi> \<rightarrow> \<bottom>" and \<psi>="\<phi>" and \<chi>="\<bottom>"]
                  set_deduction_weaken [where \<Gamma>="\<Gamma>"]
                  set_deduction_modus_ponens
            by smt
          hence "\<Gamma> \<tturnstile> \<psi>"
            using Double_Negation [where \<phi>="\<psi>"]
                  set_deduction_weaken [where \<Gamma>="\<Gamma>"]
                  set_deduction_modus_ponens
            by smt
          thus ?thesis
            using \<open>\<phi>-MCS \<Gamma>\<close>
                  Formula_Maximally_Consistent_Set_reflection
            by blast
       qed
      }
      ultimately show ?thesis 
        unfolding Maximally_Consistent_Set_def 
                  Formula_Maximally_Consistent_Set_def
                  Formula_Consistent_def
                  Consistent_def
        by blast
    qed
  }
  thus "\<exists>\<phi>. \<phi>-MCS \<Gamma> \<equiv> MCS \<Gamma>"
    unfolding Maximally_Consistent_Set_def
    by smt
qed

theorem (in Minimal_Logic) Formula_Maximally_Consistent_Set_implication_elimination:
  assumes "\<phi>-MCS \<Omega>"
  shows "(\<psi> \<rightarrow> \<chi>) \<in> \<Omega> \<Longrightarrow> \<psi> \<in> \<Omega> \<longrightarrow> \<chi> \<in> \<Omega>"
  using assms 
        Formula_Maximally_Consistent_Set_reflection 
        set_deduction_modus_ponens 
  by blast  
  
lemma (in Boolean_Propositional_Logic) Formula_Maximally_Consistent_Set_implication:
  assumes "\<phi>-MCS \<Gamma>"
  shows "\<psi> \<rightarrow> \<chi> \<in> \<Gamma> \<equiv> (\<psi> \<in> \<Gamma> \<longrightarrow> \<chi> \<in> \<Gamma>)"
proof -
  {
    assume hypothesis: "\<psi> \<in> \<Gamma> \<longrightarrow> \<chi> \<in> \<Gamma>"
    {
      assume "\<psi> \<notin> \<Gamma>" 
      hence "\<psi> \<rightarrow> \<chi> \<in> \<Gamma>"
        by (meson assms 
                  Formula_Maximal_Consistency 
                  Formula_Maximally_Consistent_Set_def 
                  Formula_Maximally_Consistent_Set_implication_elimination 
                  Formula_Maximally_Consistent_Set_reflection 
                  Maximally_Consistent_Set_def 
                  The_Principle_of_Pseudo_Scotus 
                  set_deduction_weaken)
    }
    moreover { 
      assume "\<chi> \<in> \<Gamma>"
      hence "\<psi> \<rightarrow> \<chi> \<in> \<Gamma>"
        by (metis assms 
                  calculation 
                  insert_absorb 
                  Formula_Maximally_Consistent_Set_reflection
                  set_deduction_theorem)
    }
    ultimately have  "\<psi> \<rightarrow> \<chi> \<in> \<Gamma>" using hypothesis by blast
  }
  thus "\<psi> \<rightarrow> \<chi> \<in> \<Gamma> \<equiv> (\<psi> \<in> \<Gamma> \<longrightarrow> \<chi> \<in> \<Gamma>)"
    using assms
          Formula_Maximally_Consistent_Set_implication_elimination
    by smt
qed
  
end
