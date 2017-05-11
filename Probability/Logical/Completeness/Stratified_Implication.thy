theory Stratified_Implication
  imports Logical_Probability_Elementary_Completeness
          "~~/src/HOL/Library/Permutation"
begin      
        
definition (in Classical_Propositional_Logic) 
  stratified :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list list \<Rightarrow> bool" 
  where
    "stratified n \<phi> \<Phi> \<L> \<equiv> 
        n \<noteq> 0 \<longrightarrow> length \<L> = n \<and> concat \<L> <~~> \<Phi> \<and> (\<forall> \<Psi> \<in> set \<L>. \<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>)"
    
lemma (in Classical_Propositional_Logic) implicational_concatenation:
  assumes "set \<L> \<noteq> {}"
  and     "\<forall> \<Psi> \<in> set \<L>. \<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
  shows   "\<turnstile> \<phi> \<rightarrow> \<Squnion> (concat \<L>)"
  using assms
proof (induct \<L>)
  case Nil
  then show ?case 
    by simp 
next
  case (Cons \<Psi> \<L>)
  assume "\<forall>\<Psi>'\<in>set (\<Psi> # \<L>). \<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>'"
  hence "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>" by simp
  thus ?case
  proof cases
    assume "set \<L> = {}"
    hence "concat (\<Psi> # \<L>) = \<Psi>" by simp
    with \<open>\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>\<close> show ?thesis by smt
  next
    assume "set \<L> \<noteq> {}"
    hence "\<turnstile> \<phi> \<rightarrow> \<Squnion> (concat \<L>)"
      using \<open>\<forall>\<Psi>'\<in>set (\<Psi> # \<L>). \<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>'\<close> Cons.hyps
      by simp
    hence "\<turnstile> \<phi> \<rightarrow> (\<Squnion> \<Psi> \<squnion> \<Squnion> (concat \<L>))"
      unfolding disjunction_def
      using \<open>\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>\<close> Axiom_1 Modus_Ponens flip_implication 
      by blast
    moreover have "\<turnstile> (\<Squnion> \<Psi> \<squnion> \<Squnion> (concat \<L>)) \<leftrightarrow> \<Squnion> (concat (\<Psi> # \<L>))"
    proof (induct \<Psi>)
      case Nil
      then show ?case 
        unfolding biconditional_def 
        using Axiom_1 Ex_Falso_Quodlibet Modus_Ponens excluded_middle_elimination 
        by (simp add: disjunction_def, blast)
    next
      case (Cons \<psi> \<Psi>)
      have " \<turnstile> ((\<Squnion> \<Psi> \<squnion> \<Squnion> (concat \<L>)) \<leftrightarrow> \<Squnion> (\<Psi> @ concat \<L>)) \<rightarrow> 
               (((\<psi> \<squnion> \<Squnion> \<Psi>) \<squnion> \<Squnion> (concat \<L>)) \<leftrightarrow> (\<psi> \<squnion> \<Squnion> (\<Psi> @ concat \<L>)))"
      proof -
        have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ((\<^bold>\<langle>\<Squnion> \<Psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (concat \<L>)\<^bold>\<rangle>) \<leftrightarrow> \<^bold>\<langle>\<Squnion> (\<Psi> @ concat \<L>)\<^bold>\<rangle>) \<rightarrow> 
                            (((\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Psi>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>\<Squnion> (concat \<L>)\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (\<Psi> @ concat \<L>)\<^bold>\<rangle>))"
          by simp
        hence "\<turnstile> \<^bold>\<lparr> ((\<^bold>\<langle>\<Squnion> \<Psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (concat \<L>)\<^bold>\<rangle>) \<leftrightarrow> \<^bold>\<langle>\<Squnion> (\<Psi> @ concat \<L>)\<^bold>\<rangle>) \<rightarrow> 
                   (((\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Psi>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>\<Squnion> (concat \<L>)\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (\<Psi> @ concat \<L>)\<^bold>\<rangle>)) \<^bold>\<rparr>"
          using propositional_semantics by blast
        thus ?thesis by simp
      qed
      thus ?case
        using Cons.hyps Modus_Ponens
        by simp
    qed
    ultimately show ?thesis
      unfolding biconditional_def
      using Inquality_Completeness 
      by fastforce        
  qed
qed
  
lemma (in Classical_Propositional_Logic) stratified_\<Phi>_implication:
  assumes "stratified n \<phi> \<Phi> \<L>"
  and     "set \<Phi> \<noteq> {}"
  and     "n \<noteq> 0"
  shows   "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Phi>"
  using assms 
        implicational_concatenation [where \<L>="\<L>" and \<phi>="\<phi>"]
        Set_Summation_Completeness
        perm_set_eq
  unfolding stratified_def
  by fastforce
    
lemma (in Classical_Propositional_Logic) stratified_listSubtraction:
  assumes "stratified n \<phi> \<Phi> \<L>"
      and "\<Psi> \<in> set \<L>"
      and "n \<noteq> 0"
    shows "stratified (n-1) \<phi> (\<Phi> \<ominus> \<Psi>) (\<L> \<ominus> [\<Psi>])"
proof -
  from assms listSubtract_concat listSubtract_permute 
  have "concat (\<L> \<ominus> [\<Psi>]) <~~> \<Phi> \<ominus> \<Psi>"
    unfolding stratified_def by blast
  moreover from assms have "\<Psi> \<in> set \<L>"
    unfolding stratified_def by simp
  hence "\<forall>n. length \<L> = n \<longrightarrow> length (\<L> \<ominus> [\<Psi>]) = n - 1"
  proof (induct \<L>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<Lambda> \<L>)
    assume "\<Psi> \<in> set (\<Lambda> # \<L>)"
    show "\<forall>n. length (\<Lambda> # \<L>) = n \<longrightarrow> length ((\<Lambda> # \<L>) \<ominus> [\<Psi>]) = n - 1"
      by (cases "\<Lambda> = \<Psi>", 
            simp, 
            metis Cons.prems length_remove1 listSubtract.simps(1) listSubtract.simps(2))
  qed
  hence "length (\<L> \<ominus> [\<Psi>]) = n - 1"
    using assms
    unfolding stratified_def
    by fastforce
  moreover have "\<forall>\<Psi>\<in>set (\<L> \<ominus> [\<Psi>]). \<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
    using assms 
    unfolding stratified_def by auto
  ultimately show ?thesis
    unfolding stratified_def
    by auto
qed
  
lemma (in Weakly_Additive_Logical_Probability) stratified_summation:
  assumes "stratified n \<phi> \<Phi> \<L>"
  shows "(real n) * Pr \<phi> \<le> (\<Sum>\<phi>'\<leftarrow>\<Phi>. Pr \<phi>')"
proof -
  have "\<forall> m \<Phi> \<L>. m \<le> n \<longrightarrow> stratified m \<phi> \<Phi> \<L> \<longrightarrow> (real m) * Pr \<phi> \<le> (\<Sum>\<phi>'\<leftarrow>\<Phi>. Pr \<phi>')"
  proof (induct n)
    case 0
    then show ?case
      using Ex_Falso_Quodlibet 
            falsum_zero_probability 
            implication_list_summation_inequality 
      by fastforce 
  next
    case (Suc n)
    {
      fix m
      fix \<Phi>
      fix \<L>
      assume hypothesis: "m = n + 1"
                         "stratified m \<phi> \<Phi> \<L>"
      from this obtain \<Psi> \<L>' where \<Psi>: "\<L> = \<Psi> # \<L>'"
        unfolding stratified_def
        by (metis Suc_eq_plus1 
                  Suc_le_mono 
                  impossible_Cons 
                  length_Cons 
                  list.exhaust 
                  list.size(3) 
                  zero_le)
      hence "stratified n \<phi> (\<Phi> \<ominus> \<Psi>) (\<L> \<ominus> [\<Psi>])"
        using hypothesis stratified_listSubtraction
        by fastforce
      with \<Psi> have "stratified n \<phi> (\<Phi> \<ominus> \<Psi>) \<L>'"
        by simp
      hence "(real n) * Pr \<phi> \<le> (\<Sum>\<phi>'\<leftarrow>(\<Phi> \<ominus> \<Psi>). Pr \<phi>')"
        using Suc.hyps by blast
      moreover
      have "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
        using \<Psi> hypothesis stratified_def by auto
      hence "Pr \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. Pr \<psi>)"
        by (simp add: implication_list_summation_inequality)
      ultimately have 
        "(real (n+1)) * Pr \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. Pr \<psi>) + (\<Sum>\<phi>'\<leftarrow>(\<Phi> \<ominus> \<Psi>). Pr \<phi>')"
        by (smt of_nat_1 of_nat_add semiring_normalization_rules(3))
      moreover
      have "\<Phi> <~~> \<Psi> @ concat \<L>'"
        using \<Psi> hypothesis stratified_def perm_sym by fastforce
      hence "mset \<Psi> \<subseteq># mset \<Phi>"
        using mset_le_perm_append perm_sym by blast
      hence "(\<Sum>\<psi>\<leftarrow>\<Psi>. Pr \<psi>) + (\<Sum>\<phi>'\<leftarrow>(\<Phi> \<ominus> \<Psi>). Pr \<phi>') = (\<Sum>\<phi>'\<leftarrow>\<Phi>. Pr \<phi>')"
        by (simp add: listSubstract_multisubset_list_summation)
      ultimately have "real m * Pr \<phi> \<le> (\<Sum>\<phi>'\<leftarrow>\<Phi>. Pr \<phi>')"
        using hypothesis(1) by auto  
    }
    thus ?case
      by (metis Suc.hyps Suc_eq_plus1 le_SucE)
  qed
  thus ?thesis using assms
    by blast
qed

primrec (in Minimal_Logic) 
  stratified_deduction :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool" ("_ #\<turnstile> _ _" [60,100,59] 60)
  where
    "\<Gamma> #\<turnstile> 0 \<phi> = True"
  | "\<Gamma> #\<turnstile> (Suc n) \<phi> = (\<exists> \<Phi>. mset \<Phi> \<subseteq># mset \<Gamma> \<and> \<Phi> :\<turnstile> \<phi> \<and> (\<Gamma> \<ominus> \<Phi>) #\<turnstile> n \<phi>)"

lemma (in Minimal_Logic) empty_stratified_deduction_collapse [simp]:
  "[] #\<turnstile> (Suc n) \<phi> \<equiv> \<turnstile> \<phi>"
  by (induct n, simp, simp)    

lemma (in Minimal_Logic) stratified_deduction_weaken:
  assumes "\<turnstile> \<phi>"
  shows "\<Gamma> #\<turnstile> n \<phi>"
proof -
  have "\<turnstile> \<phi> \<Longrightarrow> \<forall> \<Gamma>. \<Gamma> #\<turnstile> n \<phi>"
    apply (induct n, simp, simp)
    using list_deduction_weaken by blast
  thus ?thesis using assms by blast
qed
      
lemma (in Minimal_Logic) stratified_deduction_monotonic:
  assumes "mset \<Lambda> \<subseteq># mset \<Gamma>"
      and "\<Lambda> #\<turnstile> n \<phi>"
    shows "\<Gamma> #\<turnstile> n \<phi>"
    using assms
proof -
  have "\<forall> \<Lambda> \<Gamma>. mset \<Lambda> \<subseteq># mset \<Gamma> \<longrightarrow> \<Lambda> #\<turnstile> n \<phi> \<longrightarrow> \<Gamma> #\<turnstile> n \<phi>"
  proof (induct n)
    case 0
    then show ?case by simp 
  next
    case (Suc n)
    {
      fix \<Lambda> \<Gamma>
      assume "mset \<Lambda> \<subseteq># mset \<Gamma>"
             "\<Lambda> #\<turnstile> (n+1) \<phi>"
      from this obtain \<Phi> where \<Phi>: "mset \<Phi> \<subseteq># mset \<Lambda>" "\<Phi> :\<turnstile> \<phi>"  "(\<Lambda> \<ominus> \<Phi>) #\<turnstile> n \<phi>"
        by auto
      with \<open>mset \<Lambda> \<subseteq># mset \<Gamma>\<close> have A: "mset \<Phi> \<subseteq># mset \<Gamma>"
        using \<open>mset \<Lambda> \<subseteq># mset \<Gamma>\<close> subset_mset.order.trans by blast
      moreover from \<open>mset \<Lambda> \<subseteq># mset \<Gamma>\<close> have "mset (\<Lambda> \<ominus> \<Phi>) \<subseteq># mset (\<Gamma> \<ominus> \<Phi>)"
        by (induct \<Phi>, 
            simp, 
            simp, 
            smt Diff_eq_empty_iff_mset 
                add.commute 
                diff_diff_add_mset 
                diff_single_trivial 
                diff_subset_eq_self 
                insert_DiffM2 
                subset_mset.ord_le_eq_trans)
      hence "(\<Gamma> \<ominus> \<Phi>) #\<turnstile> n \<phi>" using Suc.hyps \<Phi>(3) by blast
      ultimately have "\<Gamma> #\<turnstile> (n+1) \<phi>" using \<open>\<Phi> :\<turnstile> \<phi>\<close> by (simp, blast)
    }
    thus ?case by simp 
  qed
  thus ?thesis using assms by blast
qed

lemma (in Minimal_Logic) stratified_perm_proves:
  assumes "\<Gamma> <~~> \<Lambda>"
  shows "(\<Gamma> #\<turnstile> n \<phi>) \<equiv> (\<Lambda> #\<turnstile> n \<phi>)"
proof -
  from assms have "mset \<Gamma> = mset \<Lambda>" by (simp add: mset_eq_perm)
  hence "mset \<Gamma> \<subseteq># mset \<Lambda>" "mset \<Lambda> \<subseteq># mset \<Gamma>" by simp+ 
  thus "(\<Gamma> #\<turnstile> n \<phi>) \<equiv> (\<Lambda> #\<turnstile> n \<phi>)"
    using stratified_deduction_monotonic
    by smt
qed 
  
lemma (in Minimal_Logic) stratified_deduction_numeric_weaken:
  assumes "\<Gamma> #\<turnstile> n \<phi>"
  shows "\<forall>m \<le> n. \<Gamma> #\<turnstile> m \<phi>"
    using assms
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  assume "\<Gamma> #\<turnstile> (Suc n) \<phi>"
  from this obtain \<Phi> where \<Phi>: "(\<Gamma> \<ominus> \<Phi>) #\<turnstile> n \<phi>" by auto
  moreover have "mset (\<Gamma> \<ominus> \<Phi>) \<subseteq># mset \<Gamma>"
    by (induct \<Phi>, simp+, meson diff_subset_eq_self subset_mset.order.trans)
  ultimately have "\<Gamma> #\<turnstile> n \<phi>" using stratified_deduction_monotonic by auto
  thus ?case
    using Suc.hyps Suc.prems le_Suc_eq by blast 
qed

abbreviation (in Classical_Propositional_Logic) map_negation :: "'a list \<Rightarrow> 'a list" ("\<^bold>\<sim>")
  where "\<^bold>\<sim> \<Phi> \<equiv> map \<sim> \<Phi>"
  
lemma (in Classical_Propositional_Logic) map_negation_list_implication:
  "\<turnstile> ((\<^bold>\<sim> \<Phi>) :\<rightarrow> (\<sim> \<phi>)) \<leftrightarrow> (\<phi> \<rightarrow> \<Squnion> \<Phi>)"
proof (induct \<Phi>)
  case Nil
  then show ?case
    by (simp add: biconditional_def negation_def The_Principle_of_Pseudo_Scotus) 
next
  case (Cons \<psi> \<Phi>)
  have "\<turnstile> (\<^bold>\<sim> \<Phi> :\<rightarrow> \<sim> \<phi> \<leftrightarrow> (\<phi> \<rightarrow> \<Squnion> \<Phi>)) \<rightarrow> (\<sim> \<psi> \<rightarrow> \<^bold>\<sim> \<Phi> :\<rightarrow> \<sim> \<phi>) \<leftrightarrow> (\<phi> \<rightarrow> (\<psi> \<squnion> \<Squnion> \<Phi>))"
  proof -
    have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<^bold>\<sim> \<Phi> :\<rightarrow> \<sim> \<phi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>)) \<rightarrow> 
                        (\<sim> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<^bold>\<sim> \<Phi> :\<rightarrow> \<sim> \<phi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>))"
      by fastforce
    hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<^bold>\<sim> \<Phi> :\<rightarrow> \<sim> \<phi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>)) \<rightarrow> 
               (\<sim> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<^bold>\<sim> \<Phi> :\<rightarrow> \<sim> \<phi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
      using propositional_semantics by blast
    thus ?thesis
      by simp
  qed
  with Cons show ?case
    by (metis list.simps(9) 
              Arbitrary_Disjunction.simps(2) 
              Modus_Ponens 
              list_implication.simps(2))
qed

lemma perm_map_perm_list_exists:
  assumes "A <~~> map f B"
  shows "\<exists> B'. A = map f B' \<and> B' <~~> B"
proof -
  have "\<forall>B. A <~~> map f B \<longrightarrow> (\<exists> B'. A = map f B' \<and> B' <~~> B)"
  proof (induct A)
    case Nil
    then show ?case by simp
  next
    case (Cons a A)
    {
      fix B
      assume "a # A <~~> map f B"
      from this obtain b where b:
        "b \<in> set B"
        "f b = a"
        by (metis (full_types) imageE list.set_intros(1) mset_eq_perm set_map set_mset_mset)
      hence "A <~~> (remove1 (f b) (map f B))"
        by (metis \<open>a # A <~~> map f B\<close> perm_remove_perm remove_hd)
      with b have "A <~~> (map f (remove1 b B))"
        by (smt list.simps(9) mset_eq_perm mset_map mset_remove1 perm_remove remove_hd)
      from this obtain B' where B':
        "A = map f B'"
        "B' <~~> (remove1 b B)"
        using Cons.hyps by blast
      with b have "a # A = map f (b # B')"
        by simp
      moreover have "B <~~> b # B'"
        by (meson B'(2) b(1) cons_perm_eq perm.trans perm_remove perm_sym)
      ultimately have "\<exists>B'. a # A = map f B' \<and> B' <~~> B"
        by (meson perm_sym)
    }
    thus ?case by blast
  qed  
  with assms show ?thesis by blast
qed
  
lemma mset_sub_map_list_exists:
  assumes "mset \<Phi> \<subseteq># mset (map f \<Gamma>)"
  shows "\<exists> \<Phi>'. mset \<Phi>' \<subseteq># mset \<Gamma> \<and> \<Phi> = (map f \<Phi>')"
proof -
  have "\<forall> \<Phi>. mset \<Phi> \<subseteq># mset (map f \<Gamma>) \<longrightarrow> (\<exists> \<Phi>'. mset \<Phi>' \<subseteq># mset \<Gamma> \<and> \<Phi> = (map f \<Phi>'))"
  proof (induct \<Gamma>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<gamma> \<Gamma>)
    {
      fix \<Phi>
      assume "mset \<Phi> \<subseteq># mset (map f (\<gamma> # \<Gamma>))"
      have "\<exists>\<Phi>'. mset \<Phi>' \<subseteq># mset (\<gamma> # \<Gamma>) \<and> \<Phi> = map f \<Phi>'"
      proof cases
        assume "f \<gamma> \<in> set \<Phi>"
        hence "f \<gamma> # (remove1 (f \<gamma>) \<Phi>) <~~> \<Phi>"
          by (simp add: perm_remove perm_sym)
        with \<open>mset \<Phi> \<subseteq># mset (map f (\<gamma> # \<Gamma>))\<close>
        have "mset (remove1 (f \<gamma>) \<Phi>) \<subseteq># mset (map f \<Gamma>)"
          by (metis insert_subset_eq_iff 
                    list.simps(9) 
                    mset.simps(2) 
                    mset_eq_perm 
                    mset_remove1 
                    remove_hd)
        from this Cons obtain \<Phi>' where \<Phi>':
          "mset \<Phi>' \<subseteq># mset \<Gamma>"
          "remove1 (f \<gamma>) \<Phi> = map f \<Phi>'"
          by blast
        hence "mset (\<gamma> # \<Phi>') \<subseteq># mset (\<gamma> # \<Gamma>)"
          and "f \<gamma> # (remove1 (f \<gamma>) \<Phi>) = map f (\<gamma> # \<Phi>')"
          by simp+
        hence "\<Phi> <~~> map f (\<gamma> # \<Phi>')"
          using \<open>f \<gamma> \<in> set \<Phi>\<close> perm_remove by force
        from this obtain \<Phi>'' where \<Phi>'':
          "\<Phi> = map f \<Phi>''"
          "\<Phi>'' <~~> \<gamma> # \<Phi>'"
          using perm_map_perm_list_exists 
          by blast
        hence "mset \<Phi>'' \<subseteq># mset (\<gamma> # \<Gamma>)"
          by (metis \<open>mset (\<gamma> # \<Phi>') \<subseteq># mset (\<gamma> # \<Gamma>)\<close> mset_eq_perm)
        thus ?thesis using \<Phi>'' by blast 
      next
        assume "f \<gamma> \<notin> set \<Phi>"
        with \<open>mset \<Phi> \<subseteq># mset (map f (\<gamma> # \<Gamma>))\<close>
        have "mset \<Phi> \<subseteq># mset (map f \<Gamma>)"
          by (smt Diff_eq_empty_iff_mset 
                  add_mset_add_single 
                  cancel_ab_semigroup_add_class.diff_right_commute 
                  diff_diff_add diff_single_trivial 
                  image_mset_add_mset 
                  mset.simps(2) 
                  mset_map 
                  set_mset_mset)
        with Cons show ?thesis
          by (metis diff_subset_eq_self mset_remove1 remove_hd subset_mset.order.trans)
      qed
    }
    thus ?case using Cons by blast
  qed
  thus ?thesis using assms by blast
qed
        
lemma listSubtract_mset_homomorphism [simp]:
  "mset (A \<ominus> B) = mset A - mset B"
  by (induct B, simp, simp)

lemma map_perm:
  assumes "A <~~> B"
  shows "map f A <~~> map f B"
  by (metis assms mset_eq_perm mset_map)

lemma listSubtract_not_member:
  assumes "b \<notin> set A"
  shows "A \<ominus> B = A \<ominus> (remove1 b B)"
  using assms
  by (induct B, 
      simp, 
      simp, 
      metis add_mset_add_single 
            diff_subset_eq_self 
            insert_DiffM2 
            insert_subset_eq_iff 
            listSubtract_mset_homomorphism 
            remove1_idem set_mset_mset)

lemma listSubtract_monotonic:
  assumes "mset A \<subseteq># mset B"
  shows "mset (A \<ominus> C) \<subseteq># mset (B \<ominus> C)"
  by (simp, meson assms subset_eq_diff_conv subset_mset.dual_order.refl subset_mset.order_trans)

lemma map_monotonic:
  assumes "mset A \<subseteq># mset B"
  shows "mset (map f A) \<subseteq># mset (map f B)"
  by (simp add: assms image_mset_subseteq_mono)
    
lemma map_listSubtract_mset_containment:
  "mset ((map f A) \<ominus> (map f B)) \<subseteq># mset (map f (A \<ominus> B))"
  by (induct B, simp, simp,
      metis diff_subset_eq_self 
            diff_zero 
            image_mset_add_mset 
            image_mset_subseteq_mono 
            image_mset_union 
            subset_eq_diff_conv 
            subset_eq_diff_conv)

lemma map_listSubtract_mset_equivalence:
  assumes "mset B \<subseteq># mset A"
  shows "mset ((map f A) \<ominus> (map f B)) = mset (map f (A \<ominus> B))"
  using assms
  by (induct B, simp, simp add: image_mset_Diff) 

lemma concat_set_membership_mset_containment:
  assumes "concat \<Gamma> <~~> \<Lambda>"
  and     "\<Phi> \<in> set \<Gamma>"
  shows   "mset \<Phi> \<subseteq># mset \<Lambda>"
  using assms
  by (induct \<Gamma>, simp, meson concat_remove1 mset_le_perm_append perm.trans perm_sym)

lemma (in Minimal_Logic) stratified_one_deduction: "\<Gamma> #\<turnstile> 1 \<phi> = \<Gamma> :\<turnstile> \<phi>"
proof (rule iffI)
  assume "\<Gamma> #\<turnstile> 1 \<phi>"
  hence "\<exists> \<Phi>. set \<Phi> \<subseteq> set \<Gamma> \<and> \<Phi> :\<turnstile> \<phi>"
    by (simp, metis mset_subset_eqD set_mset_mset subsetI)
  thus "\<Gamma> :\<turnstile> \<phi>"
    using list_deduction_monotonic by blast
next
  assume "\<Gamma> :\<turnstile> \<phi>"
  thus "\<Gamma> #\<turnstile> 1 \<phi>" by (simp, force)
qed
  
lemma (in Classical_Propositional_Logic) stratified_deduction_equivalence:
  "\<^bold>\<sim> \<Gamma> #\<turnstile> n (\<sim> \<phi>) \<equiv> \<exists> \<L>. stratified n \<phi> \<Gamma> \<L>"
proof -
  have "\<forall> \<Gamma> \<L>.( \<^bold>\<sim> \<Gamma> #\<turnstile> n (\<sim> \<phi>) = (\<exists> \<L>. stratified n \<phi> \<Gamma> \<L>))"
  proof (induct n)
    case 0 then show ?case unfolding stratified_def by simp
  next
    case (Suc n)
    {
      fix \<Gamma> :: "'a list"
      fix \<Lambda> :: "'a list list"
      have "\<^bold>\<sim> \<Gamma> #\<turnstile> (Suc n) (\<sim> \<phi>) \<equiv> \<exists> \<L>. stratified (Suc n) \<phi> \<Gamma> \<L>"
      proof -
        {
          assume "n = 0"
          have "(\<exists> \<L>. stratified 1 \<phi> \<Gamma> \<L>) = stratified 1 \<phi> \<Gamma> [\<Gamma>]"
          proof (rule iffI)
            assume "\<exists> \<L>. stratified 1 \<phi> \<Gamma> \<L>"
            hence "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Gamma>"
              by (metis One_nat_def 
                        list.size(3) 
                        empty_stratified_deduction_collapse 
                        implicational_concatenation 
                        stratified_\<Phi>_implication 
                        stratified_def 
                        stratified_deduction.simps(1) 
                        mset_eq_perm 
                        set_empty2 
                        set_mset_mset)
            thus "stratified 1 \<phi> \<Gamma> [\<Gamma>]"
              unfolding stratified_def
              by simp
          next
            assume "stratified 1 \<phi> \<Gamma> [\<Gamma>]"
            thus "\<exists> \<L>. stratified 1 \<phi> \<Gamma> \<L>" by blast
          qed
          moreover have "\<^bold>\<sim> \<Gamma> #\<turnstile> 1 (\<sim> \<phi>) = \<^bold>\<sim> \<Gamma> :\<turnstile> \<sim> \<phi>"
            using stratified_one_deduction by blast
          ultimately have "\<^bold>\<sim> \<Gamma> #\<turnstile> (Suc n) (\<sim> \<phi>) \<equiv> \<exists> \<L>. stratified (Suc n) \<phi> \<Gamma> \<L>"
            using \<open>n = 0\<close>
            unfolding stratified_def
            by (simp,
                smt biconditional_weaken 
                    list_deduction_def 
                    map_negation_list_implication 
                    set_deduction_base_theory)
        }
        moreover
        {
          assume "\<^bold>\<sim> \<Gamma> #\<turnstile> (Suc n) (\<sim> \<phi>)"
                 "n > 0"
          from this obtain \<Phi> where \<Phi>:
            "mset \<Phi> \<subseteq># mset \<Gamma>"
            "mset (\<^bold>\<sim> \<Phi>) \<subseteq># mset (\<^bold>\<sim> \<Gamma>)" 
            "(\<^bold>\<sim> \<Phi>) :\<turnstile> (\<sim> \<phi>)"
            "((\<^bold>\<sim> \<Gamma>) \<ominus> (\<^bold>\<sim> \<Phi>)) #\<turnstile> n (\<sim> \<phi>)"
            using stratified_deduction.simps(2) 
                  mset_sub_map_list_exists 
            by blast
          have  "mset ((\<^bold>\<sim> \<Gamma>) \<ominus> (\<^bold>\<sim> \<Phi>)) \<subseteq># mset (\<^bold>\<sim> (\<Gamma> \<ominus> \<Phi>))"
            using map_listSubtract_mset_containment by blast
          with \<Phi> have "\<^bold>\<sim> (\<Gamma> \<ominus> \<Phi>) #\<turnstile> n (\<sim> \<phi>)"
            using stratified_deduction_monotonic by blast
          from this Suc.hyps obtain \<L>' where \<L>':
            "stratified n \<phi> (\<Gamma> \<ominus> \<Phi>) \<L>'"
            by blast
          hence "\<Phi> @ (\<Gamma> \<ominus> \<Phi>) <~~> concat (\<Phi> # \<L>')"
            by (simp add: \<open>0 < n\<close> local.stratified_def perm_sym)
          hence "\<Gamma> <~~> concat (\<Phi> # \<L>')"
            by (metis \<Phi>(1) 
                      append_perm_listSubtract_intro 
                      mset_le_perm_append 
                      perm.trans 
                      perm_append1_eq 
                      perm_append_swap 
                      perm_sym)
          moreover have "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Phi>"
            using \<Phi>(3) 
                  biconditional_weaken 
                  list_deduction_def 
                  map_negation_list_implication 
                  set_deduction_base_theory 
            by blast
          ultimately have "\<exists> \<L>. stratified (Suc n) \<phi> \<Gamma> \<L>"
            using \<L>' \<open>n > 0\<close>
            unfolding stratified_def
            by (metis length_Cons neq0_conv perm_sym set_ConsD)
        }
        moreover
        {
          assume "\<exists> \<L>. stratified (Suc n) \<phi> \<Gamma> \<L>"
                 "n > 0"
          from this obtain \<L> where \<L>: "stratified (Suc n) \<phi> \<Gamma> \<L>"
            by blast
          from this obtain \<Phi> where \<Phi>: 
            "\<Phi> \<in> set \<L>"
            "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Phi>"
            using stratified_def by fastforce
          hence "\<^bold>\<sim> \<Phi> :\<turnstile> \<sim> \<phi>"
            using biconditional_weaken 
                  list_deduction_def 
                  map_negation_list_implication 
                  set_deduction_base_theory 
          by blast
          from \<Phi> \<open>n > 0\<close> \<L> have "stratified n \<phi> (\<Gamma> \<ominus> \<Phi>) (\<L> \<ominus> [\<Phi>])"
            using stratified_listSubtraction by fastforce
          hence "\<^bold>\<sim> (\<Gamma> \<ominus> \<Phi>) #\<turnstile> n (\<sim> \<phi>)"
            using Suc.hyps by blast
          moreover from \<open>n > 0\<close> \<L> \<Phi> have "mset \<Phi> \<subseteq># mset \<Gamma>"
            unfolding stratified_def
            by (simp, meson concat_set_membership_mset_containment) 
          hence "\<^bold>\<sim> (\<Gamma> \<ominus> \<Phi>) <~~> \<^bold>\<sim> \<Gamma> \<ominus> \<^bold>\<sim> \<Phi>"
            by (metis map_listSubtract_mset_equivalence mset_eq_perm)
          ultimately have
            "\<^bold>\<sim> \<Gamma> \<ominus> \<^bold>\<sim> \<Phi> #\<turnstile> n (\<sim> \<phi>)"
            using stratified_perm_proves by blast
          moreover from \<open>mset \<Phi> \<subseteq># mset \<Gamma>\<close> have "mset (\<^bold>\<sim> \<Phi>) \<subseteq># mset (\<^bold>\<sim> \<Gamma>)"
            by (metis Diff_eq_empty_iff_mset 
                      list.simps(8) 
                      listSubtract_mset_homomorphism 
                      map_listSubtract_mset_containment 
                      mset.simps(1) 
                      mset_map 
                      subset_mset.eq_iff 
                      subset_mset.zero_le)
          ultimately have "\<^bold>\<sim> \<Gamma> #\<turnstile> (Suc n) (\<sim> \<phi>)"
            using \<open>\<^bold>\<sim> \<Phi> :\<turnstile> \<sim> \<phi>\<close>
            using stratified_deduction.simps(2) by blast
        }
        ultimately show "\<^bold>\<sim> \<Gamma> #\<turnstile> (Suc n) (\<sim> \<phi>) \<equiv> \<exists> \<L>. stratified (Suc n) \<phi> \<Gamma> \<L>"
          by (smt neq0_conv)
      qed 
    }
    thus ?case by blast
  qed
  thus "\<^bold>\<sim> \<Gamma> #\<turnstile> n (\<sim> \<phi>) \<equiv> \<exists> \<L>. stratified n \<phi> \<Gamma> \<L>" by simp
qed

lemma (in Classical_Propositional_Logic)
  list_deduction_double_negation_equivalence:
  "\<^bold>\<sim> (\<^bold>\<sim> \<Phi>) :\<turnstile> \<phi> = \<Phi> :\<turnstile> \<phi>"
proof -
  have "\<forall> \<phi>. \<Phi> :\<turnstile> \<phi> = \<^bold>\<sim> (\<^bold>\<sim> \<Phi>) :\<turnstile> \<phi>"
  proof (induct \<Phi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<psi> \<Phi>)
    {
      fix \<phi>
      have "\<psi> # \<Phi> :\<turnstile> \<phi> = \<^bold>\<sim> (\<^bold>\<sim> (\<psi> # \<Phi>)) :\<turnstile> \<phi>"
      proof -
        have \<diamondsuit>: "\<turnstile> (\<sim> (\<sim> \<psi>) \<rightarrow> \<phi>) \<leftrightarrow> (\<psi> \<rightarrow> \<phi>)"
          using biconditional_def disjunction_def implication_equivalence negation_def 
          by auto
        have "\<^bold>\<sim> (\<^bold>\<sim> (\<psi> # \<Phi>)) :\<turnstile> \<phi> = \<^bold>\<sim> (\<^bold>\<sim> (\<Phi>)) :\<turnstile> \<sim> (\<sim> \<psi>) \<rightarrow> \<phi>"
          by (simp add: list_deduction_theorem)
        also have "... = \<^bold>\<sim> (\<^bold>\<sim> (\<Phi>)) :\<turnstile> \<psi> \<rightarrow> \<phi>"
          using \<diamondsuit> list_deduction_weaken [where \<Gamma>="\<^bold>\<sim> (\<^bold>\<sim> (\<Phi>))"]
          unfolding negation_def
          by (meson biconditional_left_elimination 
                    biconditional_right_elimination 
                    list_deduction_modus_ponens)
        also have "... = \<Phi> :\<turnstile> \<psi> \<rightarrow> \<phi>"
          using Cons by blast
        also have "... = \<psi> # \<Phi> :\<turnstile> \<phi>"
          by (simp add: list_deduction_theorem)
        finally show ?thesis by simp
      qed
    } 
    then show ?case by blast 
  qed
  then show ?thesis by blast
qed
  
lemma (in Classical_Propositional_Logic) 
  stratified_deduction_double_negation_equivalence:
  "\<^bold>\<sim> (\<^bold>\<sim> \<Gamma>) #\<turnstile> n \<phi> = \<Gamma> #\<turnstile> n \<phi>"
proof -
  have "\<forall> \<Gamma>. \<Gamma> #\<turnstile> n \<phi> = \<^bold>\<sim> (\<^bold>\<sim> \<Gamma>) #\<turnstile> n \<phi>"
  proof (induct n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    {
      fix \<Gamma>
      have "\<Gamma> #\<turnstile> (Suc n) \<phi> = \<^bold>\<sim> (\<^bold>\<sim> \<Gamma>) #\<turnstile> (Suc n) \<phi>"
      proof (rule iffI)
        assume "\<Gamma> #\<turnstile> (Suc n) \<phi>"
        from this obtain \<Phi> where \<Phi>:
          "mset \<Phi> \<subseteq># mset \<Gamma>" 
          "\<Phi> :\<turnstile> \<phi>" 
          "\<Gamma> \<ominus> \<Phi> #\<turnstile> n \<phi>"
          by auto
        from \<Phi> have A: "mset (\<^bold>\<sim> (\<^bold>\<sim> \<Phi>)) \<subseteq># mset (\<^bold>\<sim> (\<^bold>\<sim> \<Gamma>))"
          using map_monotonic by blast
        from \<Phi> have B: "\<^bold>\<sim> (\<^bold>\<sim> \<Phi>) :\<turnstile> \<phi>"
          using list_deduction_double_negation_equivalence by blast
        from \<Phi> Suc.hyps have C:
          "\<^bold>\<sim> (\<^bold>\<sim> \<Gamma>) \<ominus> \<^bold>\<sim> (\<^bold>\<sim> \<Phi>) #\<turnstile> n \<phi>"
          by (metis stratified_deduction_monotonic 
                    map_listSubtract_mset_containment 
                    map_listSubtract_mset_equivalence 
                    map_monotonic)
        from A B C show "\<^bold>\<sim> (\<^bold>\<sim> \<Gamma>) #\<turnstile> (Suc n) \<phi>" 
          by (simp, force)
      next
        assume "\<^bold>\<sim> (\<^bold>\<sim> \<Gamma>) #\<turnstile> (Suc n) \<phi>"
        from this obtain \<Phi> where \<Phi>:
          "mset \<Phi> \<subseteq># mset \<Gamma>" 
          "\<^bold>\<sim> (\<^bold>\<sim> \<Phi>) :\<turnstile> \<phi>"
          "\<^bold>\<sim> (\<^bold>\<sim> \<Gamma>) \<ominus> \<^bold>\<sim> (\<^bold>\<sim> \<Phi>) #\<turnstile> n \<phi>"
          using stratified_deduction.simps(2) mset_sub_map_list_exists 
          by blast
        moreover from \<Phi> have "\<Phi> :\<turnstile> \<phi>"
          using list_deduction_double_negation_equivalence by blast
        moreover from \<Phi> Suc.hyps have "\<Gamma> \<ominus> \<Phi> #\<turnstile> n \<phi>"
          by (metis (no_types, lifting)  
                    stratified_deduction_monotonic 
                    map_listSubtract_mset_containment 
                    map_listSubtract_mset_equivalence 
                    mset_map)
        ultimately show "\<Gamma> #\<turnstile> (Suc n) \<phi>"
          using stratified_deduction.simps(2) by blast 
      qed
    }
    thus ?case by blast
  qed
  thus ?thesis by blast
qed

lemma (in Weakly_Additive_Logical_Probability) 
  stratified_deduction_implies_probability_inequality:
  assumes "\<^bold>\<sim> \<Gamma> #\<turnstile> n (\<sim> \<phi>)"
  shows "(real n) * Pr \<phi> \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
  using assms
        stratified_deduction_equivalence
        stratified_summation 
  by blast  
  
lemma (in Weakly_Additive_Logical_Probability) list_probability_upper_bound:
  "(\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>) \<le> real (length \<Gamma>)"
  by (induct \<Gamma>, simp, simp, smt unity_upper_bound)

lemma (in Classical_Propositional_Logic) stratified_deduction_substitution:
  assumes "\<turnstile> \<phi> \<leftrightarrow> \<psi>"
  shows "\<Gamma> #\<turnstile> n \<phi> = \<Gamma> #\<turnstile> n \<psi>"
proof -
  have "\<forall>\<Gamma>. \<Gamma> #\<turnstile> n \<phi> = \<Gamma> #\<turnstile> n \<psi>"
    by (induct n, 
        simp, 
        simp, 
        meson assms 
              insert_iff 
              biconditional_weaken 
              list_deduction_modus_ponens 
              list_deduction_weaken 
              set_deduction_base_theory 
              set_deduction_reflection 
              set_deduction_theorem)
  thus ?thesis by blast
qed

definition (in Minimal_Logic) unproving_core :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list set" ("\<CC>")
  where
    "\<CC> \<Gamma> \<phi> = {\<Phi>. mset \<Phi> \<subseteq># mset \<Gamma> 
               \<and> \<not> \<Phi> :\<turnstile> \<phi> 
               \<and> (\<forall> \<Psi>. mset \<Psi> \<subseteq># mset \<Gamma> \<longrightarrow> \<not> \<Psi> :\<turnstile> \<phi> \<longrightarrow> length \<Psi> \<le> length \<Phi>)}"

lemma (in Minimal_Logic) unproving_length_monotonic:
  assumes "mset \<Sigma> \<subseteq># mset \<Gamma>"
      and "\<Phi> \<in> \<CC> \<Sigma> \<phi>"
      and "\<Psi> \<in> \<CC> \<Gamma> \<phi>"
    shows "length \<Phi> \<le> length \<Psi>"
proof -
  have "\<not> \<Phi> :\<turnstile> \<phi>" "mset \<Phi> \<subseteq># mset \<Gamma>"
    using assms(1) assms(2) unproving_core_def by (blast, auto)
  thus ?thesis
    using assms(3)
    unfolding unproving_core_def
    by blast
qed    
    
lemma (in Minimal_Logic) unproving_core_complement_deduction:
  assumes "\<Phi> \<in> \<CC> \<Gamma> \<phi>"
      and "\<psi> \<in> set (\<Gamma> \<ominus> \<Phi>)"
    shows "\<Phi> :\<turnstile> \<psi> \<rightarrow> \<phi>"
proof (rule ccontr)
  assume "\<not> \<Phi> :\<turnstile> \<psi> \<rightarrow> \<phi>"
  hence "\<not> (\<psi> # \<Phi>) :\<turnstile> \<phi>"
    by (simp add: list_deduction_theorem)
  moreover
  have "mset \<Phi> \<subseteq># mset \<Gamma>" "\<psi> \<in># mset (\<Gamma> \<ominus> \<Phi>)"
    using assms
    unfolding unproving_core_def
    by (blast, meson in_multiset_in_set)
  hence "mset (\<psi> # \<Phi>) \<subseteq># mset \<Gamma>" 
    by (simp, metis add_mset_add_single 
                    mset_subset_eq_mono_add_left_cancel 
                    mset_subset_eq_single 
                    subset_mset.add_diff_inverse)
  ultimately have "length (\<psi> # \<Phi>) \<le> length (\<Phi>)"
    using assms
    unfolding unproving_core_def
    by blast
  thus "False"
    by simp
qed

lemma listSubtract_set_difference_lower_bound:
  "set \<Gamma> - set \<Phi> \<subseteq> set (\<Gamma> \<ominus> \<Phi>)"
  using subset_Diff_insert 
  by (induct \<Phi>, simp, fastforce)          

lemma listSubtract_set_trivial_upper_bound:
  "set (\<Gamma> \<ominus> \<Phi>) \<subseteq> set \<Gamma>"
      by (induct \<Phi>, 
          simp, 
          simp, 
          meson dual_order.trans 
                set_remove1_subset)
          
lemma (in Minimal_Logic) unproving_core_set_complement [simp]:
  assumes "\<Phi> \<in> \<CC> \<Gamma> \<phi>"
  shows "set (\<Gamma> \<ominus> \<Phi>) = set \<Gamma> - set \<Phi>"
proof (rule equalityI)
  show "set (\<Gamma> \<ominus> \<Phi>) \<subseteq> set \<Gamma> - set \<Phi>"
  proof (rule subsetI)
    fix \<psi>
    assume "\<psi> \<in> set (\<Gamma> \<ominus> \<Phi>)"
    moreover from this have "\<Phi> :\<turnstile> \<psi> \<rightarrow> \<phi>"
      using assms
      using unproving_core_complement_deduction 
      by blast  
    hence "\<psi> \<notin> set \<Phi>"
      using assms 
            list_deduction_modus_ponens 
            list_deduction_reflection 
            unproving_core_def 
      by blast
    ultimately show "\<psi> \<in> set \<Gamma> - set \<Phi>"
      using listSubtract_set_trivial_upper_bound [where \<Gamma>="\<Gamma>" and \<Phi>="\<Phi>"]
      by blast
  qed
next
  show "set \<Gamma> - set \<Phi> \<subseteq> set (\<Gamma> \<ominus> \<Phi>)"
    by (simp add: listSubtract_set_difference_lower_bound)
qed  
  
lemma (in Minimal_Logic) unproving_core_complement_equiv:
  assumes "\<Phi> \<in> \<CC> \<Gamma> \<phi>"
      and "\<psi> \<in> set \<Gamma>"
    shows "\<Phi> :\<turnstile> \<psi> \<rightarrow> \<phi> = (\<psi> \<notin> set \<Phi>)"
  apply (rule iffI)
  using assms(1) list_deduction_modus_ponens list_deduction_reflection unproving_core_def 
   apply blast
  using assms unproving_core_complement_deduction 
    by auto
    
lemma (in Minimal_Logic) unproving_core_existance:
  assumes "\<not> \<turnstile> \<phi>"
    shows "\<exists> \<Sigma>. \<Sigma> \<in> \<CC> \<Gamma> \<phi>"
proof (rule ccontr)
  assume "\<nexists>\<Sigma>. \<Sigma> \<in> \<CC> \<Gamma> \<phi>"
  hence \<diamondsuit>: "\<forall> \<Phi>. mset \<Phi> \<subseteq># mset \<Gamma> \<longrightarrow>
                  \<not> \<Phi> :\<turnstile> \<phi> \<longrightarrow>
                  (\<exists>\<Psi>. mset \<Psi> \<subseteq># mset \<Gamma> \<and> \<not> \<Psi> :\<turnstile> \<phi> \<and> length \<Psi> > length \<Phi>)"
    unfolding unproving_core_def
    by fastforce
  {
    fix n
    have "\<exists> \<Psi>. mset \<Psi> \<subseteq># mset \<Gamma> \<and> \<not> \<Psi> :\<turnstile> \<phi> \<and> length \<Psi> > n"
      using \<diamondsuit>
      by (induct n, 
          metis assms list_deduction_base_theory mset.simps(1) neq0_conv subset_mset.bot.extremum,
          fastforce)          
  }
  hence "\<exists> \<Psi>. mset \<Psi> \<subseteq># mset \<Gamma> \<and> length \<Psi> > length \<Gamma>"
    by auto
  thus "False"
    using size_mset_mono by fastforce
qed
    
lemma msubset_listSubtract_length_antitonic:
  assumes "mset \<Phi> \<subseteq># mset \<Psi>"
  shows "length (\<Gamma> \<ominus> \<Psi>) \<le> length (\<Gamma> \<ominus> \<Phi>)"
proof -
  from assms have "mset (\<Gamma> \<ominus> \<Psi>) \<subseteq># mset (\<Gamma> \<ominus> \<Phi>)"
    by (simp, metis diff_diff_add diff_subset_eq_self subset_mset.add_diff_inverse)
  thus ?thesis
    by (metis size_mset size_mset_mono)
qed
        
lemma (in Minimal_Logic) unproving_listSubtract_length_equiv:
  assumes "\<Phi> \<in> \<CC> \<Gamma> \<phi>"
      and "\<Psi> \<in> \<CC> \<Gamma> \<phi>"
    shows "length (\<Gamma> \<ominus> \<Phi>) = length (\<Gamma> \<ominus> \<Psi>)"
proof -
  from assms have "length \<Phi> = length \<Psi>"
    by (simp add: dual_order.antisym unproving_core_def)
  moreover
  have "mset \<Phi> \<subseteq># mset \<Gamma>"
       "mset \<Psi> \<subseteq># mset \<Gamma>"
    using assms unproving_core_def by blast+
  hence "length (\<Gamma> \<ominus> \<Phi>) = length \<Gamma> - length \<Phi>"
        "length (\<Gamma> \<ominus> \<Psi>) = length \<Gamma> - length \<Psi>"
    by (metis listSubtract_mset_homomorphism size_Diff_submset size_mset)+
  ultimately show ?thesis by smt
qed

lemma length_sub_mset:
  assumes "mset \<Psi> \<subseteq># mset \<Gamma>"
      and "length \<Psi> >= length \<Gamma>"
    shows "mset \<Psi> = mset \<Gamma>"
  using assms
proof -
  have "\<forall> \<Psi>. mset \<Psi> \<subseteq># mset \<Gamma> \<longrightarrow> length \<Psi> >= length \<Gamma> \<longrightarrow> mset \<Psi> = mset \<Gamma>"
  proof (induct \<Gamma>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<gamma> \<Gamma>)
    {
      fix \<Psi>
      assume "mset \<Psi> \<subseteq># mset (\<gamma> # \<Gamma>)" "length \<Psi> >= length (\<gamma> # \<Gamma>)"
      have "\<gamma> \<in> set \<Psi>"
      proof (rule ccontr)
        assume "\<gamma> \<notin> set \<Psi>"
        hence \<diamondsuit>: "remove1 \<gamma> \<Psi> = \<Psi>"
          by (simp add: remove1_idem)
        have "mset \<Psi> \<subseteq># mset (\<gamma> # \<Gamma>)"
          using \<open>mset \<Psi> \<subseteq># mset (\<gamma> # \<Gamma>)\<close> by auto       
        hence "mset \<Psi> \<subseteq># mset (remove1 \<gamma> (\<gamma> # \<Gamma>))"
          by (metis \<diamondsuit> mset_le_perm_append perm_remove_perm remove1_append)
        hence "mset \<Psi> \<subseteq># mset \<Gamma>"
          by simp
        hence "mset \<Psi> = mset \<Gamma>"
          using \<open>length (\<gamma> # \<Gamma>) \<le> length \<Psi>\<close> size_mset_mono by fastforce 
        hence "length \<Psi> = length \<Gamma>"
          by (metis size_mset)
        hence "length \<Gamma> \<ge> length (\<gamma> # \<Gamma>)"
          using \<open>length (\<gamma> # \<Gamma>) \<le> length \<Psi>\<close> by auto 
        thus "False" by simp
      qed
      hence \<heartsuit>: "mset \<Psi> = mset (\<gamma> # (remove1 \<gamma> \<Psi>))"
        by simp
      hence "length (remove1 \<gamma> \<Psi>) >= length \<Gamma>"
        by (metis \<open>length (\<gamma> # \<Gamma>) \<le> length \<Psi>\<close> 
                  drop_Suc_Cons 
                  drop_eq_Nil 
                  length_Cons 
                  mset_eq_length)
      moreover have "mset (remove1 \<gamma> \<Psi>) \<subseteq># mset \<Gamma>"
        by (simp,
            metis \<heartsuit> 
                  \<open>mset \<Psi> \<subseteq># mset (\<gamma> # \<Gamma>)\<close>
                  mset.simps(2) 
                  mset_remove1 
                  mset_subset_eq_add_mset_cancel)
      ultimately have "mset (remove1 \<gamma> \<Psi>) = mset \<Gamma>" using Cons by blast
      with \<heartsuit> have "mset \<Psi> = mset (\<gamma> # \<Gamma>)" by simp
    }
    thus ?case by blast
  qed
  thus ?thesis using assms by blast
qed

lemma listSubtract_cancel_weak_upper_bound:  
  assumes "mset \<Psi> \<subseteq># mset \<Gamma>"
          "mset \<Sigma> \<subseteq># mset \<Gamma>"
    shows "mset ((\<Gamma> \<ominus> \<Psi>) \<ominus> (\<Sigma> \<ominus> \<Psi>)) \<subseteq># mset (\<Gamma> \<ominus> \<Sigma>)"
proof -
  have "\<forall> \<Gamma> \<Psi>.
          mset \<Psi> \<subseteq># mset \<Gamma> \<longrightarrow> 
          mset \<Sigma> \<subseteq># mset \<Gamma> \<longrightarrow>
          mset ((\<Gamma> \<ominus> \<Psi>) \<ominus> (\<Sigma> \<ominus> \<Psi>)) \<subseteq># mset (\<Gamma> \<ominus> \<Sigma>)"
  proof (induct \<Sigma>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<sigma> \<Sigma>)
    {
      fix \<Gamma> \<Psi> :: "'a list"
      assume "mset \<Psi> \<subseteq># mset \<Gamma>"
             "mset (\<sigma> # \<Sigma>) \<subseteq># mset \<Gamma>"
      hence "mset \<Sigma> \<subseteq># mset (remove1 \<sigma> \<Gamma>)"
            "mset (remove1 \<sigma> \<Psi>) \<subseteq># mset (remove1 \<sigma> \<Gamma>)"
      using listSubtract.simps(1) 
            listSubtract.simps(2) 
            listSubtract_monotonic
      by (metis remove_hd, metis)
      have "mset ((\<Gamma> \<ominus> \<Psi>) \<ominus> ((\<sigma> # \<Sigma>) \<ominus> \<Psi>)) \<subseteq># mset (\<Gamma> \<ominus> (\<sigma> # \<Sigma>))"
      proof (cases "\<sigma> \<in> set \<Psi>")
        assume "\<sigma> \<in> set \<Psi>"
        hence "mset ((\<Gamma> \<ominus> \<Psi>) \<ominus> ((\<sigma> # \<Sigma>) \<ominus> \<Psi>)) = 
               mset (((remove1 \<sigma> \<Gamma>) \<ominus> (remove1 \<sigma> \<Psi>)) \<ominus> (\<Sigma> \<ominus> (remove1 \<sigma> \<Psi>)))"
          by (smt listSubtract_cons_remove1_perm 
                  listSubtract_mset_homomorphism 
                  listSubtract_remove1_perm 
                  mset_eq_perm)
        moreover from Cons.hyps have
          "mset (((remove1 \<sigma> \<Gamma>) \<ominus> (remove1 \<sigma> \<Psi>)) \<ominus> (\<Sigma> \<ominus> (remove1 \<sigma> \<Psi>))) \<subseteq>#
           mset ((remove1 \<sigma> \<Gamma>) \<ominus> \<Sigma>)"
          using \<open>mset (remove1 \<sigma> \<Psi>) \<subseteq># mset (remove1 \<sigma> \<Gamma>)\<close> 
                \<open>mset \<Sigma> \<subseteq># mset (remove1 \<sigma> \<Gamma>)\<close> 
          by blast
        ultimately show ?thesis by simp
      next
        assume "\<sigma> \<notin> set \<Psi>"
        hence "mset ((\<Gamma> \<ominus> \<Psi>) \<ominus> ((\<sigma> # \<Sigma>) \<ominus> \<Psi>)) = 
               mset (((remove1 \<sigma> \<Gamma>) \<ominus> \<Psi>) \<ominus> (\<Sigma> \<ominus> \<Psi>))"
          by simp
        moreover 
        have "mset \<Psi> \<subseteq># mset (remove1 \<sigma> \<Gamma>)"
          using \<open>\<sigma> \<notin> set \<Psi>\<close> \<open>mset (remove1 \<sigma> \<Psi>) \<subseteq># mset (remove1 \<sigma> \<Gamma>)\<close>
          by (simp add: remove1_idem)
        ultimately show ?thesis
          by (metis Cons.hyps 
                    \<open>mset \<Sigma> \<subseteq># mset (remove1 \<sigma> \<Gamma>)\<close> 
                    listSubtract_remove1_cons_perm 
                    mset_eq_perm)
      qed
    }
    then show ?case by blast
  qed
  with assms show ?thesis by blast
qed
          
lemma listSubtract_cancel_strong_upper_bound:
  assumes "\<psi> \<in># mset \<Psi>"
          "\<psi> \<notin># mset \<Sigma>"
          "mset \<Psi> \<subseteq># mset \<Gamma>"
          "mset \<Sigma> \<subseteq># mset \<Gamma>"
    shows "mset ((\<Gamma> \<ominus> \<Psi>) \<ominus> (\<Sigma> \<ominus> \<Psi>)) \<subset># mset (\<Gamma> \<ominus> \<Sigma>)"
proof -
  have "\<forall> \<Gamma> \<Psi>.
          \<psi> \<in># mset \<Psi> \<longrightarrow>
          \<psi> \<notin># mset \<Sigma> \<longrightarrow> 
          mset \<Psi> \<subseteq># mset \<Gamma> \<longrightarrow> 
          mset \<Sigma> \<subseteq># mset \<Gamma> \<longrightarrow>
          mset ((\<Gamma> \<ominus> \<Psi>) \<ominus> (\<Sigma> \<ominus> \<Psi>)) \<subset># mset (\<Gamma> \<ominus> \<Sigma>)"
  proof (induct \<Sigma>)
    case Nil
    {
      fix \<Gamma> \<Psi> :: "'a list"
      assume "\<psi> \<in># mset \<Psi>"
             "mset \<Psi> \<subseteq># mset \<Gamma>"
      moreover from this have "mset (\<Gamma> \<ominus> \<Psi>) \<subseteq># mset \<Gamma> - {# \<psi> #}"
        by (smt add_mset_diff_bothsides 
                diff_subset_eq_self 
                insert_DiffM 
                listSubtract_mset_homomorphism 
                mset_subset_eqD)
      ultimately have "mset (\<Gamma> \<ominus> \<Psi>) \<subset># mset \<Gamma>" 
        by (meson mset_subset_diff_self mset_subset_eqD subset_mset.le_less_trans)
      hence "mset ((\<Gamma> \<ominus> \<Psi>) \<ominus> ([] \<ominus> \<Psi>)) \<subset># mset (\<Gamma> \<ominus> [])"
        by simp
    } 
    thus ?case by simp 
  next
    case (Cons \<sigma> \<Sigma>)
    {
      fix \<Gamma> \<Psi> :: "'a list"
      assume "\<psi> \<in># mset \<Psi>"
             "\<psi> \<notin># mset (\<sigma> # \<Sigma>)"
             "mset (\<sigma> # \<Sigma>) \<subseteq># mset \<Gamma>"
             "mset \<Psi> \<subseteq># mset \<Gamma>"
      hence "mset \<Sigma> \<subseteq># mset (remove1 \<sigma> \<Gamma>)" 
            "\<psi> \<notin># mset \<Sigma>"
            "mset (remove1 \<sigma> \<Psi>) \<subseteq># mset (remove1 \<sigma> \<Gamma>)"
        by (simp add: insert_subset_eq_iff, 
            auto, 
            metis ex_mset listSubtract_monotonic listSubtract_mset_homomorphism)
      have "mset ((\<Gamma> \<ominus> \<Psi>) \<ominus> ((\<sigma> # \<Sigma>) \<ominus> \<Psi>)) \<subset># mset (\<Gamma> \<ominus> (\<sigma> # \<Sigma>))"
      proof (cases "\<sigma> \<in> set \<Psi>")
        assume "\<sigma> \<in> set \<Psi>"
        hence "mset ((\<Gamma> \<ominus> \<Psi>) \<ominus> ((\<sigma> # \<Sigma>) \<ominus> \<Psi>)) = 
               mset (((remove1 \<sigma> \<Gamma>) \<ominus> (remove1 \<sigma> \<Psi>)) \<ominus> (\<Sigma> \<ominus> (remove1 \<sigma> \<Psi>)))"
          by (smt listSubtract_cons_remove1_perm 
                  listSubtract_mset_homomorphism 
                  listSubtract_remove1_perm 
                  mset_eq_perm)
        then show ?thesis
          by (smt Cons.hyps 
                  \<open>\<psi> \<in># mset \<Psi>\<close> 
                  \<open>\<psi> \<notin># mset (\<sigma> # \<Sigma>)\<close> 
                  \<open>\<psi> \<notin># mset \<Sigma>\<close> 
                  \<open>mset (remove1 \<sigma> \<Psi>) \<subseteq># mset (remove1 \<sigma> \<Gamma>)\<close> 
                  \<open>mset \<Sigma> \<subseteq># mset (remove1 \<sigma> \<Gamma>)\<close> 
                  in_multiset_in_set 
                  in_set_remove1 
                  list.set_intros(1) 
                  listSubtract_remove1_cons_perm 
                  mset_eq_perm)
      next
        assume "\<sigma> \<notin> set \<Psi>"
        hence "mset ((\<Gamma> \<ominus> \<Psi>) \<ominus> ((\<sigma> # \<Sigma>) \<ominus> \<Psi>)) = 
               mset (((remove1 \<sigma> \<Gamma>) \<ominus> \<Psi>) \<ominus> (\<Sigma> \<ominus> \<Psi>))"
          by simp
        moreover 
        have "mset \<Psi> \<subseteq># mset (remove1 \<sigma> \<Gamma>)"
          using \<open>\<sigma> \<notin> set \<Psi>\<close> \<open>mset (remove1 \<sigma> \<Psi>) \<subseteq># mset (remove1 \<sigma> \<Gamma>)\<close>
          by (simp add: remove1_idem)
        ultimately show ?thesis
          by (metis (no_types, lifting) 
                    Cons.hyps 
                    \<open>\<psi> \<in># mset \<Psi>\<close> 
                    \<open>\<psi> \<notin># mset \<Sigma>\<close> 
                    \<open>mset \<Sigma> \<subseteq># mset (remove1 \<sigma> \<Gamma>)\<close> 
                    listSubtract_remove1_cons_perm 
                    mset_eq_perm) 
      qed
    }
    then show ?case by simp
  qed
  thus ?thesis using assms by blast
qed
  
lemma (in Minimal_Logic) unproving_core_max_list_deduction:
  "\<Gamma> :\<turnstile> \<phi> = (\<forall> \<Phi> \<in> \<CC> \<Gamma> \<phi>. 1 \<le> length (\<Gamma> \<ominus> \<Phi>))"
proof cases
  assume "\<turnstile> \<phi>"
  hence "\<Gamma> :\<turnstile> \<phi>" "\<CC> \<Gamma> \<phi> = {}"
    unfolding unproving_core_def
    by (simp add: stratified_deduction_weaken list_deduction_weaken)+
  then show ?thesis by blast
next
  assume "\<not> \<turnstile> \<phi>"
  from this obtain \<Omega> where \<Omega>: "\<Omega> \<in> \<CC> \<Gamma> \<phi>"
    using unproving_core_existance by blast
  from this have "mset \<Omega> \<subseteq># mset \<Gamma>"
    unfolding unproving_core_def by blast
  hence \<diamondsuit>: "length (\<Gamma> \<ominus> \<Omega>) = length \<Gamma> - length \<Omega>"
    by (metis listSubtract_mset_homomorphism 
              size_Diff_submset 
              size_mset)
  show ?thesis
  proof (cases "\<Gamma> :\<turnstile> \<phi>")
    assume "\<Gamma> :\<turnstile> \<phi>"
    from \<Omega> have "mset \<Omega> \<subset># mset \<Gamma>"
      by (metis (no_types, lifting) 
                Diff_cancel 
                Diff_eq_empty_iff 
                \<open>\<Gamma> :\<turnstile> \<phi>\<close> 
                list_deduction_monotonic 
                unproving_core_def 
                mem_Collect_eq 
                mset_eq_setD 
                subset_mset.dual_order.not_eq_order_implies_strict)
    hence "length \<Omega> < length \<Gamma>"
      using mset_subset_size by fastforce
    hence "1 \<le> length \<Gamma> - length \<Omega>"
      by (simp add: Suc_leI)
    with \<diamondsuit> have "1 \<le> length (\<Gamma> \<ominus> \<Omega>)"
      by simp
    with \<open>\<Gamma> :\<turnstile> \<phi>\<close> \<Omega> show ?thesis
      by (metis unproving_listSubtract_length_equiv) 
  next
    assume "\<not> \<Gamma> :\<turnstile> \<phi>"
    moreover have "mset \<Gamma> \<subseteq># mset \<Gamma>"
      by simp
    moreover have "length \<Omega> \<le> length \<Gamma>"
      using \<open>mset \<Omega> \<subseteq># mset \<Gamma>\<close> length_sub_mset mset_eq_length 
      by fastforce  
    ultimately have "length \<Omega> = length \<Gamma>"
      using \<Omega>
      unfolding unproving_core_def
      by (simp add: dual_order.antisym)
    hence "1 > length (\<Gamma> \<ominus> \<Omega>)"
      using \<diamondsuit>
      by simp
    with \<open>\<not> \<Gamma> :\<turnstile> \<phi>\<close> \<Omega> show ?thesis
      by fastforce
  qed
qed

lemma listSubtract_msub_eq:
  assumes "mset \<Phi> \<subseteq># mset \<Gamma>"
      and "length (\<Gamma> \<ominus> \<Phi>) = m"
    shows "length \<Gamma> = m + length \<Phi>"
  using assms
proof - 
  have "\<forall> \<Gamma>. mset \<Phi> \<subseteq># mset \<Gamma> \<longrightarrow> length (\<Gamma> \<ominus> \<Phi>) = m \<longrightarrow> length \<Gamma> = m + length \<Phi>"
  proof (induct \<Phi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<phi> \<Phi>)
    {
      fix \<Gamma> :: "'a list"
      assume "mset (\<phi> # \<Phi>) \<subseteq># mset \<Gamma>"
             "length (\<Gamma> \<ominus> (\<phi> # \<Phi>)) = m"
      moreover from this have "mset \<Phi> \<subseteq># mset (remove1 \<phi> \<Gamma>)"
                              "mset (\<Gamma> \<ominus> (\<phi> # \<Phi>)) = mset ((remove1 \<phi> \<Gamma>) \<ominus> \<Phi>)"
        by (metis append_Cons mset_le_perm_append perm_remove_perm remove_hd, simp)
      ultimately have "length (remove1 \<phi> \<Gamma>) = m + length \<Phi>"
        using Cons.hyps
        by (metis mset_eq_length)
      hence "length (\<phi> # (remove1 \<phi> \<Gamma>)) = m + length (\<phi> # \<Phi>)"
        by simp
      moreover have "\<phi> \<in> set \<Gamma>"
        by (metis \<open>mset (\<Gamma> \<ominus> (\<phi> # \<Phi>)) = mset (remove1 \<phi> \<Gamma> \<ominus> \<Phi>)\<close> 
                  \<open>mset (\<phi> # \<Phi>) \<subseteq># mset \<Gamma>\<close> 
                  \<open>mset \<Phi> \<subseteq># mset (remove1 \<phi> \<Gamma>)\<close> 
                  add_diff_cancel_left' 
                  add_right_cancel 
                  eq_iff 
                  impossible_Cons 
                  listSubtract_mset_homomorphism 
                  mset_subset_eq_exists_conv 
                  remove1_idem size_mset)
      hence "length (\<phi> # (remove1 \<phi> \<Gamma>)) = length \<Gamma>"
        by (metis One_nat_def Suc_pred length_Cons length_pos_if_in_set length_remove1)
      ultimately have "length \<Gamma> = m + length (\<phi> # \<Phi>)" by simp
    }
    thus ?case by blast
  qed
  thus ?thesis using assms by blast
qed

lemma (in Minimal_Logic) unproving_core_complement_monotonic:
  assumes "mset \<Sigma> \<subseteq># mset \<Gamma>"
      and "\<Phi> \<in> \<CC> \<Sigma> \<phi>"
      and "\<Psi> \<in> \<CC> \<Gamma> \<phi>"
    shows "length (\<Sigma> \<ominus> \<Phi>) \<le> length (\<Gamma> \<ominus> \<Psi>)"
proof -
  from \<open>mset \<Sigma> \<subseteq># mset \<Gamma>\<close> have \<heartsuit>: "mset \<Sigma> = mset (\<Gamma> \<ominus> (\<Gamma> \<ominus> \<Sigma>))"
    by (simp add: add_implies_diff) 
  have "mset \<Psi> \<subseteq># mset \<Gamma>" 
    using \<open>\<Psi> \<in> \<CC> \<Gamma> \<phi>\<close>
    unfolding unproving_core_def
    by blast
  with \<heartsuit> have \<diamondsuit>: "mset (\<Psi> \<ominus> (\<Gamma> \<ominus> \<Sigma>)) \<subseteq># mset \<Sigma>"
    by (metis listSubtract_monotonic)
  from \<open>\<Psi> \<in> \<CC> \<Gamma> \<phi>\<close> have "\<not> \<Psi> \<ominus> (\<Gamma> \<ominus> \<Sigma>) :\<turnstile> \<phi>"
    by (metis (no_types, lifting) 
              listSubtract_set_trivial_upper_bound 
              list_deduction_monotonic 
              unproving_core_def 
              mem_Collect_eq)
  hence "length (\<Psi> \<ominus> (\<Gamma> \<ominus> \<Sigma>)) \<le> length \<Phi>"
        "mset \<Phi> \<subseteq># mset \<Sigma>"
    using \<diamondsuit> \<open>\<Phi> \<in> \<CC> \<Sigma> \<phi>\<close>
    unfolding unproving_core_def
    by blast+
  hence "length (\<Sigma> \<ominus> \<Phi>) \<le> length (\<Sigma> \<ominus> (\<Psi> \<ominus> (\<Gamma> \<ominus> \<Sigma>)))"
    using \<diamondsuit>
    by (metis add_le_cancel_right listSubtract_msub_eq nat_add_left_cancel_le)
  hence "length (\<Sigma> \<ominus> \<Phi>) \<le> length ((\<Gamma> \<ominus> (\<Gamma> \<ominus> \<Sigma>)) \<ominus> (\<Psi> \<ominus> (\<Gamma> \<ominus> \<Sigma>)))"
    using \<heartsuit> \<diamondsuit>
    by (metis listSubtract_mset_homomorphism size_mset)
  moreover have "mset (\<Gamma> \<ominus> \<Sigma>) \<subseteq># mset \<Gamma>"
    by simp
  with \<open>mset \<Psi> \<subseteq># mset \<Gamma>\<close> have 
    "length ((\<Gamma> \<ominus> (\<Gamma> \<ominus> \<Sigma>)) \<ominus> (\<Psi> \<ominus> (\<Gamma> \<ominus> \<Sigma>))) \<le> length (\<Gamma> \<ominus> \<Psi>)"
    by (metis listSubtract_cancel_weak_upper_bound size_mset size_mset_mono)
  ultimately show ?thesis by auto
qed 
  
lemma (in Minimal_Logic) unproving_core_stratified_deduction_lower_bound:
  assumes "\<Gamma> #\<turnstile> n \<phi>"
      and "\<Phi> \<in> \<CC> \<Gamma> \<phi>"
    shows "n \<le> length (\<Gamma> \<ominus> \<Phi>)"
proof cases
  assume "\<turnstile> \<phi>"
  hence "\<Gamma> #\<turnstile> n \<phi>" "\<CC> \<Gamma> \<phi> = {}"
    unfolding unproving_core_def
    by (simp add: stratified_deduction_weaken list_deduction_weaken)+
  then show ?thesis using assms by blast
next
  assume "\<not> \<turnstile> \<phi>"
  have "\<forall> \<Gamma>. \<Gamma> #\<turnstile> n \<phi> \<longrightarrow> (\<forall> \<Phi> \<in> \<CC> \<Gamma> \<phi>. n \<le> length (\<Gamma> \<ominus> \<Phi>))"
  proof (induct n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    {
      fix \<Gamma>
      assume "\<Gamma> #\<turnstile> (Suc n) \<phi>"
      from this obtain \<Psi> where \<Psi>: 
          "mset \<Psi> \<subseteq># mset \<Gamma>" 
          "\<Psi> :\<turnstile> \<phi>" 
          "\<Gamma> \<ominus> \<Psi> #\<turnstile> n \<phi>"
          "\<Psi> \<noteq> []"
          using stratified_deduction.simps(2)
                \<open>\<not> \<turnstile> \<phi>\<close> 
                list_deduction_base_theory 
          by blast
      from \<open>\<not> \<turnstile> \<phi>\<close> obtain \<Sigma> where \<Sigma>: "\<Sigma> \<in> \<CC> \<Gamma> \<phi>"
        using unproving_core_existance by blast
      from this have "mset \<Sigma> \<subseteq># mset \<Gamma>"
        unfolding unproving_core_def by blast
      hence \<diamondsuit>: "length (\<Gamma> \<ominus> \<Sigma>) = length \<Gamma> - length \<Sigma>"
        by (metis listSubtract_mset_homomorphism 
                  size_Diff_submset 
                  size_mset)
      from \<Sigma> \<Psi>(2) have "\<not> (mset \<Psi> \<subseteq># mset \<Sigma>)"
        using stratified_deduction_monotonic 
              stratified_one_deduction 
              unproving_core_def 
        by blast
      from this obtain \<psi> where "\<psi> \<in># mset \<Psi>" "\<psi> \<in># mset (\<Psi> \<ominus> \<Sigma>)"
        by (simp, metis Diff_eq_empty_iff_mset 
                        last_in_set 
                        listSubtract_mset_homomorphism 
                        listSubtract_set_trivial_upper_bound 
                        mset.simps(1) 
                        set_mset_mset 
                        subset_iff)
      with \<Psi>(1) have "\<psi> \<in># mset (\<Gamma> \<ominus> \<Sigma>)"
        by (meson listSubtract_monotonic mset_subset_eqD)
      hence "\<psi> \<in> set (\<Gamma> \<ominus> \<Sigma>)"
        using set_mset_mset by fastforce
      hence "\<psi> \<notin> set \<Sigma>"
        using \<Sigma> by auto
      hence "\<psi> \<notin># mset \<Sigma>"
        by simp
      moreover 
      from \<Sigma> have "\<not> (\<Sigma> \<ominus> \<Psi>) :\<turnstile> \<phi>"
                  "mset (\<Sigma> \<ominus> \<Psi>) \<subseteq># mset (\<Gamma> \<ominus> \<Psi>)"
        apply (metis (no_types, lifting) 
                     listSubtract_set_trivial_upper_bound 
                     list_deduction_monotonic 
                     unproving_core_def 
                     mem_Collect_eq)
        using \<Sigma> listSubtract_monotonic local.unproving_core_def 
        by blast          
      with \<open>\<not> \<turnstile> \<phi>\<close> obtain \<Omega> where \<Omega>: "\<Omega> \<in> \<CC> (\<Gamma> \<ominus> \<Psi>) \<phi>" "length (\<Sigma> \<ominus> \<Psi>) \<le> length \<Omega>"
        by (metis (no_types, lifting) 
                  unproving_core_def 
                  unproving_core_existance 
                  mem_Collect_eq)
      hence "n \<le> length ((\<Gamma> \<ominus> \<Psi>) \<ominus> \<Omega>)"
        using Suc.hyps \<Psi>(3) by blast
      hence "n \<le> length (\<Gamma> \<ominus> \<Psi>) - length \<Omega>"
        by (metis (no_types, lifting) 
                  \<Omega>(1) 
                  listSubtract_mset_homomorphism 
                  unproving_core_def 
                  mem_Collect_eq 
                  size_Diff_submset size_mset)
      hence "n \<le> length (\<Gamma> \<ominus> \<Psi>) - length (\<Sigma> \<ominus> \<Psi>)"
        using \<Omega>(2) diff_le_mono2 order_trans by blast
      hence "n \<le> length ((\<Gamma> \<ominus> \<Psi>) \<ominus> (\<Sigma> \<ominus> \<Psi>))"
        by (metis \<open>mset (\<Sigma> \<ominus> \<Psi>) \<subseteq># mset (\<Gamma> \<ominus> \<Psi>)\<close> 
                  listSubtract_mset_homomorphism 
                  size_Diff_submset size_mset)
      hence "n \<le> length ((\<Gamma> \<ominus> \<Psi>) \<ominus> (\<Sigma> \<ominus> \<Psi>))"
        using \<Omega>(2) msubset_listSubtract_length_antitonic [where \<Gamma>="\<Gamma> \<ominus> \<Psi>"
                                                            and \<Psi>="\<Omega>"
                                                            and \<Phi>="\<Sigma> \<ominus> \<Psi>"]
        by linarith
      moreover
      have "mset \<Sigma> \<subseteq># mset \<Gamma>" 
        using \<Sigma>(1) local.unproving_core_def by blast
      hence "length ((\<Gamma> \<ominus> \<Psi>) \<ominus> (\<Sigma> \<ominus> \<Psi>)) < length (\<Gamma> \<ominus> \<Sigma>)"
        by (metis \<Psi>(1) 
                  \<open>\<psi> \<in># mset \<Psi>\<close> 
                  \<open>\<psi> \<notin># mset \<Sigma>\<close> 
                  listSubtract_cancel_strong_upper_bound 
                  length_sub_mset 
                  not_le_imp_less 
                  subset_mset.less_imp_le 
                  subset_mset.less_imp_neq)
      ultimately have "Suc n \<le> length (\<Gamma> \<ominus> \<Sigma>)"
        by linarith
      hence "\<forall>\<Phi>\<in>\<CC> \<Gamma> \<phi>. Suc n \<le> length (\<Gamma> \<ominus> \<Phi>)" using \<Sigma>(1)
        by (metis local.unproving_listSubtract_length_equiv)
    }
    then show ?case by blast
  qed
  with assms show ?thesis by blast
qed

lemma (in Minimal_Logic) unproving_core_max_stratified_deduction:
  "\<Gamma> #\<turnstile> n \<phi> = (\<forall> \<Phi> \<in> \<CC> \<Gamma> \<phi>. n \<le> length (\<Gamma> \<ominus> \<Phi>))"
proof -
  {
    assume "n = 0"
    hence ?thesis by simp
  }
  moreover
  {
    assume "n = 1"
    hence ?thesis
      using stratified_one_deduction 
            unproving_core_max_list_deduction 
      by blast
  }
  moreover
  {
    assume "\<turnstile> \<phi>"
    hence "\<Gamma> #\<turnstile> n \<phi>" "\<CC> \<Gamma> \<phi> = {}"
      unfolding unproving_core_def
      by (simp add: stratified_deduction_weaken list_deduction_weaken)+
    hence ?thesis by blast
  }
  moreover
  {
    assume "n > 1" "\<not> \<turnstile> \<phi>"
    have "\<forall> \<Gamma>. (\<forall> \<Phi> \<in> \<CC> \<Gamma> \<phi>. n \<le> length (\<Gamma> \<ominus> \<Phi>)) \<longrightarrow> \<Gamma> #\<turnstile> n \<phi>"
    proof (induct n)
      case 0
      then show ?case by simp
    next
      case (Suc n)
      {
        fix \<Gamma>
        assume "\<forall> \<Phi> \<in> \<CC> \<Gamma> \<phi>. Suc n \<le> length (\<Gamma> \<ominus> \<Phi>)"
        with \<open>\<not> \<turnstile> \<phi>\<close> obtain \<Sigma> where \<Sigma>: "\<Sigma> \<in> \<CC> \<Gamma> \<phi>" "Suc n \<le> length (\<Gamma> \<ominus> \<Sigma>)"
          using unproving_core_existance by blast
        have "\<Gamma> #\<turnstile> (Suc n) \<phi>"
        proof (rule ccontr)
          assume "\<not> \<Gamma> #\<turnstile> (Suc n) \<phi>"
          hence "\<forall> \<Phi>. mset \<Phi> \<subseteq># mset \<Gamma> \<longrightarrow> \<Phi> :\<turnstile> \<phi> \<longrightarrow> 
                      (\<exists> \<Psi> \<in> \<CC> (\<Gamma> \<ominus> \<Phi>) \<phi>. n > length ((\<Gamma> \<ominus> \<Phi>) \<ominus> \<Psi>))"
            by (meson Suc.hyps local.stratified_deduction.simps(2) not_less)
          hence "\<forall> \<Phi>. mset \<Phi> \<subseteq># mset \<Gamma> \<longrightarrow> \<Phi> :\<turnstile> \<phi> \<longrightarrow> 
                      (\<exists> \<Psi> \<in> \<CC> (\<Gamma> \<ominus> \<Phi>) \<phi>. length \<Psi> + n > length (\<Gamma> \<ominus> \<Phi>))"
            by (metis (no_types, lifting) add.commute 
                                          add_less_mono1 
                                          listSubtract_msub_eq 
                                          local.unproving_core_def 
                                          mem_Collect_eq)
            
          show "False" sorry
        qed
      }
      then show ?case by blast
    qed
    hence ?thesis
      using unproving_core_stratified_deduction_lower_bound 
      by blast
  }
  ultimately show ?thesis
    by (meson less_one linorder_neqE_nat)
qed
  


(* TODO: strengthen to Minimal_Logic *)
lemma (in Classical_Propositional_Logic) stratified_deduction_limit:
  assumes "\<not> \<turnstile> \<sim> \<phi>"
  shows "\<not> (\<Gamma> #\<turnstile> ((length \<Gamma>) + 1) (\<sim> \<phi>))"
proof -
  from assms obtain \<Omega> where \<Omega>: "MCS \<Omega>" "\<phi> \<in> \<Omega>"
    unfolding negation_def
    by (meson insert_subset 
              Formula_Consistent_def 
              Formula_Maximal_Consistency 
              Formula_Maximally_Consistent_Extension 
              set_deduction_base_theory 
              set_deduction_theorem)
  let ?Pr = "\<lambda> \<chi>. if \<chi>\<in>\<Omega> then (1 :: real) else 0"
  from \<Omega> have "?Pr \<in> Binary_Probabilities"
    using MCS_Binary_Weakly_Additive_Logical_Probability by blast
  from this interpret Weakly_Additive_Logical_Probability "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(op \<rightarrow>)" "\<bottom>" "?Pr"
      unfolding Binary_Probabilities_def
      by auto
  {
    assume "\<Gamma> #\<turnstile> ((length \<Gamma>) + 1) (\<sim> \<phi>)"
    hence "\<^bold>\<sim> (\<^bold>\<sim> \<Gamma>) #\<turnstile> ((length \<Gamma>) + 1) (\<sim> \<phi>)"
      using stratified_deduction_double_negation_equivalence by blast
    hence "(real ((length \<Gamma>) + 1)) * ?Pr \<phi> \<le> (\<Sum>\<gamma>\<leftarrow>(\<^bold>\<sim> \<Gamma>). ?Pr \<gamma>)"
      using stratified_deduction_implies_probability_inequality by blast
    with \<Omega> have "real (length \<Gamma>) + 1 \<le> (\<Sum>\<gamma>\<leftarrow>(\<^bold>\<sim> \<Gamma>). ?Pr \<gamma>)"
      by simp
    hence "real (length \<Gamma>) + 1 \<le> real (length (\<^bold>\<sim> \<Gamma>))"
      by (induct \<Gamma>, simp, simp, smt)
    moreover have "length \<Gamma> = length (\<^bold>\<sim> \<Gamma>)"
      by simp
    ultimately have "False"
      by linarith
  }
  thus ?thesis by blast
qed

(* TODO: strengthen to Minimal_Logic *)  
lemma (in Classical_Propositional_Logic) Stratified_Deduction_Collapse:
  "(\<forall> n. \<Gamma> #\<turnstile> n \<phi>) = \<turnstile> \<phi>"
proof -
  {
    assume "\<turnstile> \<phi>"
    hence "\<forall>n. \<Gamma> #\<turnstile> n \<phi>"
      by (simp add: stratified_deduction_weaken)
  }
  moreover
  {
    assume "\<not> \<turnstile> \<phi>"
    hence "\<not> \<turnstile> \<sim> (\<sim> \<phi>)" by simp
    hence "\<not> (\<forall>n. \<Gamma> #\<turnstile> n (\<sim> (\<sim> \<phi>)))"
      using stratified_deduction_limit by blast
    moreover have "\<turnstile> \<phi> \<leftrightarrow> \<sim> (\<sim> \<phi>)"
      using biconditional_def double_negation_biconditional by auto
    ultimately have "\<not> (\<forall>n. \<Gamma> #\<turnstile> n \<phi>)"
      by (metis local.stratified_deduction_substitution)
  }
  ultimately show ?thesis by blast
qed  
  
lemma (in Minimal_Logic) unproving_core_length_bound:
  assumes "\<not> \<Gamma> #\<turnstile> n \<phi>"
      and "\<Phi> \<in> \<CC> \<Gamma> \<phi>"
    shows "n > length (\<Gamma> \<ominus> \<Phi>)"
  using assms
  by (metis unproving_core_max_stratified_deduction 
            unproving_listSubtract_length_equiv 
            not_le)

theorem (in Classical_Propositional_Logic)
  "\<^bold>\<sim> \<Gamma> #\<turnstile> n (\<sim> \<phi>) = (\<forall> Pr \<in> Binary_Probabilities. real n * Pr \<phi> \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>))"
proof -
  {
    fix Pr :: "'a \<Rightarrow> real"
    assume "Pr \<in> Binary_Probabilities"
    from this interpret Weakly_Additive_Logical_Probability "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(op \<rightarrow>)" "\<bottom>" "Pr"
      unfolding Binary_Probabilities_def
      by auto
    assume "\<^bold>\<sim> \<Gamma> #\<turnstile> n (\<sim> \<phi>)"
    hence "real n * Pr \<phi> \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
      using stratified_deduction_implies_probability_inequality 
      by blast
  }
  moreover
  {
    assume "\<not> \<^bold>\<sim> \<Gamma> #\<turnstile> n (\<sim> \<phi>)"
    have "\<exists> Pr \<in> Binary_Probabilities. real n * Pr \<phi> > (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
    proof -
      from \<open>\<not> \<^bold>\<sim> \<Gamma> #\<turnstile> n (\<sim> \<phi>)\<close> have "\<exists>\<Phi>. \<Phi> \<in> \<CC> (\<^bold>\<sim> \<Gamma>) (\<sim> \<phi>)"
        using unproving_core_max_stratified_deduction by blast
      from this obtain \<Phi> where \<Phi>: "(\<^bold>\<sim> \<Phi>) \<in> \<CC> (\<^bold>\<sim> \<Gamma>) (\<sim> \<phi>)" "mset \<Phi> \<subseteq># mset \<Gamma>"
        by (metis (mono_tags, lifting) unproving_core_def 
                                       mem_Collect_eq 
                                       mset_sub_map_list_exists)
      hence "\<not> \<turnstile> \<phi> \<rightarrow> \<Squnion> \<Phi>"
        using biconditional_weaken 
              list_deduction_def 
              map_negation_list_implication 
              set_deduction_base_theory 
              unproving_core_def 
        by blast
      from this obtain \<Omega> where \<Omega>: "MCS \<Omega>" "\<phi> \<in> \<Omega>" "\<Squnion> \<Phi> \<notin> \<Omega>"
        by (meson insert_subset 
                  Formula_Consistent_def 
                  Formula_Maximal_Consistency 
                  Formula_Maximally_Consistent_Extension 
                  Formula_Maximally_Consistent_Set_def 
                  set_deduction_base_theory 
                  set_deduction_reflection 
                  set_deduction_theorem)
      let ?Pr = "\<lambda> \<chi>. if \<chi>\<in>\<Omega> then (1 :: real) else 0"
      from \<Omega> have "?Pr \<in> Binary_Probabilities"
        using MCS_Binary_Weakly_Additive_Logical_Probability by blast
      moreover
      from this interpret Weakly_Additive_Logical_Probability "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(op \<rightarrow>)" "\<bottom>" "?Pr"
        unfolding Binary_Probabilities_def
        by auto
      have "\<forall> \<phi> \<in> set \<Phi>. ?Pr \<phi> = 0"
        using \<Phi>(1) \<Omega>(1) \<Omega>(3) arbitrary_disjunction_exclusion_MCS by auto 
      with \<Phi>(2) have "(\<Sum>\<gamma>\<leftarrow>\<Gamma>. ?Pr \<gamma>) = (\<Sum>\<gamma>\<leftarrow>(\<Gamma> \<ominus> \<Phi>). ?Pr \<gamma>)"
        by (induct \<Phi>, simp, simp,
            smt add_mset_remove_trivial 
                diff_subset_eq_self 
                remove1_idem 
                subset_mset.dual_order.trans 
                sum_list_map_remove1)
      hence "(\<Sum>\<gamma>\<leftarrow>\<Gamma>. ?Pr \<gamma>) \<le> real (length (\<Gamma> \<ominus> \<Phi>))"
        using list_probability_upper_bound 
        by auto
      moreover
      have "length (\<^bold>\<sim> \<Gamma> \<ominus> \<^bold>\<sim> \<Phi>) < n"
        using \<Phi>(1) \<open>\<not> (\<^bold>\<sim> \<Gamma>) #\<turnstile> n (\<sim> \<phi>)\<close> unproving_core_length_bound by blast
      hence "real (length (\<^bold>\<sim> \<Gamma> \<ominus> \<^bold>\<sim> \<Phi>)) < real n"
        by simp
      with \<Omega>(2) have "real (length (\<^bold>\<sim> \<Gamma> \<ominus> \<^bold>\<sim> \<Phi>)) < real n * ?Pr \<phi>"
        by simp
      moreover
      have "(\<^bold>\<sim> (\<Gamma> \<ominus> \<Phi>)) <~~> (\<^bold>\<sim> \<Gamma> \<ominus> \<^bold>\<sim> \<Phi>)"
        by (metis \<Phi>(2) map_listSubtract_mset_equivalence mset_eq_perm)
      with perm_length have "length (\<Gamma> \<ominus> \<Phi>) = length (\<^bold>\<sim> \<Gamma> \<ominus> \<^bold>\<sim> \<Phi>)"
        by fastforce
      hence "real (length (\<Gamma> \<ominus> \<Phi>)) = real (length (\<^bold>\<sim> \<Gamma> \<ominus> \<^bold>\<sim> \<Phi>))"
        by simp
      ultimately show ?thesis
        by force 
    qed
  }
  ultimately show ?thesis
    by force 
qed
  
(* TODO: Use this stuff to prove Binary Probabilities are Kolmogorov 
  
definition (in Minimal_Logic) Logical_Extensions :: "('a \<Rightarrow> bool) set" ("Extensions\<^sub>\<turnstile>")
  where
    "Extensions\<^sub>\<turnstile> = {\<L>. \<forall>\<phi>. \<turnstile> \<phi> \<longrightarrow> \<L> \<phi>}"

lemma (in Minimal_Logic) Logical_Extensions_reflection:
  "(\<lambda> \<phi>. \<turnstile> \<phi>) \<in> Extensions\<^sub>\<turnstile>"
  unfolding Logical_Extensions_def
  by simp

lemma (in Minimal_Logic) Logical_Extensions_deduction_introduction:
  assumes "\<turnstile> \<phi>"
      and "\<L> \<in> Extensions\<^sub>\<turnstile>"
    shows "\<L> \<phi>"
  using assms
  unfolding Logical_Extensions_def
  by simp

lemma (in Classical_Propositional_Logic) Binary_Probabilities_alt_def:
  "Binary_Probabilities = 
   {Pr. \<exists>\<L> \<in> Extensions\<^sub>\<turnstile>. class.Probability \<L> (op \<rightarrow>) \<bottom> Pr \<and> (\<forall>x. Pr x = 0 \<or> Pr x = 1)}"
  using Logical_Extensions_reflection
  unfolding Binary_Probabilities_def
            Logical_Extensions_def  
       
*)
