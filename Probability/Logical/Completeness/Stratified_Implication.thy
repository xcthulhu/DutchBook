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

lemma listSubtract_monotone:
  assumes "mset A \<subseteq># mset B"
  shows "mset (A \<ominus> C) \<subseteq># mset (B \<ominus> C)"
  by (simp, meson assms subset_eq_diff_conv subset_mset.dual_order.refl subset_mset.order_trans)

lemma map_monotone:
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

lemma (in Classical_Propositional_Logic) stratified_one_deduction: "\<Gamma> #\<turnstile> 1 \<phi> = \<Gamma> :\<turnstile> \<phi>"
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
          using map_monotone by blast
        from \<Phi> have B: "\<^bold>\<sim> (\<^bold>\<sim> \<Phi>) :\<turnstile> \<phi>"
          using list_deduction_double_negation_equivalence by blast
        from \<Phi> Suc.hyps have C:
          "\<^bold>\<sim> (\<^bold>\<sim> \<Gamma>) \<ominus> \<^bold>\<sim> (\<^bold>\<sim> \<Phi>) #\<turnstile> n \<phi>"
          by (metis stratified_deduction_monotonic 
                    map_listSubtract_mset_containment 
                    map_listSubtract_mset_equivalence 
                    map_monotone)
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
  
lemma (in Classical_Propositional_Logic) stratified_deduction_collapse:
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

definition 
  list_extensions :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a list) set"       (infix "\<bowtie>" 90)
  where
    [simp]: "(\<Phi> \<bowtie> \<Gamma>) = { \<Psi>. mset \<Phi> \<subseteq># mset \<Psi> \<and> mset \<Psi> \<subseteq># mset \<Gamma>}"

definition (in Minimal_Logic) basic_core where
  [simp]: "basic_core \<phi> \<Phi> \<Gamma> = 
           {\<Omega>. \<Omega> \<in> (\<Phi> \<bowtie> \<Gamma>) \<and> \<not> (\<Omega> :\<turnstile> \<phi>) 
               \<and> (\<forall>\<Psi> \<in> (\<Phi> \<bowtie> \<Gamma>). \<not> (\<Psi> :\<turnstile> \<phi>) \<longrightarrow> (length \<Psi> \<le> length \<Omega>))}"

lemma mset_set_weaken:
  assumes "mset A \<subseteq># mset B"
  shows "set A \<subseteq> set B"
proof -
  have "\<forall>A. mset A \<subseteq># mset B \<longrightarrow> set A \<subseteq> set B"
    by (induct B, 
        simp, 
        metis count_eq_zero_iff 
              count_greater_zero_iff 
              not_le 
              set_mset_mset 
              subsetI 
              subseteq_mset_def) 
  with assms show ?thesis by blast
qed
      
lemma (in Minimal_Logic) basic_core_existance:
  "(\<exists> \<Omega>. \<Omega> \<in> basic_core \<phi> \<Phi> \<Gamma>) = (mset \<Phi> \<subseteq># mset \<Gamma> \<and> \<not> (\<Phi> :\<turnstile> \<phi>))"
proof (rule iffI)
  assume "\<exists>\<Omega>. \<Omega> \<in> basic_core \<phi> \<Phi> \<Gamma>"
  from this obtain \<Omega> where \<Omega>:
    "\<not> (\<Omega> :\<turnstile> \<phi>)"
    "mset \<Phi> \<subseteq># mset \<Omega>" 
    "mset \<Omega> \<subseteq># mset \<Gamma>"
    unfolding basic_core_def
    by auto
  thus "mset \<Phi> \<subseteq># mset \<Gamma> \<and> \<not> \<Phi> :\<turnstile> \<phi>"
    using list_deduction_monotonic mset_set_weaken subset_mset.dual_order.trans by blast
next
  have "\<forall>\<Phi> \<phi>. mset \<Phi> \<subseteq># mset \<Gamma> \<and> \<not> \<Phi> :\<turnstile> \<phi> \<longrightarrow> (\<exists>\<Omega>. \<Omega> \<in> basic_core \<phi> \<Phi> \<Gamma>)"
  proof (induct \<Gamma>)
    case Nil
    {
      fix \<Phi>
      fix \<phi>
      assume hypothesis: "mset \<Phi> \<subseteq># mset []" "\<not> \<Phi> :\<turnstile> \<phi>"
      hence "\<Phi> = []" by simp
      with hypothesis have "basic_core \<phi> \<Phi> [] = {[]}" by fastforce
    }
    then show ?case by simp
  next
    case (Cons \<gamma> \<Gamma>)
    {
      fix \<Phi>
      fix \<phi>
      assume hypothesis: "mset \<Phi> \<subseteq># mset (\<gamma> # \<Gamma>)" "\<not> \<Phi> :\<turnstile> \<phi>"
      hence "\<exists>\<Omega>. \<Omega> \<in> basic_core \<phi> \<Phi> (\<gamma> # \<Gamma>)"
      proof cases
        assume assumption: "count (mset \<Phi>) \<gamma> = count (mset (\<gamma> # \<Gamma>)) \<gamma>"
        let ?\<Phi>' = "remove1 \<gamma> \<Phi>"
        show ?thesis
        proof cases
          assume "\<forall> \<Omega> \<in> basic_core \<phi> ?\<Phi>' \<Gamma>. \<Omega> :\<turnstile> \<gamma> \<rightarrow> \<phi>"
          show ?thesis sorry
        next
          assume "\<not> (\<forall> \<Omega> \<in> basic_core \<phi> ?\<Phi>' \<Gamma>. \<Omega> :\<turnstile> \<gamma> \<rightarrow> \<phi>)"
          show ?thesis sorry
      qed
      next
        assume assumption: "count (mset \<Phi>) \<gamma> \<noteq> count (mset (\<gamma> # \<Gamma>)) \<gamma>"
        show ?thesis
        proof cases
          assume "\<forall> \<Omega> \<in> basic_core \<phi> \<Phi> \<Gamma>. \<Omega> :\<turnstile> \<gamma> \<rightarrow> \<phi>"

          then show ?thesis sorry
        next
          assume "\<not> (\<forall> \<Omega> \<in> basic_core \<phi> \<Phi> \<Gamma>. \<Omega> :\<turnstile> \<gamma> \<rightarrow> \<phi>)"
          then show ?thesis sorry
        qed

        hence "count (mset \<Phi>) \<gamma> \<le> count (mset \<Gamma>) \<gamma>"
          by auto
        hence "mset \<Phi> \<subseteq># mset \<Gamma>"
          by (metis count_add_mset hypothesis(1) mset.simps(2) subseteq_mset_def)
          
        then show ?thesis sorry
      qed
    }
    then show ?case by blast
  qed
  moreover assume "mset \<Phi> \<subseteq># mset \<Gamma> \<and> \<not> \<Phi> :\<turnstile> \<phi>"
  ultimately show "\<exists>\<Omega>. \<Omega> \<in> basic_core \<phi> \<Phi> \<Gamma>" by blast
qed
      
    
lemma (in Minimal_Logic) list_deduction_maximal_core:
   "\<forall> \<Omega> \<in> basic_core \<phi> \<Phi> \<Gamma>.
           \<not> (\<Omega> :\<turnstile> \<phi>) \<and> 
           (\<forall> \<Psi> \<in> list_extensions \<Phi> \<Gamma>. \<not> (\<Psi> :\<turnstile> \<phi>) \<longrightarrow> length(\<Psi>) \<le> length(\<Omega>))"
proof (induct \<Gamma>)
  case Nil
  then show ?case
    unfolding basic_core_def
    by simp
next
  case (Cons \<gamma> \<Gamma>)
  then show ?case
    unfolding basic_core_def
    apply simp
      
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
