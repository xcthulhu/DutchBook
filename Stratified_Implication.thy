theory Stratified_Implication
  imports Elementary_Probability_Completeness
          List_Utilities
          "~~/src/HOL/Library/Permutation"
begin      
        
definition (in Classical_Propositional_Logic) 
  stratified :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list list \<Rightarrow> bool" 
  where
    "stratified n \<phi> \<Phi> \<L> \<equiv> length \<L> = n \<and> concat \<L> <~~> \<Phi> \<and> (\<forall> \<Psi> \<in> set \<L>. \<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>)"
    
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
    using assms(1)
    unfolding stratified_def
    by fastforce
  moreover have "\<forall>\<Psi>\<in>set (\<L> \<ominus> [\<Psi>]). \<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
    using assms(1) 
    unfolding stratified_def by auto
  ultimately show ?thesis
    unfolding stratified_def
    by auto
qed
  
lemma (in Probability) stratified_summation:
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
        using \<Psi> hypothesis(2) local.stratified_def by auto
      hence "Pr \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. Pr \<psi>)"
        by (simp add: implication_list_summation_inequality)
      ultimately have 
        "(real (n+1)) * Pr \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. Pr \<psi>) + (\<Sum>\<phi>'\<leftarrow>(\<Phi> \<ominus> \<Psi>). Pr \<phi>')"
        by (smt of_nat_1 of_nat_add semiring_normalization_rules(3))
      moreover
      have "\<Phi> <~~> \<Psi> @ concat \<L>'"
        using \<Psi> hypothesis(2) local.stratified_def perm_sym by fastforce
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