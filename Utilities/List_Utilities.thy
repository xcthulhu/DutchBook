theory List_Utilities
  imports "~~/src/HOL/Library/Permutation"
begin  

subsection {* Permutations and List Counts *}
  
(* TODO the converse of this is also true, is that useful for anything? *)    
lemma perm_count_list:
  assumes "\<Phi> <~~> \<Psi>"
  shows "count_list \<Phi> \<phi> = count_list \<Psi> \<phi>"
proof -
  have "\<forall>\<Psi>. \<Phi> <~~> \<Psi> \<longrightarrow> count_list \<Phi> \<phi> = count_list \<Psi> \<phi>"
  proof (induct \<Phi>)
    case Nil
    then show ?case 
      by simp
  next
    case (Cons \<chi> \<Phi>)
    {
      fix \<Psi>
      assume "\<chi> # \<Phi> <~~> \<Psi>"
      hence "\<chi> \<in> set \<Psi>"
        using perm_set_eq by fastforce
      hence "\<Psi> <~~> \<chi> # (remove1 \<chi> \<Psi>)"
        by (simp add: perm_remove)
      hence "\<Phi> <~~> (remove1 \<chi> \<Psi>)"
        using \<open>\<chi> # \<Phi> <~~> \<Psi>\<close> perm.trans by auto
      hence \<diamondsuit>: "count_list \<Phi> \<phi> = count_list (remove1 \<chi> \<Psi>) \<phi>"
        using Cons.hyps by blast
      have "count_list (\<chi> # \<Phi>) \<phi> = count_list \<Psi> \<phi>"
      proof cases
        assume "\<chi> = \<phi>"
        hence "count_list (\<chi> # \<Phi>) \<phi> = count_list \<Phi> \<phi> + 1" by simp
        with \<diamondsuit> have "count_list (\<chi> # \<Phi>) \<phi> = count_list (remove1 \<chi> \<Psi>) \<phi> + 1"
          by simp
        moreover from \<open>\<chi> = \<phi>\<close> \<open>\<chi> \<in> set \<Psi>\<close> have "count_list (remove1 \<chi> \<Psi>) \<phi> + 1 = count_list \<Psi> \<phi>"
          by (induct \<Psi>, simp, auto)
        ultimately show ?thesis by simp
      next
        assume "\<chi> \<noteq> \<phi>"
        with \<diamondsuit> have "count_list (\<chi> # \<Phi>) \<phi> = count_list (remove1 \<chi> \<Psi>) \<phi>"
          by simp
        moreover from \<open>\<chi> \<noteq> \<phi>\<close> have "count_list (remove1 \<chi> \<Psi>) \<phi> = count_list \<Psi> \<phi>" 
          by (induct \<Psi>, simp+)
        ultimately show ?thesis by simp
      qed
    }
    then show ?case 
      by blast
  qed
  with assms show ?thesis by blast
qed

subsection {* List Duplicates *}

primrec duplicates :: "'a list \<Rightarrow> 'a set"
  where
    "duplicates [] = {}"
  | "duplicates (x # xs) = (if (x \<in> set xs) then insert x (duplicates xs) else duplicates xs)"

lemma duplicates_subset:
  "duplicates \<Phi> \<subseteq> set \<Phi>"
  by (induct \<Phi>, simp, auto)
    
lemma duplicates_alt_def:
  "duplicates xs = {x. count_list xs x \<ge> 2}"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  assume inductive_hypothesis: "duplicates xs = {x. 2 \<le> count_list xs x}"
  then show ?case 
  proof cases
    assume "x \<in> set xs"
    hence "count_list (x # xs) x \<ge> 2" 
      by (simp, induct xs, simp, simp, blast)
    hence "{y. 2 \<le> count_list (x # xs) y} = insert x {y. 2 \<le> count_list xs y}"
      by (simp,  blast)
    thus ?thesis using inductive_hypothesis \<open>x \<in> set xs\<close>
      by simp 
  next
    assume "x \<notin> set xs"
    hence "{y. 2 \<le> count_list (x # xs) y} = {y. 2 \<le> count_list xs y}"
      by (simp, auto)
    thus ?thesis using inductive_hypothesis \<open>x \<notin> set xs\<close>
      by simp
  qed
qed

subsection {* List Subtraction *}  
  
primrec listSubtract :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "\<ominus>" 70)
  where
      "xs \<ominus> [] = xs"
    | "xs \<ominus> (y # ys) = (remove1 y (xs \<ominus> ys))"

lemma listSubtract_empty [simp]:
  "[] \<ominus> \<Phi> = []"
  by (induct \<Phi>, simp, simp)
    
lemma listSubtract_remove1_cons_perm:
  "\<Phi> \<ominus> (\<phi> # \<Lambda>) <~~> (remove1 \<phi> \<Phi>) \<ominus> \<Lambda>"
  by (induct \<Lambda>, simp, simp, metis perm_remove_perm remove1_commute)

lemma listSubtract_cons:
  assumes "\<phi> \<notin> set \<Lambda>"
  shows "(\<phi> # \<Phi>) \<ominus> \<Lambda> = \<phi> # (\<Phi> \<ominus> \<Lambda>)"
  using assms
  by (induct \<Lambda>, simp, simp, blast)

lemma listSubtract_cons_absorb:
  assumes "count_list \<Phi> \<phi> \<ge> count_list \<Lambda> \<phi>"
  shows "\<phi> # (\<Phi> \<ominus> \<Lambda>) <~~> (\<phi> # \<Phi>) \<ominus> \<Lambda>"
  using assms
proof -
  have "\<forall> \<Phi>. count_list \<Phi> \<phi> \<ge> count_list \<Lambda> \<phi> \<longrightarrow> \<phi> # (\<Phi> \<ominus> \<Lambda>) <~~> (\<phi> # \<Phi>) \<ominus> \<Lambda>"
  proof (induct \<Lambda>)
    case Nil
    thus ?case using listSubtract_cons by fastforce
  next
    case (Cons \<psi> \<Lambda>)
    assume inductive_hypothesis:
           " \<forall>\<Phi>. count_list \<Lambda> \<phi> \<le> count_list \<Phi> \<phi> \<longrightarrow> \<phi> # \<Phi> \<ominus> \<Lambda> <~~> (\<phi> # \<Phi>) \<ominus> \<Lambda>"
    {
      fix \<Phi> :: "'a list"
      assume "count_list (\<psi> # \<Lambda>) \<phi> \<le> count_list \<Phi> \<phi>"
      hence "count_list \<Lambda> \<phi> \<le> count_list (remove1 \<psi> \<Phi>) \<phi>"
        by (smt Suc_eq_plus1 
                count_list.simps(2) 
                le_eq_less_or_eq 
                less_Suc_eq_le 
                linorder_linear 
                order_eq_iff 
                perm_count_list 
                perm_remove 
                remove1_idem)
      hence "\<phi> # ((remove1 \<psi> \<Phi>) \<ominus> \<Lambda>) <~~> (\<phi> # (remove1 \<psi> \<Phi>)) \<ominus> \<Lambda>"
          using inductive_hypothesis by blast
      moreover have "\<phi> # ((remove1 \<psi> \<Phi>) \<ominus> \<Lambda>) <~~> \<phi> # (\<Phi> \<ominus> (\<psi> # \<Lambda>))"
        by (induct \<Lambda>, simp, simp add: perm_remove_perm remove1_commute)
      ultimately have \<star>: "\<phi> # (\<Phi> \<ominus> (\<psi> # \<Lambda>)) <~~> (\<phi> # (remove1 \<psi> \<Phi>)) \<ominus> \<Lambda>"
        by (meson perm.trans perm_sym)
      have "\<phi> # (\<Phi> \<ominus> (\<psi> # \<Lambda>)) <~~> (\<phi> # \<Phi>) \<ominus> (\<psi> # \<Lambda>)"
      proof cases
        assume "\<phi> = \<psi>"
        hence "(\<phi> # \<Phi>) \<ominus> (\<psi> # \<Lambda>) <~~> \<Phi> \<ominus> \<Lambda>"
          using listSubtract_remove1_cons_perm by fastforce
        moreover have "\<phi> \<in> set \<Phi>"
          using \<open>\<phi> = \<psi>\<close> \<open>count_list (\<psi> # \<Lambda>) \<phi> \<le> count_list \<Phi> \<phi>\<close> leD by force 
        hence "\<Phi> \<ominus> \<Lambda> <~~> (\<phi> # (remove1 \<phi> \<Phi>)) \<ominus> \<Lambda>"
          by (induct \<Lambda>, simp add: perm_remove, simp add: perm_remove_perm) 
        ultimately show ?thesis
          using \<star>
          by (metis \<open>\<phi> = \<psi>\<close> mset_eq_perm)    
      next
        assume "\<phi> \<noteq> \<psi>"
        hence "(\<phi> # (remove1 \<psi> \<Phi>)) \<ominus> \<Lambda> <~~> (\<phi> # \<Phi>) \<ominus> (\<psi> # \<Lambda>)"
          by (induct \<Lambda>, simp, simp add: perm_remove_perm remove1_commute)
        then show ?thesis using \<star> by blast 
      qed        
    }
    then show ?case by blast
  qed
  with assms show ?thesis by blast
qed    
    
lemma listSubtract_remove1_perm:
  assumes "\<phi> \<in> set \<Lambda>"
  shows  "\<Phi> \<ominus> \<Lambda> <~~> (remove1 \<phi> \<Phi>) \<ominus> (remove1 \<phi> \<Lambda>)"
  using assms
proof (induct \<Lambda>)
  case Nil
  then show ?case by simp
next
  case (Cons \<psi> \<Lambda>)
  assume "\<phi> \<in> set (\<psi> # \<Lambda>)"
  show "\<Phi> \<ominus> (\<psi> # \<Lambda>) <~~> remove1 \<phi> \<Phi> \<ominus> remove1 \<phi> (\<psi> # \<Lambda>)"
  proof cases
    assume "\<phi> = \<psi>"
    hence "\<Phi> \<ominus> (\<psi> # \<Lambda>) = remove1 \<phi> (\<Phi> \<ominus> \<Lambda>)" and 
          "remove1 \<phi> \<Phi> \<ominus> remove1 \<phi> (\<psi> # \<Lambda>) = (remove1 \<phi> \<Phi>) \<ominus> \<Lambda>" by auto
    then show ?thesis using listSubtract_remove1_cons_perm by auto
  next
    assume "\<phi> \<noteq> \<psi>"
    hence "\<phi> \<in> set \<Lambda>" using \<open>\<phi> \<in> set (\<psi> # \<Lambda>)\<close> by auto
    hence "\<Phi> \<ominus> \<Lambda> <~~> (remove1 \<phi> \<Phi>) \<ominus> (remove1 \<phi> \<Lambda>)"
      using Cons.hyps
      by auto
    hence "\<Phi> \<ominus> (\<psi> # \<Lambda>) <~~> (remove1 \<psi> ((remove1 \<phi> \<Phi>) \<ominus> (remove1 \<phi> \<Lambda>)))"
      by (simp add: perm_remove_perm)  
    moreover have "(remove1 \<phi> \<Phi>) \<ominus> (remove1 \<phi> (\<psi> # \<Lambda>)) = 
                   (remove1 \<psi> ((remove1 \<phi> \<Phi>) \<ominus> (remove1 \<phi> \<Lambda>)))"
      using \<open>\<phi> \<noteq> \<psi>\<close>
        by simp
    ultimately show ?thesis
      by simp 
    qed
qed
  
lemma listSubtract_cons_remove1_perm:
  assumes "\<phi> \<in> set \<Lambda>"
  shows "(\<phi> # \<Phi>) \<ominus> \<Lambda> <~~> \<Phi> \<ominus> (remove1 \<phi> \<Lambda>)"
  using assms listSubtract_remove1_perm by fastforce
    
lemma listSubtract_removeAll_perm:
  assumes "count_list \<Phi> \<phi> \<le> count_list \<Lambda> \<phi>"
  shows "\<Phi> \<ominus> \<Lambda> <~~> (removeAll \<phi> \<Phi>) \<ominus> (removeAll \<phi> \<Lambda>)"
proof -
  have "\<forall> \<Lambda>. count_list \<Phi> \<phi> \<le> count_list \<Lambda> \<phi> \<longrightarrow> \<Phi> \<ominus> \<Lambda> <~~> (removeAll \<phi> \<Phi>) \<ominus> (removeAll \<phi> \<Lambda>)"
  proof (induct \<Phi>)
    case Nil
    thus ?case by auto
  next
    case (Cons \<xi> \<Phi>)
    {
      fix \<Lambda>
      assume "count_list (\<xi> # \<Phi>) \<phi> \<le> count_list \<Lambda> \<phi>"
      hence "\<Phi> \<ominus> \<Lambda> <~~> (removeAll \<phi> \<Phi>) \<ominus> (removeAll \<phi> \<Lambda>)"
        by (metis Cons.hyps count_list.simps(2) dual_order.trans le_add_same_cancel1 zero_le_one)
      have "(\<xi> # \<Phi>) \<ominus> \<Lambda> <~~> (removeAll \<phi> (\<xi> # \<Phi>)) \<ominus> (removeAll \<phi> \<Lambda>)"
      proof cases
        assume "\<xi> = \<phi>"
        hence "count_list \<Phi> \<phi> < count_list \<Lambda> \<phi>"
          using \<open>count_list (\<xi> # \<Phi>) \<phi> \<le> count_list \<Lambda> \<phi>\<close>
          by auto
        hence "count_list \<Phi> \<phi> \<le> count_list (remove1 \<phi> \<Lambda>) \<phi>" by (induct \<Lambda>, simp, auto)
        hence "\<Phi> \<ominus> (remove1 \<phi> \<Lambda>) <~~> removeAll \<phi> \<Phi> \<ominus> removeAll \<phi> (remove1 \<phi> \<Lambda>)"
          using Cons.hyps by blast
        hence "\<Phi> \<ominus> (remove1 \<phi> \<Lambda>) <~~> removeAll \<phi> \<Phi> \<ominus> removeAll \<phi> \<Lambda>"
          by (simp add: filter_remove1 removeAll_filter_not_eq)
        moreover have "\<phi> \<in> set \<Lambda>" and "\<phi> \<in> set (\<phi> # \<Phi>)"
          using \<open>\<xi> = \<phi>\<close>
                \<open>count_list (\<xi> # \<Phi>) \<phi> \<le> count_list \<Lambda> \<phi>\<close>
                gr_implies_not0 
          by fastforce+
        hence "(\<phi> # \<Phi>) \<ominus> \<Lambda> <~~> (remove1 \<phi> (\<phi> # \<Phi>)) \<ominus> (remove1 \<phi> \<Lambda>)"
          by (meson listSubtract_remove1_perm)
        hence "(\<phi> # \<Phi>) \<ominus> \<Lambda> <~~> \<Phi> \<ominus> (remove1 \<phi> \<Lambda>)" by simp
        ultimately show ?thesis using \<open>\<xi> = \<phi>\<close> by auto 
      next
        assume "\<xi> \<noteq> \<phi>"
        show ?thesis
        proof cases
          assume "\<xi> \<in> set \<Lambda>"
          hence "(\<xi> # \<Phi>) \<ominus> \<Lambda> <~~> \<Phi> \<ominus> remove1 \<xi> \<Lambda>"
            by (simp add: listSubtract_cons_remove1_perm)
          moreover have "count_list \<Lambda> \<phi> = count_list (remove1 \<xi> \<Lambda>) \<phi>" 
            using \<open>\<xi> \<noteq> \<phi>\<close> \<open>\<xi> \<in> set \<Lambda>\<close> perm_count_list perm_remove 
            by force
          hence "count_list \<Phi> \<phi> \<le> count_list (remove1 \<xi> \<Lambda>) \<phi>"
            using \<open>\<xi> \<noteq> \<phi>\<close> \<open>count_list (\<xi> # \<Phi>) \<phi> \<le> count_list \<Lambda> \<phi>\<close> by auto
          hence "\<Phi> \<ominus> remove1 \<xi> \<Lambda> <~~> (removeAll \<phi> \<Phi>) \<ominus> (removeAll \<phi> (remove1 \<xi> \<Lambda>))"
            using Cons.hyps by blast
          moreover
          have "(removeAll \<phi> \<Phi>) \<ominus> (removeAll \<phi> (remove1 \<xi> \<Lambda>)) <~~> 
                (removeAll \<phi> \<Phi>) \<ominus> (remove1 \<xi> (removeAll \<phi> \<Lambda>))"
            by (induct \<Lambda>, simp, simp add: filter_remove1 removeAll_filter_not_eq)  
          hence "(removeAll \<phi> \<Phi>) \<ominus> (removeAll \<phi> (remove1 \<xi> \<Lambda>)) <~~>
                 (removeAll \<phi> (\<xi> # \<Phi>)) \<ominus> (removeAll \<phi> \<Lambda>)"
            by (simp add: \<open>\<xi> \<in> set \<Lambda>\<close> 
                          filter_remove1 
                          listSubtract_cons_remove1_perm 
                          perm_sym 
                          removeAll_filter_not_eq)
          ultimately show ?thesis by blast 
        next
          assume "\<xi> \<notin> set \<Lambda>"
          hence "(\<xi> # \<Phi>) \<ominus> \<Lambda> <~~> \<xi> # (\<Phi> \<ominus> \<Lambda>)"
            by (simp add: listSubtract_cons_absorb perm_sym)
          hence "(\<xi> # \<Phi>) \<ominus> \<Lambda> <~~> \<xi> # ((removeAll \<phi> \<Phi>) \<ominus> (removeAll \<phi> \<Lambda>))"
            using \<open>\<Phi> \<ominus> \<Lambda> <~~> removeAll \<phi> \<Phi> \<ominus> removeAll \<phi> \<Lambda>\<close> by blast
          hence "(\<xi> # \<Phi>) \<ominus> \<Lambda> <~~> (\<xi> # (removeAll \<phi> \<Phi>)) \<ominus> (removeAll \<phi> \<Lambda>)"
            by (simp add: \<open>\<xi> \<notin> set \<Lambda>\<close> listSubtract_cons)
          thus ?thesis using \<open>\<xi> \<noteq> \<phi>\<close> by auto 
        qed
      qed
    }
    then show ?case by auto
  qed
  with assms show ?thesis by blast
qed
  
lemma listSubtract_permute:
  assumes "\<Phi> <~~> \<Psi>"
  shows "\<Phi> \<ominus> \<Lambda> <~~> \<Psi> \<ominus> \<Lambda>"
proof -
  {
    fix \<Phi> \<Psi> :: "'a list"
    fix \<phi> :: "'a"
    assume "\<phi> \<in> set \<Phi>"
    hence "\<Phi> \<ominus> \<Psi> <~~> (\<phi> # (remove1 \<phi> \<Phi>)) \<ominus> \<Psi>"
    proof (induct \<Psi>)
      case Nil
      then show ?case 
        by (simp, meson perm_remove) 
    next
      case (Cons \<psi> \<Psi>)
      hence "\<Phi> \<ominus> \<Psi> <~~> (\<phi> # remove1 \<phi> \<Phi>) \<ominus> \<Psi>"
        by blast
      hence "remove1 \<psi> (\<Phi> \<ominus> \<Psi>) <~~> remove1 \<psi> ((\<phi> # remove1 \<phi> \<Phi>) \<ominus> \<Psi>)"
        by (simp add: perm_remove_perm)
      then show ?case
        by simp
    qed
  } note listSubtract_perm_remove = this
  have "\<forall>\<Psi>. \<Phi> <~~> \<Psi> \<longrightarrow> \<Phi> \<ominus> \<Lambda> <~~> \<Psi> \<ominus> \<Lambda>"
  proof (induct \<Phi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<phi> \<Phi>)
    {
      fix \<Psi>
      assume "\<phi> # \<Phi> <~~> \<Psi>"
      moreover from this have "\<phi> \<in> set \<Psi>"
        using perm_set_eq by fastforce
      hence "\<Psi> <~~> \<phi> # (remove1 \<phi> \<Psi>)"
        by (simp add: perm_remove)
      ultimately have \<diamondsuit>: "\<Phi> <~~> (remove1 \<phi> \<Psi>)"
        using perm.trans by auto
      have "(\<phi> # \<Phi>) \<ominus> \<Lambda> <~~> \<Psi> \<ominus> \<Lambda>"
      proof cases
        assume A: "count_list \<Phi> \<phi> \<ge> count_list \<Lambda> \<phi>"
        hence B: "count_list (remove1 \<phi> \<Psi>) \<phi> \<ge> count_list \<Lambda> \<phi>"
          using \<diamondsuit> perm_count_list by fastforce
        from \<diamondsuit> have "\<Phi> \<ominus> \<Lambda> <~~> (remove1 \<phi> \<Psi>) \<ominus> \<Lambda>"
          by (simp add: Cons.hyps)
        hence "\<phi> # (\<Phi> \<ominus> \<Lambda>) <~~> \<phi> # ((remove1 \<phi> \<Psi>) \<ominus> \<Lambda>)"
          by simp
        with A B listSubtract_cons_absorb 
        have "(\<phi> # \<Phi>) \<ominus> \<Lambda> <~~> (\<phi> # (remove1 \<phi> \<Psi>)) \<ominus> \<Lambda>"
          by (metis perm.trans perm_sym)
        thus ?thesis
          by (meson listSubtract_perm_remove perm.trans perm_sym \<open>\<phi> \<in> set \<Psi>\<close>)
      next
        assume "\<not> (count_list \<Phi> \<phi> \<ge> count_list \<Lambda> \<phi>)"
        hence "count_list \<Phi> \<phi> < count_list \<Lambda> \<phi>"
          using not_le by blast
        hence A: "count_list (\<phi> # \<Phi>) \<phi> \<le> count_list \<Lambda> \<phi>"
          by simp
        hence B: "count_list \<Psi> \<phi> \<le> count_list \<Lambda> \<phi>"
          by (metis \<open>\<phi> # \<Phi> <~~> \<Psi>\<close> perm_count_list)
        from A have "(\<phi> # \<Phi>) \<ominus> \<Lambda> <~~> (removeAll \<phi> (\<phi> # \<Phi>)) \<ominus> (removeAll \<phi> \<Lambda>)"
          using listSubtract_removeAll_perm
          by smt
        hence "(\<phi> # \<Phi>) \<ominus> \<Lambda> <~~> (removeAll \<phi> \<Phi>) \<ominus> (removeAll \<phi> \<Lambda>)"
          by simp
        moreover from \<open>count_list \<Phi> \<phi> < count_list \<Lambda> \<phi>\<close>
        have "\<Phi> \<ominus> \<Lambda> <~~> (removeAll \<phi> \<Phi>) \<ominus> (removeAll \<phi> \<Lambda>)"
          using listSubtract_removeAll_perm
          by (simp add: listSubtract_removeAll_perm)
        ultimately have "(\<phi> # \<Phi>) \<ominus> \<Lambda> <~~> \<Phi> \<ominus> \<Lambda>"
          by (metis mset_eq_perm)
        with \<diamondsuit> have "(\<phi> # \<Phi>) \<ominus> \<Lambda> <~~> (remove1 \<phi> \<Psi>) \<ominus> \<Lambda>"
          using Cons.hyps by blast
        hence "(\<phi> # \<Phi>) \<ominus> \<Lambda> <~~> (removeAll \<phi> (remove1 \<phi> \<Psi>)) \<ominus> (removeAll \<phi> \<Lambda>)"
          using \<diamondsuit> \<open>count_list \<Phi> \<phi> < count_list \<Lambda> \<phi>\<close> listSubtract_removeAll_perm
          by (metis less_imp_le perm.trans perm_count_list)
        hence "(\<phi> # \<Phi>) \<ominus> \<Lambda> <~~> (removeAll \<phi> \<Psi>) \<ominus> (removeAll \<phi> \<Lambda>)"
          by (simp add: filter_remove1 removeAll_filter_not_eq)
        with B show ?thesis
          using listSubtract_removeAll_perm
          by (metis perm.trans perm_sym)
      qed
    }
    thus ?case by blast
  qed
  with assms show ?thesis by blast
qed

lemma concat_remove1:
  assumes "\<Psi> \<in> set \<L>"
  shows "concat \<L> <~~> \<Psi> @ concat (\<L> \<ominus> [\<Psi>])"
    using assms
    by (induct \<L>, 
        simp,
        simp,
        metis append.assoc 
              perm.trans 
              perm_append1 
              perm_append_swap)

lemma append_set_containment:
  assumes "a \<in> set A"
      and "A <~~> B @ C"
    shows "a \<in> set B \<or> a \<in> set C"
  using assms
  by (simp add: perm_set_eq)

lemma count_list_append:
  "count_list (A @ B) a = count_list A a + count_list B a"
  by (induct A, simp, simp)
    
lemma append_perm_listSubtract_intro:
  assumes "A <~~> B @ C"
  shows "A \<ominus> C <~~> B"
proof -
  have "\<forall>B C. A <~~> B @ C \<longrightarrow> A \<ominus> C <~~> B"
  proof (induct A)
    case Nil
    then show ?case by simp
  next
    case (Cons a A)
    {
      fix B C
      assume "a # A <~~> B @ C"
             "a \<in> set B"
      hence "a # A <~~> a # (remove1 a B) @ C"
        by (metis perm.Cons perm_remove_perm remove1_append remove_hd)
      hence "A <~~> (remove1 a B) @ C"
        by blast
      hence "A \<ominus> C <~~> remove1 a B"
        by (simp add: Cons.hyps)
      hence "a # (A \<ominus> C) <~~> a # (remove1 a B)"
        by simp
      with \<open>a \<in> set B\<close> have "a # (A \<ominus> C) <~~> B"
        by (meson perm.trans perm_remove perm_sym)
      moreover 
      have "count_list A a \<ge> count_list C a"
        using \<open>A <~~> (remove1 a B) @ C\<close>
              count_list_append
        by (metis add.commute le_add_same_cancel1 less_eq_nat.simps(1) perm_count_list)
      ultimately have "(a # A) \<ominus> C <~~> B"
        by (meson listSubtract_cons_absorb perm.trans perm_sym) 
    }
    then show ?case 
      using append_set_containment 
            perm_append_swap
            listSubtract_cons_remove1_perm 
            Cons 
            perm.trans 
            perm_remove_perm 
            remove1_append 
            remove1_idem 
            remove_hd
      by smt 
  qed
  thus ?thesis using assms by blast
qed
       
lemma listSubtract_concat:
  assumes "\<Psi> \<in> set \<L>"
  shows "concat (\<L> \<ominus> [\<Psi>]) <~~> (concat \<L>) \<ominus> \<Psi>"
  using assms
  by (meson append_perm_listSubtract_intro concat_remove1 perm.trans perm_append_swap perm_sym)

lemma (in comm_monoid_add) perm_list_summation:
  assumes "\<Psi> <~~> \<Phi>"
  shows "(\<Sum>\<psi>'\<leftarrow>\<Psi>. f \<psi>') = (\<Sum>\<phi>'\<leftarrow>\<Phi>. f \<phi>')"
proof -
  have "\<forall> \<Phi>. \<Psi> <~~> \<Phi> \<longrightarrow> (\<Sum>\<psi>'\<leftarrow>\<Psi>. f \<psi>') = (\<Sum>\<phi>'\<leftarrow>\<Phi>. f \<phi>')"
  proof (induct \<Psi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<psi> \<Psi>)
    {
      fix \<Phi>
      assume hypothesis: "\<psi> # \<Psi> <~~> \<Phi>"
      hence "\<Psi> <~~> (remove1 \<psi> \<Phi>)"
        by (metis perm_remove_perm remove_hd)
      hence "(\<Sum>\<psi>' \<leftarrow> \<Psi>. f \<psi>') = (\<Sum>\<phi>' \<leftarrow> (remove1 \<psi> \<Phi>). f \<phi>')"
        using Cons.hyps by blast
      moreover have "\<psi> \<in> set \<Phi>"
        using hypothesis perm_set_eq by fastforce
      hence "(\<Sum>\<phi>' \<leftarrow> (\<psi> # (remove1 \<psi> \<Phi>)). f \<phi>') = (\<Sum>\<phi>'\<leftarrow>\<Phi>. f \<phi>')"
      proof (induct \<Phi>)
        case Nil
        then show ?case by simp
      next
        case (Cons \<phi> \<Phi>)
        show ?case
        proof cases
          assume "\<phi> = \<psi>"
          then show ?thesis by simp
        next
          assume "\<phi> \<noteq> \<psi>"
          hence "\<psi> \<in> set \<Phi>" 
            using Cons.prems by auto
          hence "(\<Sum>\<phi>' \<leftarrow> (\<psi> # (remove1 \<psi> \<Phi>)). f \<phi>') = (\<Sum>\<phi>'\<leftarrow>\<Phi>. f \<phi>')"
            using Cons.hyps by blast
          hence "(\<Sum>\<phi>'\<leftarrow>(\<phi> # \<Phi>). f \<phi>') = (\<Sum>\<phi>' \<leftarrow> (\<psi> # \<phi> # (remove1 \<psi> \<Phi>)). f \<phi>')"
            by (simp add: add.left_commute)
          moreover
          have "(\<psi> # (\<phi> # (remove1 \<psi> \<Phi>))) = (\<psi> # (remove1 \<psi> (\<phi> # \<Phi>)))"
            using \<open>\<phi> \<noteq> \<psi>\<close> by simp
          ultimately show ?thesis
            by simp
        qed
      qed
      ultimately have "(\<Sum>\<psi>'\<leftarrow>(\<psi> # \<Psi>). f \<psi>') = (\<Sum>\<phi>'\<leftarrow>\<Phi>. f \<phi>')"
        by simp   
    }
    then show ?case by blast
  qed
  with assms show ?thesis by blast
qed
  
lemma (in comm_monoid_add) listSubstract_multisubset_list_summation:
  assumes "mset \<Psi> \<subseteq># mset \<Phi>"
  shows "(\<Sum>\<psi>\<leftarrow>\<Psi>. f \<psi>) + (\<Sum>\<phi>'\<leftarrow>(\<Phi> \<ominus> \<Psi>). f \<phi>') = (\<Sum>\<phi>'\<leftarrow>\<Phi>. f \<phi>')"
proof -
  have "\<forall> \<Phi>. mset \<Psi> \<subseteq># mset \<Phi> \<longrightarrow> (\<Sum>\<psi>'\<leftarrow>\<Psi>. f \<psi>') + (\<Sum>\<phi>'\<leftarrow>(\<Phi> \<ominus> \<Psi>). f \<phi>') = (\<Sum>\<phi>'\<leftarrow>\<Phi>. f \<phi>')"
  proof(induct \<Psi>)
    case Nil
    then show ?case
      by simp 
  next
    case (Cons \<psi> \<Psi>)
    {
      fix \<Phi>
      assume hypothesis: "mset (\<psi> # \<Psi>) \<subseteq># mset \<Phi>"
      hence "mset \<Psi> \<subseteq># mset (remove1 \<psi> \<Phi>)"
        by (metis append_Cons mset_le_perm_append perm_remove_perm remove_hd)
      hence 
        "(\<Sum>\<psi>'\<leftarrow> \<Psi>. f \<psi>') + (\<Sum>\<phi>'\<leftarrow>((remove1 \<psi> \<Phi>) \<ominus> \<Psi>). f \<phi>') = (\<Sum>\<phi>'\<leftarrow> (remove1 \<psi> \<Phi>). f \<phi>')"
        using Cons.hyps by blast
      moreover have "(remove1 \<psi> \<Phi>) \<ominus> \<Psi> <~~> \<Phi> \<ominus> (\<psi> # \<Psi>)"
        by (meson listSubtract_remove1_cons_perm perm_sym)
      hence "(\<Sum>\<phi>'\<leftarrow>((remove1 \<psi> \<Phi>) \<ominus> \<Psi>). f \<phi>') = (\<Sum>\<phi>'\<leftarrow>(\<Phi> \<ominus> (\<psi> # \<Psi>)). f \<phi>')"
        using perm_list_summation by blast
      ultimately have 
        "(\<Sum>\<psi>'\<leftarrow> \<Psi>. f \<psi>') + (\<Sum>\<phi>'\<leftarrow>(\<Phi> \<ominus> (\<psi> # \<Psi>)). f \<phi>') = (\<Sum>\<phi>'\<leftarrow> (remove1 \<psi> \<Phi>). f \<phi>')"
        by simp
      hence 
        "(\<Sum>\<psi>'\<leftarrow> (\<psi> # \<Psi>). f \<psi>') + (\<Sum>\<phi>'\<leftarrow>(\<Phi> \<ominus> (\<psi> # \<Psi>)). f \<phi>') = 
         (\<Sum>\<phi>'\<leftarrow> (\<psi> # (remove1 \<psi> \<Phi>)). f \<phi>')"
        by (simp add: add.assoc)  
      moreover have "\<psi> \<in> set \<Phi>"
        by (metis append_Cons hypothesis list.set_intros(1) mset_le_perm_append perm_set_eq)
      hence "(\<psi> # (remove1 \<psi> \<Phi>)) <~~> \<Phi>"
        by (simp add: perm_remove perm_sym)
      hence "(\<Sum>\<phi>'\<leftarrow> (\<psi> # (remove1 \<psi> \<Phi>)). f \<phi>') = (\<Sum>\<phi>'\<leftarrow>\<Phi>. f \<phi>')"
        using perm_list_summation by blast
      ultimately have 
        "(\<Sum>\<psi>'\<leftarrow> (\<psi> # \<Psi>). f \<psi>') + (\<Sum>\<phi>'\<leftarrow>(\<Phi> \<ominus> (\<psi> # \<Psi>)). f \<phi>') = (\<Sum>\<phi>'\<leftarrow>\<Phi>. f \<phi>')"
        by simp
    }
    then show ?case
      by blast 
  qed
  with assms show ?thesis by blast
qed

end