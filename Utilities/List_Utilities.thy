theory List_Utilities
  imports "~~/src/HOL/Library/Permutation"
begin

sledgehammer_params [smt_proofs = false]

subsection \<open> Multiset Coercion \<close>

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

lemma set_exclusion_mset_simplify:
  assumes "\<not> (\<exists> \<psi> \<in> set \<Psi>. \<psi> \<in> set \<Sigma>)"
      and "mset \<Psi> \<subseteq># mset (\<Sigma> @ \<Gamma>)"
    shows "mset \<Psi> \<subseteq># mset \<Gamma>"
using assms
proof (induct \<Sigma>)
  case Nil
  then show ?case by simp
next
  case (Cons \<sigma> \<Sigma>)
  then show ?case
    by (cases "\<sigma> \<in> set \<Psi>",
        fastforce,
        metis add.commute
              add_mset_add_single
              diff_single_trivial
              in_multiset_in_set
              mset.simps(2)
              notin_set_remove1
              remove_hd
              subset_eq_diff_conv
              union_code
              append_Cons)
qed

subsection \<open> List Mapping \<close>

lemma map_perm:
  assumes "A <~~> B"
  shows "map f A <~~> map f B"
  by (metis assms mset_eq_perm mset_map)

lemma map_monotonic:
  assumes "mset A \<subseteq># mset B"
  shows "mset (map f A) \<subseteq># mset (map f B)"
  by (simp add: assms image_mset_subseteq_mono)

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
            "B <~~> b # remove1 b B"
        by (metis \<open>a # A <~~> map f B\<close> perm_remove_perm remove_hd,
            meson b(1) perm_remove)
      hence "A <~~> (map f (remove1 b B))"
        by (metis (no_types) list.simps(9) mset_eq_perm mset_map mset_remove1 remove_hd)
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
        have "mset \<Phi> - {#f \<gamma>#} = mset \<Phi>"
            by (metis (no_types) \<open>f \<gamma> \<notin> set \<Phi>\<close> diff_single_trivial set_mset_mset)
        moreover have "mset (map f (\<gamma> # \<Gamma>)) = add_mset (f \<gamma>) (image_mset f (mset \<Gamma>))"
          by simp
        ultimately have "mset \<Phi> \<subseteq># mset (map f \<Gamma>)"
          by (metis (no_types) Diff_eq_empty_iff_mset
                               \<open>mset \<Phi> \<subseteq># mset (map f (\<gamma> # \<Gamma>))\<close>
                               add_mset_add_single
                               cancel_ab_semigroup_add_class.diff_right_commute
                               diff_diff_add mset_map)
        with Cons show ?thesis
          by (metis diff_subset_eq_self mset_remove1 remove_hd subset_mset.order.trans)
      qed
    }
    thus ?case using Cons by blast
  qed
  thus ?thesis using assms by blast
qed

subsection \<open> Laws for Searching a List \<close>

lemma find_Some_predicate:
  assumes "find P \<Psi> = Some \<psi>"
  shows "P \<psi>"
  using assms
proof (induct \<Psi>)
  case Nil
  then show ?case by simp
next
  case (Cons \<omega> \<Psi>)
  then show ?case by (cases "P \<omega>", fastforce+)
qed

lemma find_Some_set_membership:
  assumes "find P \<Psi> = Some \<psi>"
  shows "\<psi> \<in> set \<Psi>"
  using assms
proof (induct \<Psi>)
  case Nil
  then show ?case by simp
next
  case (Cons \<omega> \<Psi>)
  then show ?case by (cases "P \<omega>", fastforce+)
qed

subsection \<open> Permutations \<close>

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

lemma count_list_append:
  "count_list (A @ B) a = count_list A a + count_list B a"
  by (induct A, simp, simp)

lemma append_set_containment:
  assumes "a \<in> set A"
      and "A <~~> B @ C"
    shows "a \<in> set B \<or> a \<in> set C"
  using assms
  by (simp add: perm_set_eq)

lemma concat_remove1:
  assumes "\<Psi> \<in> set \<L>"
  shows "concat \<L> <~~> \<Psi> @ concat (remove1 \<Psi> \<L>)"
    using assms
    by (induct \<L>,
        simp,
        simp,
        metis append.assoc
              perm.trans
              perm_append1
              perm_append_swap)

lemma concat_set_membership_mset_containment:
  assumes "concat \<Gamma> <~~> \<Lambda>"
  and     "\<Phi> \<in> set \<Gamma>"
  shows   "mset \<Phi> \<subseteq># mset \<Lambda>"
  using assms
  by (induct \<Gamma>, simp, meson concat_remove1 mset_le_perm_append perm.trans perm_sym)

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

subsection \<open> List Duplicates \<close>

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

subsection \<open> List Subtraction \<close>

primrec listSubtract :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "\<ominus>" 70)
  where
      "xs \<ominus> [] = xs"
    | "xs \<ominus> (y # ys) = (remove1 y (xs \<ominus> ys))"

lemma listSubtract_mset_homomorphism [simp]:
  "mset (A \<ominus> B) = mset A - mset B"
  by (induct B, simp, simp)

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
      have "count_list \<Lambda> \<phi> \<le> count_list (remove1 \<psi> \<Phi>) \<phi>"
      proof (cases "\<phi> = \<psi>")
        case True
        hence "1 + count_list \<Lambda> \<phi> \<le> count_list \<Phi> \<phi>"
          using \<open>count_list (\<psi> # \<Lambda>) \<phi> \<le> count_list \<Phi> \<phi>\<close>
          by auto
        moreover from this have "\<phi> \<in> set \<Phi>"
          using not_one_le_zero by fastforce
        hence "\<Phi> <~~> \<phi> # (remove1 \<psi> \<Phi>)"
          using True
          by (simp add: True perm_remove)
        ultimately show ?thesis by (simp add: perm_count_list)
      next
        case False
        hence "count_list (\<psi> # \<Lambda>) \<phi> = count_list \<Lambda> \<phi>"
           by simp
        moreover have "count_list \<Phi> \<phi> = count_list (remove1 \<psi> \<Phi>) \<phi>"
        proof (induct \<Phi>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<phi>' \<Phi>)
          show ?case
          proof (cases "\<phi>' = \<phi>")
            case True
            with \<open>\<phi> \<noteq> \<psi>\<close>
            have "count_list (\<phi>' # \<Phi>) \<phi> = 1 + count_list \<Phi> \<phi>"
                 "count_list (remove1 \<psi> (\<phi>' # \<Phi>)) \<phi> = 1 + count_list (remove1 \<psi> \<Phi>) \<phi>"
              by simp+
            with Cons show ?thesis by linarith
          next
            case False
            with Cons show ?thesis by (cases "\<phi>' = \<psi>", simp+)
          qed
        qed
        ultimately show ?thesis
          using \<open>count_list (\<psi> # \<Lambda>) \<phi> \<le> count_list \<Phi> \<phi>\<close>
          by auto
      qed
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
proof -
  from \<open>\<phi> \<in> set \<Lambda>\<close> 
  have "mset (\<Phi> \<ominus> \<Lambda>) = mset ((remove1 \<phi> \<Phi>) \<ominus> (remove1 \<phi> \<Lambda>))"
    by simp
  thus ?thesis
    using mset_eq_perm by blast
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
  from \<open>\<Phi> <~~> \<Psi>\<close> have "mset \<Phi> = mset \<Psi>"
    by (simp add: mset_eq_perm)
  hence "mset (\<Phi> \<ominus> \<Lambda>) = mset (\<Psi> \<ominus> \<Lambda>)"
    by simp
  thus ?thesis
    using mset_eq_perm by blast 
qed

lemma append_perm_listSubtract_intro:
  assumes "A <~~> B @ C"
  shows "A \<ominus> C <~~> B"
proof -
  from \<open>A <~~> B @ C\<close> have "mset A = mset (B @ C)"
    using mset_eq_perm by blast
  hence "mset (A \<ominus> C) = mset B"
    by simp
  thus ?thesis using mset_eq_perm by blast
qed

lemma listSubtract_concat:
  assumes "\<Psi> \<in> set \<L>"
  shows "concat (\<L> \<ominus> [\<Psi>]) <~~> (concat \<L>) \<ominus> \<Psi>"
  using assms
  by (simp, 
      meson append_perm_listSubtract_intro
            concat_remove1
            perm.trans
            perm_append_swap
            perm_sym)

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

lemma listSubtract_msub_eq:
  assumes "mset \<Phi> \<subseteq># mset \<Gamma>"
      and "length (\<Gamma> \<ominus> \<Phi>) = m"
    shows "length \<Gamma> = m + length \<Phi>"
  using assms
proof -
  have "\<forall> \<Gamma>. mset \<Phi> \<subseteq># mset \<Gamma> --> length (\<Gamma> \<ominus> \<Phi>) = m --> length \<Gamma> = m + length \<Phi>"
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

lemma msub_listSubtract_elem_cons_msub:
  assumes "mset \<Xi> \<subseteq># mset \<Gamma>"
      and "\<psi> \<in> set (\<Gamma> \<ominus> \<Xi>)"
    shows "mset (\<psi> # \<Xi>) \<subseteq># mset \<Gamma>"
proof -
  have "\<forall> \<Gamma>. mset \<Xi> \<subseteq># mset \<Gamma> --> \<psi> \<in> set (\<Gamma> \<ominus> \<Xi>) --> mset (\<psi> # \<Xi>) \<subseteq># mset \<Gamma>"
  proof(induct \<Xi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<xi> \<Xi>)
    {
      fix \<Gamma>
      assume "mset (\<xi> # \<Xi>) \<subseteq># mset \<Gamma>"
             "\<psi> \<in> set (\<Gamma> \<ominus> (\<xi> # \<Xi>))"
      hence "\<xi> \<in> set \<Gamma>"
            "mset \<Xi> \<subseteq># mset (remove1 \<xi> \<Gamma>)"
            "\<psi> \<in> set ((remove1 \<xi> \<Gamma>) \<ominus> \<Xi>)"
        by (simp, metis ex_mset
                        list.set_intros(1)
                        mset.simps(2)
                        mset_eq_setD
                        subset_mset.le_iff_add
                        union_mset_add_mset_left,
            metis listSubtract.simps(1)
                  listSubtract.simps(2)
                  listSubtract_monotonic
                  remove_hd,
            simp, metis listSubtract_remove1_cons_perm
                        perm_set_eq)
      with Cons.hyps have "mset \<Gamma> = mset (\<xi> # (remove1 \<xi> \<Gamma>))"
                          "mset (\<psi> # \<Xi>) \<subseteq># mset (remove1 \<xi> \<Gamma>)"
        by (simp, blast)
      hence "mset (\<psi> # \<xi> # \<Xi>) \<subseteq># mset \<Gamma>"
        by (simp, metis add_mset_commute
                        mset_subset_eq_add_mset_cancel)
    }
    then show ?case by auto
  qed
  thus ?thesis using assms by blast
qed

subsection \<open> Tuple Lists \<close>

lemma remove1_pairs_list_projections_fst:
  assumes "(\<gamma>,\<sigma>) \<in># mset \<Phi>"
  shows "mset (map fst (remove1 (\<gamma>, \<sigma>) \<Phi>)) = mset (map fst \<Phi>) - {# \<gamma> #}"
using assms
proof (induct \<Phi>)
  case Nil
  then show ?case by simp
next
  case (Cons \<phi> \<Phi>)
  assume "(\<gamma>, \<sigma>) \<in># mset (\<phi> # \<Phi>)"
  show ?case
  proof (cases "\<phi> = (\<gamma>, \<sigma>)")
    assume "\<phi> = (\<gamma>, \<sigma>)"
    then show ?thesis by simp
  next
    assume "\<phi> \<noteq> (\<gamma>, \<sigma>)"
    then have "add_mset \<phi> (mset \<Phi> - {#(\<gamma>, \<sigma>)#}) = add_mset \<phi> (mset \<Phi>) - {#(\<gamma>, \<sigma>)#}"
        by force
    then have "add_mset (fst \<phi>) (image_mset fst (mset \<Phi> - {#(\<gamma>, \<sigma>)#}))
             = add_mset (fst \<phi>) (image_mset fst (mset \<Phi>)) - {#\<gamma>#}"
      by (metis (no_types) Cons.prems
                           add_mset_remove_trivial
                           fst_conv
                           image_mset_add_mset
                           insert_DiffM mset.simps(2))
    with \<open>\<phi> \<noteq> (\<gamma>, \<sigma>)\<close> show ?thesis
      by simp
  qed
qed

lemma remove1_pairs_list_projections_snd:
  assumes "(\<gamma>,\<sigma>) \<in># mset \<Phi>"
  shows "mset (map snd (remove1 (\<gamma>, \<sigma>) \<Phi>)) = mset (map snd \<Phi>) - {# \<sigma> #}"
using assms
proof (induct \<Phi>)
  case Nil
  then show ?case by simp
next
  case (Cons \<phi> \<Phi>)
  assume "(\<gamma>, \<sigma>) \<in># mset (\<phi> # \<Phi>)"
  show ?case
  proof (cases "\<phi> = (\<gamma>, \<sigma>)")
    assume "\<phi> = (\<gamma>, \<sigma>)"
    then show ?thesis by simp
  next
    assume "\<phi> \<noteq> (\<gamma>, \<sigma>)"
    then have "add_mset (snd \<phi>) (image_mset snd (mset \<Phi> - {#(\<gamma>, \<sigma>)#}))
             = image_mset snd (mset (\<phi> # \<Phi>) - {#(\<gamma>, \<sigma>)#})"
      by auto
    moreover have "add_mset (snd \<phi>) (image_mset snd (mset \<Phi>))
                 = add_mset \<sigma> (image_mset snd (mset (\<phi> # \<Phi>) - {#(\<gamma>, \<sigma>)#}))"
      by (metis (no_types) Cons.prems
                           image_mset_add_mset
                           insert_DiffM
                           mset.simps(2)
                           snd_conv)
    ultimately have "add_mset (snd \<phi>) (image_mset snd (mset \<Phi> - {#(\<gamma>, \<sigma>)#}))
                   = add_mset (snd \<phi>) (image_mset snd (mset \<Phi>)) - {#\<sigma>#}"
      by simp
    with \<open>\<phi> \<noteq> (\<gamma>, \<sigma>)\<close> show ?thesis
      by simp
  qed
qed

lemma triple_list_exists:
  assumes "mset (map snd \<Psi>) \<subseteq># mset \<Sigma>"
      and "mset \<Sigma> \<subseteq># mset (map snd \<Delta>)"
    shows "\<exists> \<Omega>. map (\<lambda> (\<psi>, \<sigma>, _). (\<psi>, \<sigma>)) \<Omega> = \<Psi> \<and>
                mset (map (\<lambda> (_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>)) \<Omega>) \<subseteq># mset \<Delta>"
  using assms(1)
proof (induct \<Psi>)
  case Nil
  then show ?case by fastforce
next
  case (Cons \<psi> \<Psi>)
  from Cons obtain \<Omega> where \<Omega>:
    "map (\<lambda> (\<psi>, \<sigma>, _). (\<psi>, \<sigma>)) \<Omega> = \<Psi>"
    "mset (map (\<lambda> (_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>)) \<Omega>) \<subseteq># mset \<Delta>"
    by (metis (no_types, lifting)
              diff_subset_eq_self
              list.set_intros(1)
              remove1_pairs_list_projections_snd
              remove_hd
              set_mset_mset
              subset_mset.dual_order.trans
              surjective_pairing)
  let ?\<Delta>\<^sub>\<Omega> = "map (\<lambda> (_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>)) \<Omega>"
  let ?\<psi> = "fst \<psi>"
  let ?\<sigma> = "snd \<psi>"
  from Cons.prems have "add_mset ?\<sigma> (image_mset snd (mset \<Psi>)) \<subseteq># mset \<Sigma>" by simp
  then have "mset \<Sigma> - {#?\<sigma>#} - image_mset snd (mset \<Psi>) \<noteq> mset \<Sigma> - image_mset snd (mset \<Psi>)"
    by (metis (no_types) insert_subset_eq_iff
                         mset_subset_eq_insertD
                         multi_drop_mem_not_eq
                         subset_mset.diff_add
                         subset_mset_def)
  hence "?\<sigma> \<in># mset \<Sigma> - mset (map snd \<Psi>)"
    using diff_single_trivial by fastforce
  have "mset (map snd (\<psi> # \<Psi>)) \<subseteq># mset (map snd \<Delta>)"
    by (meson Cons.prems \<open>mset \<Sigma> \<subseteq># mset (map snd \<Delta>)\<close> subset_mset.dual_order.trans)
  then have "mset (map snd \<Delta>) - mset (map snd (\<psi> # \<Psi>)) + ({#} + {#snd \<psi>#})
           = mset (map snd \<Delta>) + ({#} + {#snd \<psi>#}) - add_mset (snd \<psi>) (mset (map snd \<Psi>))"
    by (metis (no_types) list.simps(9) mset.simps(2) mset_subset_eq_multiset_union_diff_commute)
  then have "mset (map snd \<Delta>) - mset (map snd (\<psi> # \<Psi>)) + ({#} + {#snd \<psi>#})
           = mset (map snd \<Delta>) - mset (map snd \<Psi>)"
    by auto
  hence "?\<sigma> \<in># mset (map snd \<Delta>) - mset (map snd \<Psi>)"
    using add_mset_remove_trivial_eq by fastforce
  moreover have "snd \<circ> (\<lambda> (\<psi>, \<sigma>, _). (\<psi>, \<sigma>)) = snd \<circ> (\<lambda> (_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>))" by auto
  hence "map snd (?\<Delta>\<^sub>\<Omega>) = map snd (map (\<lambda> (\<psi>, \<sigma>, _). (\<psi>, \<sigma>)) \<Omega>)"
    by fastforce
  hence "map snd (?\<Delta>\<^sub>\<Omega>) = map snd \<Psi>"
    using \<Omega>(1) by simp
  ultimately have "?\<sigma> \<in># mset (map snd \<Delta>) - mset (map snd ?\<Delta>\<^sub>\<Omega>)"
    by simp
  hence "?\<sigma> \<in># image_mset snd (mset \<Delta> - mset ?\<Delta>\<^sub>\<Omega>)"
    using \<Omega>(2) by (metis image_mset_Diff mset_map)
  hence "?\<sigma> \<in> snd ` set_mset (mset \<Delta> - mset ?\<Delta>\<^sub>\<Omega>)"
    by (metis in_image_mset)
  from this obtain \<rho> where \<rho>:
    "snd \<rho> = ?\<sigma>" "\<rho> \<in># mset \<Delta> - mset ?\<Delta>\<^sub>\<Omega>"
    using imageE by auto
  from this obtain \<gamma> where
    "(\<gamma>, ?\<sigma>) = \<rho>"
    by (metis prod.collapse)
  with \<rho>(2) have \<gamma>: "(\<gamma>, ?\<sigma>) \<in># mset \<Delta> - mset ?\<Delta>\<^sub>\<Omega>" by auto
  let ?\<Omega> = "(?\<psi>, ?\<sigma>, \<gamma>) # \<Omega>"
  have "map (\<lambda> (\<psi>, \<sigma>, _). (\<psi>, \<sigma>)) ?\<Omega> = \<psi> # \<Psi>"
    using \<Omega>(1) by simp
  moreover
  have A: "(\<gamma>, snd \<psi>) = (case (snd \<psi>, \<gamma>) of (a, c) \<Rightarrow> (c, a))"
    by auto
  have B: "mset (map (\<lambda>(b, a, c). (c, a)) \<Omega>) + {#case (snd \<psi>, \<gamma>) of (a, c) \<Rightarrow> (c, a)#}
         = mset (map (\<lambda>(b, a, c). (c, a)) ((fst \<psi>, snd \<psi>, \<gamma>) # \<Omega>))"
    by simp
  obtain mm :: "('c \<times> 'a) multiset \<Rightarrow> ('c \<times> 'a) multiset \<Rightarrow> ('c \<times> 'a) multiset" where
    "\<forall>x0 x1. (\<exists>v2. x0 = x1 + v2) = (x0 = x1 + mm x0 x1)"
    by moura
  then have "mset \<Delta> = mset (map (\<lambda>(b, a, c). (c, a)) \<Omega>) + mm (mset \<Delta>) (mset (map (\<lambda>(b, a, c). (c, a)) \<Omega>))"
    by (metis \<Omega>(2) subset_mset.le_iff_add)
  then have "mset (map (\<lambda> (_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>)) ?\<Omega>) \<subseteq># mset \<Delta>"
    using A B by (metis \<gamma> add_diff_cancel_left' single_subset_iff subset_mset.add_le_cancel_left)
  ultimately show ?case by meson
qed

subsection \<open> List Intersection \<close>

primrec list_intersect :: "'a list => 'a list => 'a list"  (infixl "\<^bold>\<inter>" 60)
  where
    "_ \<^bold>\<inter> [] = []"
  | "xs \<^bold>\<inter> (y # ys) = (if (y \<in> set xs) then (y # (remove1 y xs \<^bold>\<inter> ys)) else (xs \<^bold>\<inter> ys))"

lemma list_intersect_mset_homomorphism [simp]: "mset (\<Phi> \<^bold>\<inter> \<Psi>) = mset \<Phi> \<inter># mset \<Psi>"
proof -
  have "\<forall> \<Phi>. mset (\<Phi> \<^bold>\<inter> \<Psi>) = mset \<Phi> \<inter># mset \<Psi>"
  proof (induct \<Psi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<psi> \<Psi>)
    {
      fix \<Phi>
      have "mset (\<Phi> \<^bold>\<inter> \<psi> # \<Psi>) = mset \<Phi> \<inter># mset (\<psi> # \<Psi>)"
        using Cons.hyps
        by (cases "\<psi> \<in> set \<Phi>", 
            simp add: inter_add_right2,
            simp add: inter_add_right1)
    }
    then show ?case by blast 
  qed
  thus ?thesis by simp
qed
    
lemma list_intersect_left_empty [simp]: "[] \<^bold>\<inter> \<Phi> = []" by (induct \<Phi>, simp+)
    
lemma list_diff_intersect_comp:
  "mset \<Phi> = mset (\<Phi> \<ominus> \<Psi>) + mset (\<Phi> \<^bold>\<inter> \<Psi>)"
  by (simp add: multiset_inter_def)
  
lemma list_intersect_left_project: "mset (\<Phi> \<^bold>\<inter> \<Psi>) \<subseteq># mset \<Phi>"
  by simp

lemma list_intersect_right_project: "mset (\<Phi> \<^bold>\<inter> \<Psi>) \<subseteq># mset \<Psi>"
  by simp

end
