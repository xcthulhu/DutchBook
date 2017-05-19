theory Logical_Probability_Full_Completeness
  imports "../Weakly_Additive/Weakly_Additive_Logical_Probability"
          Logical_Probability_Elementary_Completeness
begin

(* TODO: Move utility stuff *)
  
definition uncurry :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c"
  where [simp]: "uncurry f = (\<lambda> (x, y). f x y)"

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


lemma remove1_pairs_list_projections:
  assumes "(\<gamma>,\<sigma>) \<in># mset \<Phi>"
  shows "mset (map fst (remove1 (\<gamma>, \<sigma>) \<Phi>)) = mset (map fst \<Phi>) - {# \<gamma> #} \<and> 
         mset (map snd (remove1 (\<gamma>, \<sigma>) \<Phi>)) = mset (map snd \<Phi>) - {# \<sigma> #}"
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
    then show ?thesis
    by (simp, smt Cons.prems
              add_mset_remove_trivial 
              diff_union_swap 
              fst_conv
              snd_conv
              image_mset_add_mset 
              insert_DiffM 
              mset.simps(2)) 
  qed
qed
    
(***************************************)

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
    
(***************************************)    
    
primrec (in Classical_Propositional_Logic) 
  stratified_deduction :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool" ("_ #\<turnstile> _ _" [60,100,59] 60)
  where
    "\<Gamma> #\<turnstile> 0 \<phi> = True"
  | "\<Gamma> #\<turnstile> (Suc n) \<phi> = (\<exists> \<Psi>. mset (map snd \<Psi>) \<subseteq># mset \<Gamma> \<and> 
                             map (uncurry (op \<squnion>)) \<Psi> :\<turnstile> \<phi> \<and> 
                             map (uncurry (op \<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>) #\<turnstile> n \<phi>)"
    
primrec (in Classical_Propositional_Logic) 
  segmented_deduction :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" ("_ $\<turnstile> _" [60,100] 60)
  where
    "\<Gamma> $\<turnstile> [] = True"
  | "\<Gamma> $\<turnstile> (\<phi> # \<Phi>) = (\<exists> \<Psi>. mset (map snd \<Psi>) \<subseteq># mset \<Gamma> \<and> 
                           map (uncurry (op \<squnion>)) \<Psi> :\<turnstile> \<phi> \<and> 
                           map (uncurry (op \<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>) $\<turnstile> \<Phi>)"

lemma (in Classical_Propositional_Logic) stratified_segmented_deduction_replicate:
  "\<Gamma> #\<turnstile> n \<phi> = \<Gamma> $\<turnstile> (replicate n \<phi>)"
proof -
  have "\<forall> \<Gamma>. \<Gamma> #\<turnstile> n \<phi> = \<Gamma> $\<turnstile> (replicate n \<phi>)"
    by (induct n, simp+)
  thus ?thesis by blast
qed

definition (in Minimal_Logic) 
  stronger_theory_relation :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infix "\<preceq>" 100)
  where
    "\<Sigma> \<preceq> \<Gamma> = (\<exists> \<Phi>. map snd \<Phi> = \<Sigma> \<and> 
                    mset (map fst \<Phi>) \<subseteq># mset \<Gamma> \<and> 
                    (\<forall> (\<gamma>,\<sigma>) \<in> set \<Phi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>))"

lemma (in Minimal_Logic) msubset_stronger_theory:    
  assumes "mset \<Sigma> \<subseteq># mset \<Gamma>"
  shows "\<Sigma> \<preceq> \<Gamma>"
proof -
  let ?\<Delta>\<Sigma> = "map (\<lambda> x. (x,x)) \<Sigma>"
  have "map snd ?\<Delta>\<Sigma> = \<Sigma>"
    by (induct \<Sigma>, simp, simp)
  moreover have "map fst ?\<Delta>\<Sigma> = \<Sigma>"
    by (induct \<Sigma>, simp, simp)
  hence "mset (map fst ?\<Delta>\<Sigma>) \<subseteq># mset \<Gamma>"
    using assms by simp
  moreover have "\<forall> (\<gamma>,\<sigma>) \<in> set ?\<Delta>\<Sigma>. \<turnstile> \<gamma> \<rightarrow> \<sigma>"
    by (induct \<Sigma>, simp, simp, 
        metis list_implication.simps(1) list_implication_Axiom_1)
  ultimately show ?thesis using stronger_theory_relation_def by (simp, blast)
qed
  
lemma (in Minimal_Logic) stronger_theory_reflexive: "\<Gamma> \<preceq> \<Gamma>"
  using msubset_stronger_theory by auto

lemma (in Minimal_Logic) weakest_theory: "[] \<preceq> \<Gamma>"
  using msubset_stronger_theory by auto

lemma (in Minimal_Logic) stronger_theory_empty_list_intro [simp]:
  assumes "\<Gamma> \<preceq> []"
  shows "\<Gamma> = []"
  using assms stronger_theory_relation_def by simp

lemma (in Minimal_Logic) stronger_theory_right_permutation:
  assumes "\<Gamma> <~~> \<Gamma>'"
      and "\<Sigma> \<preceq> \<Gamma>"
    shows "\<Sigma> \<preceq> \<Gamma>'"
proof -
  from assms(1) have "mset \<Gamma> = mset \<Gamma>'"
    by (simp add: mset_eq_perm)
  thus ?thesis 
    using assms(2) stronger_theory_relation_def
    by fastforce
qed
  
lemma (in Minimal_Logic) stronger_theory_left_permutation:
  assumes "\<Sigma> <~~> \<Sigma>'"
      and "\<Sigma> \<preceq> \<Gamma>"
    shows "\<Sigma>' \<preceq> \<Gamma>"
proof -
  have "\<forall> \<Sigma> \<Gamma>. \<Sigma> <~~> \<Sigma>' \<longrightarrow> \<Sigma> \<preceq> \<Gamma> \<longrightarrow> \<Sigma>' \<preceq> \<Gamma>"
  proof (induct \<Sigma>')
    case Nil
    then show ?case by simp
  next
    case (Cons \<sigma> \<Sigma>')
    {
      fix \<Sigma> \<Gamma>
      assume "\<Sigma> <~~> (\<sigma> # \<Sigma>')" "\<Sigma> \<preceq> \<Gamma>"
      from this obtain \<Phi> where \<Phi>:
        "map snd \<Phi> = \<Sigma>"
        "mset (map fst \<Phi>) \<subseteq># mset \<Gamma>" 
        "\<forall> (\<gamma>,\<sigma>) \<in> set \<Phi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>"
        using stronger_theory_relation_def by fastforce
      with \<open>\<Sigma> <~~> (\<sigma> # \<Sigma>')\<close> have "\<sigma> \<in># mset (map snd \<Phi>)"
        by (simp add: perm_set_eq)
      from this obtain \<gamma> where \<gamma>: "(\<gamma>, \<sigma>) \<in># mset \<Phi>"
        by (induct \<Phi>, fastforce+)
      let ?\<Phi>\<^sub>0 = "remove1 (\<gamma>, \<sigma>) \<Phi>"
      let ?\<Sigma>\<^sub>0 = "map snd ?\<Phi>\<^sub>0"
      from \<gamma> \<Phi>(2) have "mset (map fst ?\<Phi>\<^sub>0) \<subseteq># mset (remove1 \<gamma> \<Gamma>)"
        by (metis ex_mset 
                  listSubtract_monotonic 
                  listSubtract_mset_homomorphism 
                  mset_remove1
                  remove1_pairs_list_projections)
      moreover have "mset ?\<Phi>\<^sub>0 \<subseteq># mset \<Phi>" by simp
      with \<Phi>(3) have "\<forall> (\<gamma>,\<sigma>) \<in> set ?\<Phi>\<^sub>0. \<turnstile> \<gamma> \<rightarrow> \<sigma>" by fastforce
      ultimately have "?\<Sigma>\<^sub>0 \<preceq> remove1 \<gamma> \<Gamma>"
        unfolding stronger_theory_relation_def by blast
      moreover have "\<Sigma>' <~~> (remove1 \<sigma> \<Sigma>)" using \<open>\<Sigma> <~~> (\<sigma> # \<Sigma>')\<close>
        by (metis perm_remove_perm perm_sym remove_hd)
      moreover from \<gamma> \<Phi>(1) have "mset ?\<Sigma>\<^sub>0 = mset (remove1 \<sigma> \<Sigma>)"
        using remove1_pairs_list_projections
        by fastforce
      hence "?\<Sigma>\<^sub>0 <~~> remove1 \<sigma> \<Sigma>"
        using mset_eq_perm by blast
      ultimately have "\<Sigma>' \<preceq> remove1 \<gamma> \<Gamma>" using Cons
        by (meson perm.trans perm_sym)
      from this obtain \<Psi>\<^sub>0 where \<Psi>\<^sub>0:
        "map snd \<Psi>\<^sub>0 = \<Sigma>'"
        "mset (map fst \<Psi>\<^sub>0) \<subseteq># mset (remove1 \<gamma> \<Gamma>)" 
        "\<forall> (\<gamma>,\<sigma>) \<in> set \<Psi>\<^sub>0. \<turnstile> \<gamma> \<rightarrow> \<sigma>"
        using stronger_theory_relation_def by fastforce
      let ?\<Psi> = "(\<gamma>, \<sigma>) # \<Psi>\<^sub>0"
      have "map snd ?\<Psi> = (\<sigma> # \<Sigma>')"
        by (simp add: \<Psi>\<^sub>0(1))
      moreover have "mset (map fst ?\<Psi>) \<subseteq># mset (\<gamma> # (remove1 \<gamma> \<Gamma>))"
        using \<Psi>\<^sub>0(2) by auto
      moreover from \<gamma> \<Phi>(3) \<Psi>\<^sub>0(3) have "\<forall> (\<gamma>,\<sigma>) \<in> set ?\<Psi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>" by auto
      ultimately have "(\<sigma> # \<Sigma>') \<preceq> (\<gamma> # (remove1 \<gamma> \<Gamma>))"
        unfolding stronger_theory_relation_def by smt
      moreover from \<gamma> \<Phi>(2) have "\<gamma> \<in># mset \<Gamma>"
        using mset_subset_eqD by fastforce
      hence "(\<gamma> # (remove1 \<gamma> \<Gamma>)) <~~> \<Gamma>"
        by (simp add: perm_remove perm_sym)
      ultimately have "(\<sigma> # \<Sigma>') \<preceq> \<Gamma>"
        using stronger_theory_right_permutation by blast 
    }
    then show ?case by blast
  qed
  with assms show ?thesis by blast
qed
  
lemma (in Minimal_Logic) stronger_theory_transitive:
  assumes "\<Sigma> \<preceq> \<Delta>" and "\<Delta> \<preceq> \<Gamma>"
    shows "\<Sigma> \<preceq> \<Gamma>"
proof -
  have "\<forall> \<Delta> \<Gamma>. \<Sigma> \<preceq> \<Delta> \<longrightarrow> \<Delta> \<preceq> \<Gamma> \<longrightarrow> \<Sigma> \<preceq> \<Gamma>"
  proof (induct \<Sigma>)
    case Nil
    then show ?case using stronger_theory_relation_def by simp 
  next
    case (Cons \<sigma> \<Sigma>)
    {
      fix \<Delta> \<Gamma>
      assume "(\<sigma> # \<Sigma>) \<preceq> \<Delta>" "\<Delta> \<preceq> \<Gamma>"
      from this obtain \<Phi> where \<Phi>:
        "map snd \<Phi> = \<sigma> # \<Sigma>"
        "mset (map fst \<Phi>) \<subseteq># mset \<Delta>" 
        "\<forall> (\<delta>,\<sigma>) \<in> set \<Phi>. \<turnstile> \<delta> \<rightarrow> \<sigma>"
        using stronger_theory_relation_def by (simp, smt)
      let ?\<delta> = "fst (hd \<Phi>)"
      from \<Phi>(1) have "\<Phi> \<noteq> []" by (induct \<Phi>, simp+)
      hence "?\<delta> \<in># mset (map fst \<Phi>)" by (induct \<Phi>, simp+)
      with \<Phi>(2) have "?\<delta> \<in># mset \<Delta>" by (meson mset_subset_eqD)
      with \<open>\<Phi> \<noteq> []\<close> \<Phi>(2) have "mset (map fst (remove1 (hd \<Phi>) \<Phi>)) \<subseteq># mset (remove1 ?\<delta> \<Delta>)"
        by (simp, 
            metis diff_single_eq_union 
                  hd_in_set 
                  image_mset_add_mset 
                  insert_subset_eq_iff 
                  set_mset_mset)
      moreover from \<open>\<Phi> \<noteq> []\<close> have "remove1 (hd \<Phi>) \<Phi> = tl \<Phi>" by (induct \<Phi>, simp+)
      moreover from \<Phi>(1) have "map snd (tl \<Phi>) = \<Sigma>"
        by (simp add: map_tl)
      moreover from \<Phi>(3) have "\<forall> (\<delta>,\<sigma>) \<in> set (tl \<Phi>). \<turnstile> \<delta> \<rightarrow> \<sigma>"
        by (simp add: \<open>\<Phi> \<noteq> []\<close> list.set_sel(2)) 
      ultimately have "\<Sigma> \<preceq> remove1 ?\<delta> \<Delta>"
        using stronger_theory_relation_def by auto
      from \<open>?\<delta> \<in># mset \<Delta>\<close> have "?\<delta> # (remove1 ?\<delta> \<Delta>) <~~> \<Delta>"
        by (simp add: perm_remove perm_sym)
      with \<open>\<Delta> \<preceq> \<Gamma>\<close> have "(?\<delta> # (remove1 ?\<delta> \<Delta>)) \<preceq> \<Gamma>"
        using stronger_theory_left_permutation perm_sym by blast
      from this obtain \<Psi> where \<Psi>:
        "map snd \<Psi> = (?\<delta> # (remove1 ?\<delta> \<Delta>))"
        "mset (map fst \<Psi>) \<subseteq># mset \<Gamma>"
        "\<forall> (\<gamma>,\<delta>) \<in> set \<Psi>. \<turnstile> \<gamma> \<rightarrow> \<delta>"
        using stronger_theory_relation_def by (simp, smt)
      let ?\<gamma> = "fst (hd \<Psi>)"
      from \<Psi>(1) have "\<Psi> \<noteq> []" by (induct \<Psi>, simp+)
      hence "?\<gamma> \<in># mset (map fst \<Psi>)" by (induct \<Psi>, simp+)
      with \<Psi>(2) have "?\<gamma> \<in># mset \<Gamma>" by (meson mset_subset_eqD)
      with \<open>\<Psi> \<noteq> []\<close> \<Psi>(2) have "mset (map fst (remove1 (hd \<Psi>) \<Psi>)) \<subseteq># mset (remove1 ?\<gamma> \<Gamma>)"
        by (simp, 
            metis diff_single_eq_union 
                  hd_in_set 
                  image_mset_add_mset 
                  insert_subset_eq_iff 
                  set_mset_mset)
      moreover from \<open>\<Psi> \<noteq> []\<close> have "remove1 (hd \<Psi>) \<Psi> = tl \<Psi>" by (induct \<Psi>, simp+)
      moreover from \<Psi>(1) have "map snd (tl \<Psi>) = (remove1 ?\<delta> \<Delta>)"
        by (simp add: map_tl)
      moreover from \<Psi>(3) have "\<forall> (\<gamma>,\<delta>) \<in> set (tl \<Psi>). \<turnstile> \<gamma> \<rightarrow> \<delta>"
        by (simp add: \<open>\<Psi> \<noteq> []\<close> list.set_sel(2)) 
      ultimately have "remove1 ?\<delta> \<Delta> \<preceq> remove1 ?\<gamma> \<Gamma>"
        using stronger_theory_relation_def by auto
      with \<open>\<Sigma> \<preceq> remove1 ?\<delta> \<Delta>\<close> Cons.hyps have "\<Sigma> \<preceq> remove1 ?\<gamma> \<Gamma>"
        by blast
      from this obtain \<Omega>\<^sub>0 where \<Omega>\<^sub>0:
        "map snd \<Omega>\<^sub>0 = \<Sigma>"
        "mset (map fst \<Omega>\<^sub>0) \<subseteq># mset (remove1 ?\<gamma> \<Gamma>)" 
        "\<forall> (\<gamma>,\<sigma>) \<in> set \<Omega>\<^sub>0. \<turnstile> \<gamma> \<rightarrow> \<sigma>"
        using stronger_theory_relation_def by (simp, smt)
      let ?\<Omega> = "(?\<gamma>, \<sigma>) # \<Omega>\<^sub>0"
      from \<Omega>\<^sub>0(1) have "map snd ?\<Omega> = \<sigma> # \<Sigma>" by simp
      moreover from \<Omega>\<^sub>0(2) have "mset (map fst ?\<Omega>) \<subseteq># mset (?\<gamma> # (remove1 ?\<gamma> \<Gamma>))"
        by simp
      moreover from \<Phi>(1) \<Psi>(1) have "\<sigma> = snd (hd \<Phi>)" "?\<delta> = snd (hd \<Psi>)" by fastforce+
      with \<Phi>(3) \<Psi>(3) \<open>\<Phi> \<noteq> []\<close> \<open>\<Psi> \<noteq> []\<close> hd_in_set have "\<turnstile> ?\<delta> \<rightarrow> \<sigma>" "\<turnstile> ?\<gamma> \<rightarrow> ?\<delta>"
        by fastforce+
      hence "\<turnstile> ?\<gamma> \<rightarrow> \<sigma>" using Modus_Ponens hypothetical_syllogism by blast 
      with \<Omega>\<^sub>0(3) have "\<forall> (\<gamma>,\<sigma>) \<in> set ?\<Omega>. \<turnstile> \<gamma> \<rightarrow> \<sigma>"
        by auto
      ultimately have "(\<sigma> # \<Sigma>) \<preceq> (?\<gamma> # (remove1 ?\<gamma> \<Gamma>))"
        unfolding stronger_theory_relation_def
        by smt
      moreover from \<open>?\<gamma> \<in># mset \<Gamma>\<close> have "(?\<gamma> # (remove1 ?\<gamma> \<Gamma>)) <~~> \<Gamma>"
        by (simp add: perm_remove perm_sym)
      ultimately have "(\<sigma> # \<Sigma>) \<preceq> \<Gamma>"
        using stronger_theory_right_permutation 
        by blast 
    }
    then show ?case by blast
  qed
  thus ?thesis using assms by blast
qed

lemma (in Minimal_Logic) stronger_theory_witness:
  assumes "\<sigma> \<in> set \<Sigma>"
    shows "\<Sigma> \<preceq> \<Gamma> = (\<exists> \<gamma> \<in> set \<Gamma>. \<turnstile> \<gamma> \<rightarrow> \<sigma> \<and> (remove1 \<sigma> \<Sigma>) \<preceq> (remove1 \<gamma> \<Gamma>))"
proof (rule iffI)
  assume "\<Sigma> \<preceq> \<Gamma>"
  from this obtain \<Phi> where \<Phi>:
    "map snd \<Phi> = \<Sigma>"
    "mset (map fst \<Phi>) \<subseteq># mset \<Gamma>" 
    "\<forall> (\<gamma>,\<sigma>) \<in> set \<Phi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>"
    unfolding stronger_theory_relation_def by blast
  from assms \<Phi>(1) obtain \<gamma> where \<gamma>: "(\<gamma>, \<sigma>) \<in># mset \<Phi>" 
    by (induct \<Phi>, fastforce+)
  hence "\<gamma> \<in># mset (map fst \<Phi>)" by force
  hence "\<gamma> \<in># mset \<Gamma>" using \<Phi>(2)
    by (meson mset_subset_eqD)
  moreover 
  let ?\<Phi>\<^sub>0 = "remove1 (\<gamma>, \<sigma>) \<Phi>"
  let ?\<Sigma>\<^sub>0 = "map snd ?\<Phi>\<^sub>0"
  from \<gamma> \<Phi>(2) have "mset (map fst ?\<Phi>\<^sub>0) \<subseteq># mset (remove1 \<gamma> \<Gamma>)"
    by (metis ex_mset 
              listSubtract_monotonic 
              listSubtract_mset_homomorphism
              remove1_pairs_list_projections
              mset_remove1)
  moreover have "mset ?\<Phi>\<^sub>0 \<subseteq># mset \<Phi>" by simp
  with \<Phi>(3) have "\<forall> (\<gamma>,\<sigma>) \<in> set ?\<Phi>\<^sub>0. \<turnstile> \<gamma> \<rightarrow> \<sigma>" by fastforce
  ultimately have "?\<Sigma>\<^sub>0 \<preceq> remove1 \<gamma> \<Gamma>"
    unfolding stronger_theory_relation_def by blast
  moreover from \<gamma> \<Phi>(1) have "mset ?\<Sigma>\<^sub>0 = mset (remove1 \<sigma> \<Sigma>)"
    using remove1_pairs_list_projections
    by fastforce
  hence "?\<Sigma>\<^sub>0 <~~> remove1 \<sigma> \<Sigma>"
    using mset_eq_perm by blast
  ultimately have "remove1 \<sigma> \<Sigma> \<preceq> remove1 \<gamma> \<Gamma>"
    using stronger_theory_left_permutation by auto
  moreover from \<gamma> \<Phi>(3) have "\<turnstile> \<gamma> \<rightarrow> \<sigma>" by (simp, fast)
  moreover from \<gamma> \<Phi>(2) have "\<gamma> \<in># mset \<Gamma>"
    using mset_subset_eqD by fastforce
  ultimately show "\<exists> \<gamma> \<in> set \<Gamma>. \<turnstile> \<gamma> \<rightarrow> \<sigma> \<and> (remove1 \<sigma> \<Sigma>) \<preceq> (remove1 \<gamma> \<Gamma>)" by auto
next
  assume "\<exists> \<gamma> \<in> set \<Gamma>. \<turnstile> \<gamma> \<rightarrow> \<sigma> \<and> (remove1 \<sigma> \<Sigma>) \<preceq> (remove1 \<gamma> \<Gamma>)"
  from this obtain \<Phi> \<gamma> where \<gamma>: "\<gamma> \<in> set \<Gamma>" "\<turnstile> \<gamma> \<rightarrow> \<sigma>"
                       and \<Phi>: "map snd \<Phi> = (remove1 \<sigma> \<Sigma>)"
                              "mset (map fst \<Phi>) \<subseteq># mset (remove1 \<gamma> \<Gamma>)" 
                              "\<forall> (\<gamma>,\<sigma>) \<in> set \<Phi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>"
    unfolding stronger_theory_relation_def by blast
  let ?\<Phi> = "(\<gamma>, \<sigma>) # \<Phi>"
  from \<Phi>(1) have "map snd ?\<Phi> = \<sigma> # (remove1 \<sigma> \<Sigma>)" by simp
  moreover from \<Phi>(2) \<gamma>(1) have "mset (map fst ?\<Phi>) \<subseteq># mset \<Gamma>" 
    by (simp add: insert_subset_eq_iff)
  moreover from \<Phi>(3) \<gamma>(2) have "\<forall> (\<gamma>,\<sigma>) \<in> set ?\<Phi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>"
    by auto
  ultimately have "(\<sigma> # (remove1 \<sigma> \<Sigma>)) \<preceq> \<Gamma>"
    unfolding stronger_theory_relation_def by smt
  moreover from assms have "\<sigma> # (remove1 \<sigma> \<Sigma>) <~~> \<Sigma>"
    by (simp add: perm_remove perm_sym)
  ultimately show "\<Sigma> \<preceq> \<Gamma>"
    using stronger_theory_left_permutation by blast 
qed  

lemma (in Minimal_Logic) stronger_theory_cons_witness:
  "(\<sigma> # \<Sigma>) \<preceq> \<Gamma> = (\<exists> \<gamma> \<in> set \<Gamma>. \<turnstile> \<gamma> \<rightarrow> \<sigma> \<and> \<Sigma> \<preceq> (remove1 \<gamma> \<Gamma>))"
proof -
  have "\<sigma> \<in># mset (\<sigma> # \<Sigma>)" by simp
  hence "(\<sigma> # \<Sigma>) \<preceq> \<Gamma> = (\<exists> \<gamma> \<in> set \<Gamma>. \<turnstile> \<gamma> \<rightarrow> \<sigma> \<and> (remove1 \<sigma> (\<sigma> # \<Sigma>)) \<preceq> (remove1 \<gamma> \<Gamma>))"
    by (meson list.set_intros(1) stronger_theory_witness)
  thus ?thesis by simp
qed
  
lemma (in Minimal_Logic) stronger_theory_left_cons:
  assumes "(\<sigma> # \<Sigma>) \<preceq> \<Gamma>"
  shows "\<Sigma> \<preceq> \<Gamma>"
proof -
  from assms obtain \<Phi> where \<Phi>:
    "map snd \<Phi> = \<sigma> # \<Sigma>"
    "mset (map fst \<Phi>) \<subseteq># mset \<Gamma>" 
    "\<forall> (\<delta>,\<sigma>) \<in> set \<Phi>. \<turnstile> \<delta> \<rightarrow> \<sigma>"
        using stronger_theory_relation_def by (simp, smt)
  let ?\<Phi>' = "remove1 (hd \<Phi>) \<Phi>"
  from \<Phi>(1) have "map snd ?\<Phi>' = \<Sigma>" by (induct \<Phi>, simp+)
  moreover from \<Phi>(2) have "mset (map fst ?\<Phi>') \<subseteq># mset \<Gamma>"
    by (metis diff_subset_eq_self 
              listSubtract.simps(1) 
              listSubtract.simps(2) 
              listSubtract_mset_homomorphism 
              map_monotonic 
              subset_mset.dual_order.trans)
  moreover from \<Phi>(3) have "\<forall> (\<delta>,\<sigma>) \<in> set ?\<Phi>'. \<turnstile> \<delta> \<rightarrow> \<sigma>" by fastforce
  ultimately show ?thesis unfolding stronger_theory_relation_def by blast
qed
  
lemma (in Minimal_Logic) stronger_theory_deduction_monotonic:
  assumes "\<Sigma> \<preceq> \<Gamma>"
      and "\<Sigma> :\<turnstile> \<phi>"
    shows "\<Gamma> :\<turnstile> \<phi>"
using assms
proof -
  have "\<forall> \<phi>. \<Sigma> \<preceq> \<Gamma> \<longrightarrow> \<Sigma> :\<turnstile> \<phi> \<longrightarrow> \<Gamma> :\<turnstile> \<phi>"
  proof (induct \<Sigma>)
    case Nil
    then show ?case
      by (simp add: list_deduction_weaken)
  next
    case (Cons \<sigma> \<Sigma>)
    {
      fix \<phi>
      assume "(\<sigma> # \<Sigma>) \<preceq> \<Gamma>" "(\<sigma> # \<Sigma>) :\<turnstile> \<phi>"
      hence "\<Sigma> :\<turnstile> \<sigma> \<rightarrow> \<phi>" "\<Sigma> \<preceq> \<Gamma>"
        using list_deduction_theorem
              stronger_theory_left_cons
        by (blast, smt)
      with Cons have "\<Gamma> :\<turnstile> \<sigma> \<rightarrow> \<phi>" by blast
      moreover 
      have "\<sigma> \<in> set (\<sigma> # \<Sigma>)" by auto
      with \<open>(\<sigma> # \<Sigma>) \<preceq> \<Gamma>\<close> obtain \<gamma> where \<gamma>: "\<gamma> \<in> set \<Gamma>" "\<turnstile> \<gamma> \<rightarrow> \<sigma>"
        using stronger_theory_witness by blast
      hence "\<Gamma> :\<turnstile> \<sigma>"
        using list_deduction_modus_ponens 
              list_deduction_reflection 
              list_deduction_weaken 
        by blast
      ultimately have "\<Gamma> :\<turnstile> \<phi>"
        using list_deduction_modus_ponens by blast 
    }
    then show ?case by blast
  qed
  with assms show ?thesis by blast
qed
  
lemma (in Classical_Propositional_Logic) segmented_deduction_assumption_mset_monotonic:
  assumes "mset \<Sigma> \<subseteq># mset \<Gamma>"
      and "\<Sigma> $\<turnstile> \<Phi>"
    shows "\<Gamma> $\<turnstile> \<Phi>"
using assms
proof -
  have "\<forall> \<Sigma> \<Gamma>. mset \<Sigma> \<subseteq># mset \<Gamma> \<longrightarrow> \<Sigma> $\<turnstile> \<Phi> \<longrightarrow> \<Gamma> $\<turnstile> \<Phi>"
  proof (induct \<Phi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<phi> \<Phi>)
    {
      fix \<Sigma> \<Gamma>
      assume "mset \<Sigma> \<subseteq># mset \<Gamma>" "\<Sigma> $\<turnstile> (\<phi> # \<Phi>)"
      from this obtain \<Psi> where \<Psi>:
        "mset (map snd \<Psi>) \<subseteq># mset \<Sigma>"
        "map (uncurry (op \<squnion>)) \<Psi> :\<turnstile> \<phi>"
        "map (uncurry (op \<rightarrow>)) \<Psi> @ \<Sigma> \<ominus> (map snd \<Psi>) $\<turnstile> \<Phi>"
        using segmented_deduction.simps(2) by blast
      let ?\<Psi> = "map snd \<Psi>"
      let ?\<Psi>' = "map (uncurry (op \<rightarrow>)) \<Psi>"
      let ?\<Sigma>' = "?\<Psi>' @ (\<Sigma> \<ominus> ?\<Psi>)"
      let ?\<Gamma>' = "?\<Psi>' @ (\<Gamma> \<ominus> ?\<Psi>)"
      from \<Psi> have "mset ?\<Psi> \<subseteq># mset \<Gamma>"
        using \<open>mset \<Sigma> \<subseteq># mset \<Gamma>\<close> subset_mset.order.trans by blast
      moreover have "mset (\<Sigma> \<ominus> ?\<Psi>) \<subseteq># mset (\<Gamma> \<ominus> ?\<Psi>)"
        by (metis \<open>mset \<Sigma> \<subseteq># mset \<Gamma>\<close> listSubtract_monotonic)
      hence "mset ?\<Sigma>' \<subseteq># mset ?\<Gamma>'"
        by simp
      with Cons.hyps \<Psi>(3) have "?\<Gamma>' $\<turnstile> \<Phi>" by blast        
      ultimately have "\<Gamma> $\<turnstile> (\<phi> # \<Phi>)"
        using \<Psi>(2) by fastforce
    }
    then show ?case 
      by simp
  qed
  thus ?thesis using assms by blast
qed
  
lemma (in Classical_Propositional_Logic) segmented_stronger_theory:
  assumes "\<Sigma> \<preceq> \<Gamma>"
  shows "\<Gamma> $\<turnstile> \<Sigma>"
proof -
  have "\<forall> \<Gamma>. \<Sigma> \<preceq> \<Gamma> \<longrightarrow> \<Gamma> $\<turnstile> \<Sigma>"
  proof (induct \<Sigma>)
    case Nil
    then show ?case by fastforce
  next
    case (Cons \<sigma> \<Sigma>)
    {
      fix \<Gamma>
      assume "(\<sigma> # \<Sigma>) \<preceq> \<Gamma>"
      from this obtain \<gamma> where \<gamma>: "\<gamma> \<in> set \<Gamma>" "\<turnstile> \<gamma> \<rightarrow> \<sigma>" "\<Sigma> \<preceq> (remove1 \<gamma> \<Gamma>)"
        using stronger_theory_cons_witness by blast
      let ?\<Phi> = "[(\<gamma>,\<gamma>)]"
      from \<gamma> Cons have "(remove1 \<gamma> \<Gamma>) $\<turnstile> \<Sigma>" by blast
      moreover have "mset (remove1 \<gamma> \<Gamma>) \<subseteq># mset (map (uncurry (op \<rightarrow>)) ?\<Phi> @ \<Gamma> \<ominus> (map snd ?\<Phi>))"
        by simp
      ultimately have "map (uncurry (op \<rightarrow>)) ?\<Phi> @ \<Gamma> \<ominus> (map snd ?\<Phi>) $\<turnstile> \<Sigma>"
        using segmented_deduction_assumption_mset_monotonic by blast
      moreover have "map (uncurry (op \<squnion>)) ?\<Phi> :\<turnstile> \<sigma>"
        by (simp, metis \<gamma>(2) 
                        Peirces_law 
                        disjunction_def 
                        list_deduction_def 
                        list_deduction_modus_ponens 
                        list_deduction_weaken 
                        list_implication.simps(1) 
                        list_implication.simps(2))
      moreover from \<gamma>(1) have "mset (map snd ?\<Phi>) \<subseteq># mset \<Gamma>" by simp
      ultimately have "\<Gamma> $\<turnstile> (\<sigma> # \<Sigma>)"
        using segmented_deduction.simps(2) by blast
    }
    then show ?case by blast
  qed
  thus ?thesis using assms by blast
qed
  
lemma (in Weakly_Additive_Logical_Probability) negated_segmented_deduction
  "\<^bold>\<sim> \<Gamma> $\<turnstile> (\<phi> # \<Phi>) = (\<exists> \<Psi>. mset (map fst \<Psi>) \<subseteq># mset \<Gamma> \<and> 
                        \<^bold>\<sim> (map (uncurry (op \<setminus>)) \<Psi>) :\<turnstile> \<phi> \<and> 
                        \<^bold>\<sim> (map (uncurry (op \<sqinter>)) \<Psi> @ \<Gamma> \<ominus> (map fst \<Psi>)) $\<turnstile> \<Phi>)"
  sorry

lemma (in Weakly_Additive_Logical_Probability)
  assumes "\<^bold>\<sim> \<Gamma> $\<turnstile> \<^bold>\<sim> \<Phi>"
  shows "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
proof -
  have "\<forall> \<Gamma>. \<^bold>\<sim> \<Gamma> $\<turnstile> \<^bold>\<sim> \<Phi> \<longrightarrow> (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
  proof (induct \<Phi>)
    case Nil
    then show ?case
      by (simp, metis (full_types) ex_map_conv Non_Negative sum_list_nonneg) 
  next
    case (Cons \<phi> \<Phi>)
    {
      fix \<Gamma>
      assume "\<^bold>\<sim> \<Gamma> $\<turnstile> \<^bold>\<sim> (\<phi> # \<Phi>)"
      hence "\<^bold>\<sim> \<Gamma> $\<turnstile> (\<sim> \<phi> # \<^bold>\<sim> \<Phi>)" by simp
      from this obtain \<Psi> \<Psi>' where \<Psi>:
        "mset \<Psi>' \<subseteq># mset \<Gamma>"
        "map snd \<Psi> = \<^bold>\<sim> \<Psi>'"
        "map (\<lambda> (\<chi>,\<psi>). \<sim>(\<sim> \<chi> \<sqinter> \<sim> \<psi>)) \<Psi> :\<turnstile> \<sim> \<phi>"
        "map (\<lambda> (\<chi>,\<psi>). \<sim>(\<chi> \<sqinter> \<sim> \<psi>)) \<Psi> @ (\<^bold>\<sim> \<Gamma>) \<ominus> (\<^bold>\<sim> \<Psi>') $\<turnstile> \<^bold>\<sim> \<Phi>"
        using segmented_deduction.simps(2)
              mset_sub_map_list_exists [where f="\<sim>" and \<Gamma>="\<Gamma>"]
        by metis
      let ?\<Psi>\<^sub>1 = "map (\<lambda> (\<chi>,\<psi>). \<chi> \<sqinter> \<sim> \<psi>) \<Psi>"
      let ?\<Psi>\<^sub>2 = "map (\<lambda> (\<chi>,\<psi>). \<sim> \<chi> \<sqinter> \<sim> \<psi>) \<Psi>"
      have "mset (\<^bold>\<sim> ?\<Psi>\<^sub>1 @ ((\<^bold>\<sim> \<Gamma>) \<ominus> (\<^bold>\<sim> \<Psi>'))) = mset (\<^bold>\<sim> (?\<Psi>\<^sub>1 @ \<Gamma> \<ominus> \<Psi>'))"
        using map_listSubtract_mset_equivalence \<Psi>(1)
        by (simp, blast)
      moreover
      have "(\<lambda>(\<chi>, \<psi>). \<sim> (\<chi> \<sqinter> \<sim> \<psi>)) = \<sim> \<circ> (\<lambda>(\<chi>, \<psi>). (\<chi> \<sqinter> \<sim> \<psi>))"
        by fastforce
      hence "\<^bold>\<sim> ?\<Psi>\<^sub>1 @ ((\<^bold>\<sim> \<Gamma>) \<ominus> (\<^bold>\<sim> \<Psi>')) $\<turnstile> \<^bold>\<sim> \<Phi>"
        using \<Psi>(4) by simp 
      ultimately have "\<^bold>\<sim> (?\<Psi>\<^sub>1 @ \<Gamma> \<ominus> \<Psi>') $\<turnstile> \<^bold>\<sim> \<Phi>"
        using segmented_deduction_assumption_mset_monotonic
        by (metis subset_mset.dual_order.refl)
      hence "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>(?\<Psi>\<^sub>1 @ \<Gamma> \<ominus> \<Psi>'). Pr \<gamma>)"
        using Cons.hyps
        by blast
        
        
          
      have "(\<Sum>\<phi>'\<leftarrow>(\<phi> # \<Phi>). Pr \<phi>') \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)" sorry
    }
    then show ?case by blast
  qed

(*
lemma (in Classical_Propositional_Logic) conj_cons_list_deduction [simp]:
  "(\<phi> \<sqinter> \<psi>) # \<Phi> :\<turnstile> \<chi> = \<phi> # \<psi> # \<Phi> :\<turnstile> \<chi>"
  sorry

lemma (in Classical_Propositional_Logic) subtr_cons_list_deduction [simp]:
  "(\<phi> \<setminus> \<psi>) # \<Phi> :\<turnstile> \<chi> = \<phi> # (\<sim> \<psi>) # \<Phi> :\<turnstile> \<chi>"
  unfolding subtraction_def
  by simp

lemma (in Classical_Propositional_Logic) intuitionistic_demorgans:
  "\<turnstile> \<sim>(a \<sqinter> b) \<leftrightarrow> (\<sim>a \<squnion> \<sim>b)"
  sorry
    
lemma (in Weakly_Additive_Logical_Probability)
  "2 * Pr p \<le> Pr (\<sim>(a \<sqinter> (b \<rightarrow> (\<sim> p)))) + 
              Pr (\<sim>(b \<sqinter> (a \<rightarrow> (\<sim> p)))) + 
              Pr (\<sim>((a \<rightarrow> (\<sim> p)) \<sqinter> (b \<rightarrow> (\<sim> p))))"
proof -
  have "\<turnstile> \<sim>(a \<sqinter> (b \<rightarrow> (\<sim> p))) \<leftrightarrow> (\<sim>a \<squnion> \<sim>(b \<rightarrow> (\<sim> p)))"
       "\<turnstile> \<sim>(b \<sqinter> (a \<rightarrow> (\<sim> p))) \<leftrightarrow> (\<sim>b \<squnion> \<sim>(a \<rightarrow> (\<sim> p)))"
       "\<turnstile> \<sim>((a \<rightarrow> (\<sim> p)) \<sqinter> (b \<rightarrow> (\<sim> p))) \<leftrightarrow>
          (\<sim>(a \<rightarrow> (\<sim> p)) \<squnion> \<sim> (b \<rightarrow> (\<sim> p)))"
    by (simp add: intuitionistic_demorgans)+
  moreover have "\<turnstile> \<sim>(b \<rightarrow> (\<sim> p)) \<leftrightarrow> (b \<sqinter> p)"
                "\<turnstile> \<sim>(a \<rightarrow> (\<sim> p)) \<leftrightarrow> (a \<sqinter> p)"
    by (simp add: biconditional_def, 
        simp add: conjunction_def 
                  negation_def 
                  The_Principle_of_Pseudo_Scotus)+ 
  ultimately have "\<turnstile> \<sim>(a \<sqinter> (b \<rightarrow> (\<sim> p))) \<leftrightarrow> (\<sim>a \<squnion> (b \<sqinter> p))"
                  "\<turnstile> \<sim>(b \<sqinter> (a \<rightarrow> (\<sim> p))) \<leftrightarrow> (\<sim>b \<squnion> (a \<sqinter> p))"
                  "\<turnstile> \<sim>((a \<rightarrow> (\<sim> p)) \<sqinter> (b \<rightarrow> (\<sim> p))) \<leftrightarrow>
                       ((a \<sqinter> p) \<squnion> (b \<sqinter> p))"
    by (simp add: conjunction_def negation_def)+
  hence 
    "Pr (\<sim>(a \<sqinter> (b \<rightarrow> (\<sim> p)))) + 
     Pr (\<sim>(b \<sqinter> (a \<rightarrow> (\<sim> p)))) + 
     Pr (\<sim>((a \<rightarrow> (\<sim> p)) \<sqinter> (b \<rightarrow> (\<sim> p))))
              =  
     Pr (\<sim>a \<squnion> (b \<sqinter> p)) + 
     Pr (\<sim>b \<squnion> (a \<sqinter> p)) + 
     Pr ((a \<sqinter> p) \<squnion> (b \<sqinter> p))"
    using biconditional_equivalence by auto  
*)  

  (*
lemma (in Classical_Propositional_Logic)
  "[a \<sqinter> (b \<rightarrow> p), b \<sqinter> (a \<rightarrow> p), (a \<rightarrow> p) \<sqinter> (b \<rightarrow> p)] #\<turnstile> 2 p"
  (is "[?X, ?Y, ?Z] #\<turnstile> 2 _")
proof -
  have "[?Y, ?Z] :\<turnstile> p"
  proof -
    let ?\<Gamma> = "[a \<rightarrow> p, b \<rightarrow> p, b, a \<rightarrow> p]"
    have "[?Y, ?Z] :\<turnstile> p = [b, a \<rightarrow> p, ?Z] :\<turnstile> p" by simp
    moreover have "set [b, a \<rightarrow> p, ?Z] = set [?Z, b, a \<rightarrow> p]" by fastforce
    ultimately have "[?Y, ?Z] :\<turnstile> p = [?Z, b, a \<rightarrow> p] :\<turnstile> p"
      by (smt insert_subset list.simps(15) list_deduction_monotonic set_subset_Cons)
    hence "[?Y, ?Z] :\<turnstile> p = ?\<Gamma> :\<turnstile> p" by simp
    moreover have "?\<Gamma> :\<turnstile> b" "?\<Gamma> :\<turnstile> b \<rightarrow> p"
      by (simp add: list_deduction_reflection)+
    hence "?\<Gamma> :\<turnstile> p" using list_deduction_modus_ponens by blast
    ultimately show "[?Y, ?Z] :\<turnstile> p" by simp
  qed
  moreover have "[?X, ?Y \<setminus> p, ?Z \<setminus> p] :\<turnstile> p"
    *)