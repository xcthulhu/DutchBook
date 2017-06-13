theory Logical_Probability_Full_Completeness
  imports "../Weakly_Additive/Weakly_Additive_Logical_Probability"
begin

(* TODO: Move utility stuff *)

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
    then show ?thesis
    by (simp, smt Cons.prems
              add_mset_remove_trivial 
              diff_union_swap 
              fst_conv
              image_mset_add_mset 
              insert_DiffM 
              mset.simps(2)) 
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
    then show ?thesis
    by (simp, smt Cons.prems
              add_mset_remove_trivial 
              diff_union_swap 
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

lemma (in Minimal_Logic) msub_stronger_theory_intro:    
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
  
lemma (in Minimal_Logic) stronger_theory_reflexive [simp]: "\<Gamma> \<preceq> \<Gamma>"
  using msub_stronger_theory_intro by auto

lemma (in Minimal_Logic) weakest_theory [simp]: "[] \<preceq> \<Gamma>"
  using msub_stronger_theory_intro by auto

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
                  remove1_pairs_list_projections_fst)
      moreover have "mset ?\<Phi>\<^sub>0 \<subseteq># mset \<Phi>" by simp
      with \<Phi>(3) have "\<forall> (\<gamma>,\<sigma>) \<in> set ?\<Phi>\<^sub>0. \<turnstile> \<gamma> \<rightarrow> \<sigma>" by fastforce
      ultimately have "?\<Sigma>\<^sub>0 \<preceq> remove1 \<gamma> \<Gamma>"
        unfolding stronger_theory_relation_def by blast
      moreover have "\<Sigma>' <~~> (remove1 \<sigma> \<Sigma>)" using \<open>\<Sigma> <~~> (\<sigma> # \<Sigma>')\<close>
        by (metis perm_remove_perm perm_sym remove_hd)
      moreover from \<gamma> \<Phi>(1) have "mset ?\<Sigma>\<^sub>0 = mset (remove1 \<sigma> \<Sigma>)"
        using remove1_pairs_list_projections_snd
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
              remove1_pairs_list_projections_fst
              mset_remove1)
  moreover have "mset ?\<Phi>\<^sub>0 \<subseteq># mset \<Phi>" by simp
  with \<Phi>(3) have "\<forall> (\<gamma>,\<sigma>) \<in> set ?\<Phi>\<^sub>0. \<turnstile> \<gamma> \<rightarrow> \<sigma>" by fastforce
  ultimately have "?\<Sigma>\<^sub>0 \<preceq> remove1 \<gamma> \<Gamma>"
    unfolding stronger_theory_relation_def by blast
  moreover from \<gamma> \<Phi>(1) have "mset ?\<Sigma>\<^sub>0 = mset (remove1 \<sigma> \<Sigma>)"
    using remove1_pairs_list_projections_snd
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

lemma (in Minimal_Logic) stronger_theory_right_cons:
  assumes "\<Sigma> \<preceq> \<Gamma>"
  shows "\<Sigma> \<preceq> (\<gamma> # \<Gamma>)"
proof -
  from assms obtain \<Phi> where \<Phi>:
    "map snd \<Phi> = \<Sigma>" 
    "mset (map fst \<Phi>) \<subseteq># mset \<Gamma>" 
    "\<forall>(\<gamma>, \<sigma>)\<in>set \<Phi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>"
    unfolding stronger_theory_relation_def
    by auto
  hence "mset (map fst \<Phi>) \<subseteq># mset (\<gamma> # \<Gamma>)"
    by (metis Diff_eq_empty_iff_mset 
              listSubtract.simps(2) 
              listSubtract_mset_homomorphism 
              mset_zero_iff remove1.simps(1))
  with \<Phi>(1) \<Phi>(3) show ?thesis
    unfolding stronger_theory_relation_def
    by auto
qed

lemma (in Minimal_Logic) stronger_theory_left_right_cons:
  assumes "\<turnstile> \<gamma> \<rightarrow> \<sigma>"
      and "\<Sigma> \<preceq> \<Gamma>"
    shows "(\<sigma> # \<Sigma>) \<preceq> (\<gamma> # \<Gamma>)"
proof -
  from assms(2) obtain \<Phi> where \<Phi>:
    "map snd \<Phi> = \<Sigma>" 
    "mset (map fst \<Phi>) \<subseteq># mset \<Gamma>" 
    "\<forall>(\<gamma>, \<sigma>)\<in>set \<Phi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>"
    unfolding stronger_theory_relation_def
    by auto
  let ?\<Phi> = "(\<gamma>, \<sigma>) # \<Phi>"
  from assms(1) \<Phi> have
    "map snd ?\<Phi> = \<sigma> # \<Sigma>"
    "mset (map fst ?\<Phi>) \<subseteq># mset (\<gamma> # \<Gamma>)"
    "\<forall>(\<gamma>, \<sigma>)\<in>set ?\<Phi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>"
    by fastforce+
  thus ?thesis 
    unfolding stronger_theory_relation_def
    by smt
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
  
lemma (in Classical_Propositional_Logic) segmented_msub_left_monotonic:
  assumes "mset \<Sigma> \<subseteq># mset \<Gamma>"
      and "\<Sigma> $\<turnstile> \<Phi>"
    shows "\<Gamma> $\<turnstile> \<Phi>"
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
  
lemma (in Classical_Propositional_Logic) segmented_stronger_theory_intro:
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
        using segmented_msub_left_monotonic by blast
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


lemma (in Minimal_Logic) stronger_theory_relation_alt_def:
  "\<Sigma> \<preceq> \<Gamma> = (\<exists>\<Phi>. mset (map snd \<Phi>) = mset \<Sigma> \<and> 
                 mset (map fst \<Phi>) \<subseteq># mset \<Gamma> \<and> 
                 (\<forall>(\<gamma>, \<sigma>)\<in>set \<Phi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>))"
proof -
  have "\<forall> \<Sigma> . \<Sigma> \<preceq> \<Gamma> = (\<exists>\<Phi>. mset (map snd \<Phi>) = mset \<Sigma> \<and> 
                            mset (map fst \<Phi>) \<subseteq># mset \<Gamma> \<and> 
                            (\<forall>(\<gamma>, \<sigma>)\<in>set \<Phi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>))"
  proof (induct \<Gamma>)
    case Nil
    then show ?case
      using stronger_theory_empty_list_intro 
            stronger_theory_reflexive 
      by (simp, blast) 
  next
    case (Cons \<gamma> \<Gamma>)
    {
      fix \<Sigma>
      have "\<Sigma> \<preceq> (\<gamma> # \<Gamma>) = (\<exists>\<Phi>. mset (map snd \<Phi>) = mset \<Sigma> \<and> 
                                mset (map fst \<Phi>) \<subseteq># mset (\<gamma> # \<Gamma>) \<and> 
                                (\<forall>(\<gamma>, \<sigma>) \<in> set \<Phi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>))"
      proof (rule iffI)
        assume "\<Sigma> \<preceq> (\<gamma> # \<Gamma>)"
        thus "\<exists>\<Phi>. mset (map snd \<Phi>) = mset \<Sigma> \<and> 
                  mset (map fst \<Phi>) \<subseteq># mset (\<gamma> # \<Gamma>) \<and> 
                  (\<forall>(\<gamma>, \<sigma>)\<in>set \<Phi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>)"
          unfolding stronger_theory_relation_def
          by smt
      next
        assume "\<exists>\<Phi>. mset (map snd \<Phi>) = mset \<Sigma> \<and> 
                    mset (map fst \<Phi>) \<subseteq># mset (\<gamma> # \<Gamma>) \<and> 
                    (\<forall>(\<gamma>, \<sigma>)\<in>set \<Phi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>)"
        from this obtain \<Phi> where \<Phi>:
          "mset (map snd \<Phi>) = mset \<Sigma>" 
          "mset (map fst \<Phi>) \<subseteq># mset (\<gamma> # \<Gamma>)" 
          "\<forall>(\<gamma>, \<sigma>)\<in>set \<Phi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>"
          by smt
        show "\<Sigma> \<preceq> (\<gamma> # \<Gamma>)"
        proof (cases "\<exists> \<sigma>. (\<gamma>, \<sigma>) \<in> set \<Phi>")
          assume "\<exists> \<sigma>. (\<gamma>, \<sigma>) \<in> set \<Phi>"
          from this obtain \<sigma> where \<sigma>: "(\<gamma>, \<sigma>) \<in> set \<Phi>" by auto
          let ?\<Phi> = "remove1 (\<gamma>, \<sigma>) \<Phi>"
          from \<sigma> have "mset (map snd ?\<Phi>) = mset (remove1 \<sigma> \<Sigma>)"
            using \<Phi>(1) remove1_pairs_list_projections_snd by force+
          moreover
          from \<sigma> have "mset (map fst ?\<Phi>) = mset (remove1 \<gamma> (map fst \<Phi>))"
            using \<Phi>(1) remove1_pairs_list_projections_fst by force+
          with \<Phi>(2) have "mset (map fst ?\<Phi>) \<subseteq># mset \<Gamma>"
            by (simp add: subset_eq_diff_conv)
          moreover from \<Phi>(3) have "\<forall>(\<gamma>, \<sigma>)\<in>set ?\<Phi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>"
            by fastforce
          ultimately have "remove1 \<sigma> \<Sigma> \<preceq> \<Gamma>" using Cons by blast
          from this obtain \<Psi> where \<Psi>:
            "map snd \<Psi> = remove1 \<sigma> \<Sigma>" 
            "mset (map fst \<Psi>) \<subseteq># mset \<Gamma>"
            "\<forall>(\<gamma>, \<sigma>)\<in>set \<Psi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>"
            unfolding stronger_theory_relation_def
            by blast
          let ?\<Psi> = "(\<gamma>, \<sigma>) # \<Psi>"
          from \<Psi> have "map snd ?\<Psi> = \<sigma> # (remove1 \<sigma> \<Sigma>)"
                      "mset (map fst ?\<Psi>) \<subseteq># mset (\<gamma> # \<Gamma>)"
            by simp+
          moreover from \<Phi>(3) \<sigma> have "\<turnstile> \<gamma> \<rightarrow> \<sigma>" by auto
          with \<Psi>(3) have "\<forall>(\<gamma>, \<sigma>)\<in>set ?\<Psi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>" by auto
          ultimately have "(\<sigma> # (remove1 \<sigma> \<Sigma>)) \<preceq> (\<gamma> # \<Gamma>)"
            unfolding stronger_theory_relation_def
            by smt
          moreover
          have "\<sigma> \<in> set \<Sigma>" 
            by (metis \<Phi>(1) \<sigma> set_mset_mset set_zip_rightD zip_map_fst_snd) 
          hence "\<Sigma> <~~> \<sigma> # (remove1 \<sigma> \<Sigma>)"
             by (simp add: perm_remove)
          hence "\<Sigma> \<preceq> (\<sigma> # (remove1 \<sigma> \<Sigma>))"
            using stronger_theory_reflexive 
                  stronger_theory_right_permutation 
            by blast
          ultimately show ?thesis
            using stronger_theory_transitive
            by blast
        next
          assume "\<nexists>\<sigma>. (\<gamma>, \<sigma>) \<in> set \<Phi>"
          hence "\<gamma> \<notin> set (map fst \<Phi>)" by fastforce
          with \<Phi>(2) have "mset (map fst \<Phi>) \<subseteq># mset \<Gamma>"
            by (metis diff_single_trivial 
                      in_multiset_in_set 
                      insert_DiffM2 
                      mset_remove1 
                      remove_hd 
                      subset_eq_diff_conv)
          hence "\<Sigma> \<preceq> \<Gamma>"
            using Cons \<Phi>(1) \<Phi>(3)
            by blast
          thus ?thesis
            using stronger_theory_right_cons 
            by auto
        qed
       qed
    }
    then show ?case by auto
  qed
  thus ?thesis by auto
qed

lemma (in Classical_Propositional_Logic) witness_weaker_theory:
  assumes "mset (map snd \<Sigma>) \<subseteq># mset \<Gamma>"
  shows "map (uncurry (op \<squnion>)) \<Sigma> \<preceq> \<Gamma>"
proof -
  have "\<forall> \<Gamma>. mset (map snd \<Sigma>) \<subseteq># mset \<Gamma> \<longrightarrow> map (uncurry (op \<squnion>)) \<Sigma> \<preceq> \<Gamma>"
  proof (induct \<Sigma>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<sigma> \<Sigma>)
    {
      fix \<Gamma>
      assume "mset (map snd (\<sigma> # \<Sigma>)) \<subseteq># mset \<Gamma>"
      hence "mset (map snd \<Sigma>) \<subseteq># mset (remove1 (snd \<sigma>) \<Gamma>)"
        by (simp add: insert_subset_eq_iff)
      with Cons have "map (uncurry (op \<squnion>)) \<Sigma> \<preceq> remove1 (snd \<sigma>) \<Gamma>" by blast
      moreover have "uncurry (op \<squnion>) = (\<lambda> \<sigma>. fst \<sigma> \<squnion> snd \<sigma>)" by fastforce
      hence "uncurry (op \<squnion>) \<sigma> = fst \<sigma> \<squnion> snd \<sigma>" by simp
      moreover have "\<turnstile> snd \<sigma> \<rightarrow> (fst \<sigma> \<squnion> snd \<sigma>)"
        unfolding disjunction_def
        by (simp add: Axiom_1)
      ultimately have "map (uncurry op \<squnion>) (\<sigma> # \<Sigma>) \<preceq> (snd \<sigma> # (remove1 (snd \<sigma>) \<Gamma>))"
        by (simp add: stronger_theory_left_right_cons)
      moreover have "mset (snd \<sigma> # (remove1 (snd \<sigma>) \<Gamma>)) = mset \<Gamma>" 
        using \<open>mset (map snd (\<sigma> # \<Sigma>)) \<subseteq># mset \<Gamma>\<close>
        by (simp, meson insert_DiffM mset_subset_eq_insertD) 
      ultimately have "map (uncurry op \<squnion>) (\<sigma> # \<Sigma>) \<preceq> \<Gamma>"
        unfolding stronger_theory_relation_alt_def
        by simp
    }
    then show ?case by blast
  qed
  with assms show ?thesis by simp
qed
    
lemma (in Classical_Propositional_Logic) segmented_deduction_one_collapse [simp]:
  "\<Gamma> $\<turnstile> [\<phi>] = \<Gamma> :\<turnstile> \<phi>"
proof (rule iffI)
  assume "\<Gamma> $\<turnstile> [\<phi>]"
  from this obtain \<Sigma> where 
    \<Sigma>: "mset (map snd \<Sigma>) \<subseteq># mset \<Gamma>"
       "map (uncurry (op \<squnion>)) \<Sigma> :\<turnstile> \<phi>"
    by auto
  hence "map (uncurry (op \<squnion>)) \<Sigma> \<preceq> \<Gamma>"
    using witness_weaker_theory by blast 
  thus "\<Gamma> :\<turnstile> \<phi>" using \<Sigma>(2)
    using stronger_theory_deduction_monotonic by blast 
next
  assume "\<Gamma> :\<turnstile> \<phi>"
  let ?\<Sigma> = "map (\<lambda> \<gamma>. (\<bottom>, \<gamma>)) \<Gamma>"
  have "\<Gamma> \<preceq> map (uncurry (op \<squnion>)) ?\<Sigma>"
  proof (induct \<Gamma>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<gamma> \<Gamma>)
    have "\<turnstile> (\<bottom> \<squnion> \<gamma>) \<rightarrow> \<gamma>"
      unfolding disjunction_def
      using Ex_Falso_Quodlibet Modus_Ponens excluded_middle_elimination 
      by blast
    then show ?case using Cons
      by (simp add: stronger_theory_left_right_cons) 
  qed
  hence "map (uncurry (op \<squnion>)) ?\<Sigma> :\<turnstile> \<phi>"
    using \<open>\<Gamma> :\<turnstile> \<phi>\<close> stronger_theory_deduction_monotonic by blast
  moreover have "mset (map snd ?\<Sigma>) \<subseteq># mset \<Gamma>" by (induct \<Gamma>, simp+)
  ultimately show "\<Gamma> $\<turnstile> [\<phi>]"
    using segmented_deduction.simps(1) 
          segmented_deduction.simps(2) 
    by blast 
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
  have "?\<sigma> \<in># mset \<Sigma> - mset (map snd \<Psi>)"
    using Cons.prems
    by (simp, smt cancel_ab_semigroup_add_class.diff_right_commute 
                  diff_single_trivial 
                  insert_subset_eq_iff 
                  mset_subset_eq_insertD 
                  multi_drop_mem_not_eq 
                  subset_mset.diff_add 
                  subset_mset_def)
  hence "?\<sigma> \<in># mset (map snd \<Delta>) - mset (map snd \<Psi>)"
    using assms(2)
    by (metis listSubtract_monotonic 
              listSubtract_mset_homomorphism 
              mset_subset_eqD)
  moreover have "snd \<circ> (\<lambda> (\<psi>, \<sigma>, _). (\<psi>, \<sigma>)) = snd \<circ> (\<lambda> (_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>))" by auto
  hence "map snd (?\<Delta>\<^sub>\<Omega>) = map snd (map (\<lambda> (\<psi>, \<sigma>, _). (\<psi>, \<sigma>)) \<Omega>)"
    by fastforce
  hence "map snd (?\<Delta>\<^sub>\<Omega>) = map snd \<Psi>"
    using \<Omega>(1) by simp
  ultimately have "?\<sigma> \<in># mset (map snd \<Delta>) - mset (map snd ?\<Delta>\<^sub>\<Omega>)"
    by simp
  hence "?\<sigma> \<in># image_mset snd (mset \<Delta> - mset ?\<Delta>\<^sub>\<Omega>)"
    using \<Omega>(2) by (smt image_mset_Diff mset_map)
  from this obtain \<gamma> where \<gamma>: 
    "(\<gamma>, ?\<sigma>) \<in># mset \<Delta> - mset ?\<Delta>\<^sub>\<Omega>"
    by (smt imageE in_image_mset prod.collapse)
  let ?\<Omega> = "(?\<psi>, ?\<sigma>, \<gamma>) # \<Omega>"
  have "map (\<lambda> (\<psi>, \<sigma>, _). (\<psi>, \<sigma>)) ?\<Omega> = \<psi> # \<Psi>"
    using \<Omega>(1) by simp
  moreover have "mset (map (\<lambda> (_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>)) ?\<Omega>) \<subseteq># mset \<Delta>"
    using \<Omega>(2) \<gamma>
    by (smt add_diff_cancel_left' 
            add_mset_remove_trivial 
            case_prod_conv 
            list.set_intros(1) 
            list.simps(9) 
            mset.simps(2) 
            set_mset_mset 
            single_subset_iff 
            subset_mset.add_le_cancel_left 
            subset_mset.diff_add 
            subset_mset.le_iff_add) 
  ultimately show ?case by smt
qed

lemma (in Minimal_Logic) stronger_theory_combine:
  assumes "\<Phi> \<preceq> \<Delta>"
      and "\<Psi> \<preceq> \<Gamma>"
    shows "(\<Phi> @ \<Psi>) \<preceq> (\<Delta> @ \<Gamma>)"
proof -
  have "\<forall> \<Phi>. \<Phi> \<preceq> \<Delta> \<longrightarrow> (\<Phi> @ \<Psi>) \<preceq> (\<Delta> @ \<Gamma>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case
      using assms(2) stronger_theory_empty_list_intro by fastforce 
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Phi>
      assume "\<Phi> \<preceq> (\<delta> # \<Delta>)"
      from this obtain \<Sigma> where \<Sigma>:
        "map snd \<Sigma> = \<Phi>"
        "mset (map fst \<Sigma>) \<subseteq># mset (\<delta> # \<Delta>)" 
        "\<forall> (\<delta>,\<phi>) \<in> set \<Sigma>. \<turnstile> \<delta> \<rightarrow> \<phi>"
        unfolding stronger_theory_relation_def
        by blast
      have "(\<Phi> @ \<Psi>) \<preceq> ((\<delta> # \<Delta>) @ \<Gamma>)"
      proof (cases "\<exists> \<phi> . (\<delta>, \<phi>) \<in> set \<Sigma>")
        assume "\<exists> \<phi> . (\<delta>, \<phi>) \<in> set \<Sigma>"
        from this obtain \<phi> where \<phi>: "(\<delta>, \<phi>) \<in> set \<Sigma>" by auto
        let ?\<Sigma> = "remove1 (\<delta>, \<phi>) \<Sigma>"
        from \<phi> \<Sigma>(1) have "mset (map snd ?\<Sigma>) = mset (remove1 \<phi> \<Phi>)"
          using remove1_pairs_list_projections_snd by fastforce
        moreover from \<phi> have "mset (map fst ?\<Sigma>) = mset (remove1 \<delta> (map fst \<Sigma>))"
          using remove1_pairs_list_projections_fst by fastforce
        hence "mset (map fst ?\<Sigma>) \<subseteq># mset \<Delta>"
          using \<Sigma>(2) mset.simps(1) subset_eq_diff_conv by force
        moreover from \<Sigma>(3) have "\<forall> (\<delta>,\<phi>) \<in> set ?\<Sigma>. \<turnstile> \<delta> \<rightarrow> \<phi>" by auto
        ultimately have "remove1 \<phi> \<Phi> \<preceq> \<Delta>"
          unfolding stronger_theory_relation_alt_def by blast
        hence "(remove1 \<phi> \<Phi> @ \<Psi>) \<preceq> (\<Delta> @ \<Gamma>)" using Cons by auto
        from this obtain \<Omega> where \<Omega>:
          "map snd \<Omega> = (remove1 \<phi> \<Phi>) @ \<Psi>"
          "mset (map fst \<Omega>) \<subseteq># mset (\<Delta> @ \<Gamma>)" 
          "\<forall> (\<alpha>,\<beta>) \<in> set \<Omega>. \<turnstile> \<alpha> \<rightarrow> \<beta>"
          unfolding stronger_theory_relation_def
          by blast
        let ?\<Omega> = "(\<delta>, \<phi>) # \<Omega>"
        have "map snd ?\<Omega> = \<phi> # remove1 \<phi> \<Phi> @ \<Psi>"
          using \<Omega>(1) by simp
        moreover have "mset (map fst ?\<Omega>) \<subseteq># mset ((\<delta> # \<Delta>) @ \<Gamma>)"
          using \<Omega>(2) by simp
        moreover have "\<turnstile> \<delta> \<rightarrow> \<phi>"
          using \<Sigma>(3) \<phi> by blast
        hence "\<forall> (\<alpha>,\<beta>) \<in> set ?\<Omega>. \<turnstile> \<alpha> \<rightarrow> \<beta>" using \<Omega>(3) by auto
        ultimately have "(\<phi> # remove1 \<phi> \<Phi> @ \<Psi>) \<preceq> ((\<delta> # \<Delta>) @ \<Gamma>)"
          by (metis stronger_theory_relation_def)
        moreover have "\<phi> \<in> set \<Phi>"
          using \<Sigma>(1) \<phi> by force
        hence "(\<phi> # remove1 \<phi> \<Phi>) <~~> \<Phi>"
          by (simp add: perm_remove perm_sym)
        hence "(\<phi> # remove1 \<phi> \<Phi> @ \<Psi>) <~~> \<Phi> @ \<Psi>"
          by (metis append_Cons perm_append2)  
        ultimately show ?thesis
          using stronger_theory_left_permutation by blast 
      next
        assume "\<nexists>\<phi>. (\<delta>, \<phi>) \<in> set \<Sigma>"
        hence "\<delta> \<notin> set (map fst \<Sigma>)"
          by auto
        hence "mset (map fst \<Sigma>) \<subseteq># mset \<Delta>"
          by (smt \<Sigma>(2) 
                  diff_single_trivial 
                  mset.simps(1) 
                  mset.simps(2) 
                  mset_append 
                  mset_eq_perm 
                  perm_append_single 
                  set_mset_mset 
                  subset_eq_diff_conv)
        with \<Sigma>(1) \<Sigma>(3) have "\<Phi> \<preceq> \<Delta>"
          unfolding stronger_theory_relation_def
          by blast
        hence "(\<Phi> @ \<Psi>) \<preceq> (\<Delta> @ \<Gamma>)" using Cons by auto
        then show ?thesis
          by (simp add: stronger_theory_right_cons) 
      qed
    }
    then show ?case by blast
  qed
  thus ?thesis using assms by blast
qed
    
lemma (in Classical_Propositional_Logic) segmented_empty_deduction [simp]:
  "[] $\<turnstile> \<Phi> = (\<forall> \<phi> \<in> set \<Phi>. \<turnstile> \<phi>)"
  by (induct \<Phi>, simp, rule iffI, fastforce+)
    
lemma (in Classical_Propositional_Logic) segmented_stronger_theory_left_monotonic:
  assumes "\<Sigma> \<preceq> \<Gamma>"
      and "\<Sigma> $\<turnstile> \<Phi>"
    shows "\<Gamma> $\<turnstile> \<Phi>"
proof -
  have "\<forall> \<Sigma> \<Gamma>. \<Sigma> \<preceq> \<Gamma> \<longrightarrow> \<Sigma> $\<turnstile> \<Phi> \<longrightarrow> \<Gamma> $\<turnstile> \<Phi>"
  proof (induct \<Phi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<phi> \<Phi>)
    {
      fix \<Sigma> \<Gamma>
      assume "\<Sigma> $\<turnstile> (\<phi> # \<Phi>)" "\<Sigma> \<preceq> \<Gamma>"
      from this obtain \<Psi> \<Delta> where 
        \<Psi>: "mset (map snd \<Psi>) \<subseteq># mset \<Sigma>"
           "map (uncurry (op \<squnion>)) \<Psi> :\<turnstile> \<phi>"
           "map (uncurry (op \<rightarrow>)) \<Psi> @ \<Sigma> \<ominus> (map snd \<Psi>) $\<turnstile> \<Phi>"
        and 
        \<Delta>: "map snd \<Delta> = \<Sigma>"
           "mset (map fst \<Delta>) \<subseteq># mset \<Gamma>" 
           "\<forall> (\<gamma>,\<sigma>) \<in> set \<Delta>. \<turnstile> \<gamma> \<rightarrow> \<sigma>"
        unfolding stronger_theory_relation_def
        by fastforce
      from \<open>mset (map snd \<Psi>) \<subseteq># mset \<Sigma>\<close>
           \<open>map snd \<Delta> = \<Sigma>\<close>
      obtain \<Omega> where \<Omega>:
        "map (\<lambda> (\<psi>, \<sigma>, _). (\<psi>, \<sigma>)) \<Omega> = \<Psi>"
        "mset (map (\<lambda> (_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>)) \<Omega>) \<subseteq># mset \<Delta>"
        using triple_list_exists by blast
      let ?\<Theta> = "map (\<lambda> (\<psi>, _, \<gamma>). (\<psi>, \<gamma>)) \<Omega>"
      have "map snd ?\<Theta> = map fst (map (\<lambda> (_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>)) \<Omega>)"
        by auto
      hence "mset (map snd ?\<Theta>) \<subseteq># mset \<Gamma>"
        using \<Omega>(2) \<Delta>(2) map_monotonic subset_mset.order.trans
        by smt
      moreover have "map (uncurry (op \<squnion>)) \<Psi> \<preceq> map (uncurry (op \<squnion>)) ?\<Theta>"
      proof -
        let ?\<Phi> = "map (\<lambda> (\<psi>, \<sigma>, \<gamma>). (\<psi> \<squnion> \<gamma>, \<psi> \<squnion> \<sigma>)) \<Omega>"
        have "map snd ?\<Phi> = map (uncurry (op \<squnion>)) \<Psi>"
          using \<Omega>(1) by fastforce
        moreover have "map fst ?\<Phi> = map (uncurry (op \<squnion>)) ?\<Theta>"
          by fastforce
        hence "mset (map fst ?\<Phi>) \<subseteq># mset (map (uncurry (op \<squnion>)) ?\<Theta>)"
          by (smt subset_mset.dual_order.refl)
        moreover
        have "mset (map (\<lambda>(\<psi>, \<sigma>, _). (\<psi>, \<sigma>)) \<Omega>) \<subseteq># mset \<Psi>"
          using \<Omega>(1) by simp
        hence "\<forall> (\<phi>,\<chi>) \<in> set ?\<Phi>. \<turnstile> \<phi> \<rightarrow> \<chi>" using \<Omega>(2)
        proof (induct \<Omega>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<omega> \<Omega>)
          let ?\<Phi> = "map (\<lambda> (\<psi>, \<sigma>, \<gamma>). (\<psi> \<squnion> \<gamma>, \<psi> \<squnion> \<sigma>)) (\<omega> # \<Omega>)"
          let ?\<Phi>' = "map (\<lambda> (\<psi>, \<sigma>, \<gamma>). (\<psi> \<squnion> \<gamma>, \<psi> \<squnion> \<sigma>)) \<Omega>"
          have "mset (map (\<lambda>(\<psi>, \<sigma>, _). (\<psi>, \<sigma>)) \<Omega>) \<subseteq># mset \<Psi>"
               "mset (map (\<lambda>(_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>)) \<Omega>) \<subseteq># mset \<Delta>"
            using Cons.prems(1) Cons.prems(2) subset_mset.dual_order.trans by fastforce+
          with Cons have "\<forall> (\<phi>,\<chi>) \<in> set ?\<Phi>'. \<turnstile> \<phi> \<rightarrow> \<chi>" by fastforce
          moreover
          let ?\<psi> = "(\<lambda> (\<psi>, _, _). \<psi>) \<omega>"
          let ?\<sigma> = "(\<lambda> (_, \<sigma>, _). \<sigma>) \<omega>"
          let ?\<gamma> = "(\<lambda> (_, _, \<gamma>). \<gamma>) \<omega>"
          have "(\<lambda>(_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>)) = (\<lambda> \<omega>. ((\<lambda> (_, _, \<gamma>). \<gamma>) \<omega>,(\<lambda> (_, \<sigma>, _). \<sigma>) \<omega>))" by auto
          hence "(\<lambda>(_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>)) \<omega> = (?\<gamma>, ?\<sigma>)" by smt
          hence "\<turnstile> ?\<gamma> \<rightarrow> ?\<sigma>" 
            using Cons.prems(2) mset_subset_eqD \<Delta>(3) 
            by fastforce
          hence "\<turnstile> (?\<psi> \<squnion> ?\<gamma>) \<rightarrow> (?\<psi> \<squnion> ?\<sigma>)"
            unfolding disjunction_def
            using Modus_Ponens hypothetical_syllogism 
            by blast
          moreover have 
            "(\<lambda>(\<psi>, \<sigma>, \<gamma>). (\<psi> \<squnion> \<gamma>, \<psi> \<squnion> \<sigma>)) = 
             (\<lambda> \<omega>. (((\<lambda> (\<psi>, _, _). \<psi>) \<omega>) \<squnion> ((\<lambda> (_, _, \<gamma>). \<gamma>) \<omega>),
                    ((\<lambda> (\<psi>, _, _). \<psi>) \<omega>) \<squnion> ((\<lambda> (_, \<sigma>, _). \<sigma>) \<omega>)))"
            by auto
          hence "(\<lambda>(\<psi>, \<sigma>, \<gamma>). (\<psi> \<squnion> \<gamma>, \<psi> \<squnion> \<sigma>)) \<omega> = ((?\<psi> \<squnion> ?\<gamma>), (?\<psi> \<squnion> ?\<sigma>))" by smt
          ultimately show ?case by simp
        qed
        ultimately show ?thesis
          unfolding stronger_theory_relation_def
          by blast
      qed
      with \<Psi>(2) have "map (uncurry (op \<squnion>)) ?\<Theta> :\<turnstile> \<phi>"
        by (smt stronger_theory_deduction_monotonic)
      moreover have
        "(map (uncurry (op \<rightarrow>)) \<Psi> @ \<Sigma> \<ominus> (map snd \<Psi>)) \<preceq> 
         (map (uncurry (op \<rightarrow>)) ?\<Theta> @ \<Gamma> \<ominus> (map snd ?\<Theta>))"
      proof -
        have "map (uncurry (op \<rightarrow>)) \<Psi> \<preceq> map (uncurry (op \<rightarrow>)) ?\<Theta>"
        proof -
          let ?\<Phi> = "map (\<lambda> (\<psi>, \<sigma>, \<gamma>). (\<psi> \<rightarrow> \<gamma>, \<psi> \<rightarrow> \<sigma>)) \<Omega>"
          have "map snd ?\<Phi> = map (uncurry (op \<rightarrow>)) \<Psi>"
            using \<Omega>(1) by fastforce
          moreover have "map fst ?\<Phi> = map (uncurry (op \<rightarrow>)) ?\<Theta>"
            by fastforce
          hence "mset (map fst ?\<Phi>) \<subseteq># mset (map (uncurry (op \<rightarrow>)) ?\<Theta>)"
            by (smt subset_mset.dual_order.refl)
          moreover
          have "mset (map (\<lambda>(\<psi>, \<sigma>, _). (\<psi>, \<sigma>)) \<Omega>) \<subseteq># mset \<Psi>"
            using \<Omega>(1) by simp
          hence "\<forall> (\<phi>,\<chi>) \<in> set ?\<Phi>. \<turnstile> \<phi> \<rightarrow> \<chi>" using \<Omega>(2)
          proof (induct \<Omega>)
            case Nil
            then show ?case by simp
          next
            case (Cons \<omega> \<Omega>)
            let ?\<Phi> = "map (\<lambda> (\<psi>, \<sigma>, \<gamma>). (\<psi> \<rightarrow> \<gamma>, \<psi> \<rightarrow> \<sigma>)) (\<omega> # \<Omega>)"
            let ?\<Phi>' = "map (\<lambda> (\<psi>, \<sigma>, \<gamma>). (\<psi> \<rightarrow> \<gamma>, \<psi> \<rightarrow> \<sigma>)) \<Omega>"
            have "mset (map (\<lambda>(\<psi>, \<sigma>, _). (\<psi>, \<sigma>)) \<Omega>) \<subseteq># mset \<Psi>"
                 "mset (map (\<lambda>(_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>)) \<Omega>) \<subseteq># mset \<Delta>"
              using Cons.prems(1) Cons.prems(2) subset_mset.dual_order.trans by fastforce+
            with Cons have "\<forall> (\<phi>,\<chi>) \<in> set ?\<Phi>'. \<turnstile> \<phi> \<rightarrow> \<chi>" by fastforce
            moreover
            let ?\<psi> = "(\<lambda> (\<psi>, _, _). \<psi>) \<omega>"
            let ?\<sigma> = "(\<lambda> (_, \<sigma>, _). \<sigma>) \<omega>"
            let ?\<gamma> = "(\<lambda> (_, _, \<gamma>). \<gamma>) \<omega>"
            have "(\<lambda>(_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>)) = (\<lambda> \<omega>. ((\<lambda> (_, _, \<gamma>). \<gamma>) \<omega>,(\<lambda> (_, \<sigma>, _). \<sigma>) \<omega>))" by auto
            hence "(\<lambda>(_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>)) \<omega> = (?\<gamma>, ?\<sigma>)" by smt
            hence "\<turnstile> ?\<gamma> \<rightarrow> ?\<sigma>" 
              using Cons.prems(2) mset_subset_eqD \<Delta>(3) 
              by fastforce
            hence "\<turnstile> (?\<psi> \<rightarrow> ?\<gamma>) \<rightarrow> (?\<psi> \<rightarrow> ?\<sigma>)"
              using Modus_Ponens hypothetical_syllogism 
              by blast
            moreover have 
              "(\<lambda>(\<psi>, \<sigma>, \<gamma>). (\<psi> \<rightarrow> \<gamma>, \<psi> \<rightarrow> \<sigma>)) = 
               (\<lambda> \<omega>. (((\<lambda> (\<psi>, _, _). \<psi>) \<omega>) \<rightarrow> ((\<lambda> (_, _, \<gamma>). \<gamma>) \<omega>),
                      ((\<lambda> (\<psi>, _, _). \<psi>) \<omega>) \<rightarrow> ((\<lambda> (_, \<sigma>, _). \<sigma>) \<omega>)))"
              by auto
            hence "(\<lambda>(\<psi>, \<sigma>, \<gamma>). (\<psi> \<rightarrow> \<gamma>, \<psi> \<rightarrow> \<sigma>)) \<omega> = ((?\<psi> \<rightarrow> ?\<gamma>), (?\<psi> \<rightarrow> ?\<sigma>))" by smt
            ultimately show ?case by simp
          qed
          ultimately show ?thesis
            unfolding stronger_theory_relation_def
            by blast
        qed
        moreover
        have "(\<Sigma> \<ominus> (map snd \<Psi>)) \<preceq> (\<Gamma> \<ominus> (map snd ?\<Theta>))"
        proof -
          let ?\<Delta> = "\<Delta> \<ominus> (map (\<lambda> (_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>)) \<Omega>)"
          have "mset (map fst ?\<Delta>) \<subseteq># mset (\<Gamma> \<ominus> (map snd ?\<Theta>))"
            using \<Delta>(2)
            by (smt \<Omega>(2) 
                    \<open>map snd (map (\<lambda>(\<psi>, _, \<gamma>). (\<psi>, \<gamma>)) \<Omega>) = 
                     map fst (map (\<lambda>(_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>)) \<Omega>)\<close> 
                    listSubtract_monotonic 
                    map_listSubtract_mset_equivalence)
          moreover
          from \<Omega>(2) have "mset ?\<Delta> \<subseteq># mset \<Delta>" by simp
          hence "\<forall> (\<gamma>,\<sigma>) \<in> set ?\<Delta>. \<turnstile> \<gamma> \<rightarrow> \<sigma>"
            using \<Delta>(3)
            by (smt mset_subset_eqD set_mset_mset)
          moreover 
          have "map snd (map (\<lambda>(_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>)) \<Omega>) = map snd \<Psi>"
            using \<Omega>(1)
            by (induct \<Omega>, simp, fastforce)
          hence "mset (map snd ?\<Delta>) = mset (\<Sigma> \<ominus> (map snd \<Psi>))" 
            by (smt \<Delta>(1) \<Omega>(2) map_listSubtract_mset_equivalence) 
          ultimately show ?thesis
            by (smt stronger_theory_relation_alt_def)        
        qed
        ultimately show ?thesis using stronger_theory_combine by blast
      qed
      hence "map (uncurry (op \<rightarrow>)) ?\<Theta> @ \<Gamma> \<ominus> (map snd ?\<Theta>) $\<turnstile> \<Phi>"
        using \<Psi>(3) Cons by smt
      ultimately have "\<Gamma> $\<turnstile> (\<phi> # \<Phi>)"
        by (smt segmented_deduction.simps(2))
    }    
    then show ?case by blast
  qed
  with assms show ?thesis by blast
qed
  
lemma (in Classical_Propositional_Logic) negated_segmented_deduction:
  "\<^bold>\<sim> \<Gamma> $\<turnstile> (\<phi> # \<Phi>) = (\<exists> \<Psi>. mset (map fst \<Psi>) \<subseteq># mset \<Gamma> \<and> 
                        \<^bold>\<sim> (map (uncurry (op \<setminus>)) \<Psi>) :\<turnstile> \<phi> \<and> 
                        \<^bold>\<sim> (map (uncurry (op \<sqinter>)) \<Psi> @ \<Gamma> \<ominus> (map fst \<Psi>)) $\<turnstile> \<Phi>)"
proof (rule iffI)
  assume "\<^bold>\<sim> \<Gamma> $\<turnstile> (\<phi> # \<Phi>)"
  from this obtain \<Psi> where \<Psi>:
    "mset (map snd \<Psi>) \<subseteq># mset (\<^bold>\<sim> \<Gamma>)"
    "map (uncurry (op \<squnion>)) \<Psi> :\<turnstile> \<phi>"
    "map (uncurry (op \<rightarrow>)) \<Psi> @ \<^bold>\<sim> \<Gamma> \<ominus> map snd \<Psi> $\<turnstile> \<Phi>"
    using segmented_deduction.simps(2)
    by metis
  from this obtain \<Delta> where \<Delta>:
    "mset \<Delta> \<subseteq># mset \<Gamma>"
    "map snd \<Psi> = \<^bold>\<sim> \<Delta>"
    using mset_sub_map_list_exists [where f="\<sim>" and \<Gamma>="\<Gamma>"]
    by metis
  let ?\<Psi> = "zip \<Delta> (map fst \<Psi>)"
  from \<Delta>(2) have "map fst ?\<Psi> = \<Delta>"
    by (metis length_map map_fst_zip)
  with \<Delta>(1) have "mset (map fst ?\<Psi>) \<subseteq># mset \<Gamma>"
    by simp
  moreover have "\<forall> \<Delta>. map snd \<Psi> = \<^bold>\<sim> \<Delta> \<longrightarrow>
                      map (uncurry (op \<squnion>)) \<Psi> \<preceq> \<^bold>\<sim> (map (uncurry (op \<setminus>)) (zip \<Delta> (map fst \<Psi>)))"
  proof (induct \<Psi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<psi> \<Psi>)
    let ?\<psi> = "fst \<psi>"
    {
      fix \<Delta>
      assume "map snd (\<psi> # \<Psi>) = \<^bold>\<sim> \<Delta>"
      from this obtain \<gamma> where \<gamma>: "\<sim> \<gamma> = snd \<psi>" "\<gamma> = hd \<Delta>" by auto
      from \<open>map snd (\<psi> # \<Psi>) = \<^bold>\<sim> \<Delta>\<close> have "map snd \<Psi> = \<^bold>\<sim> (tl \<Delta>)" by auto
      with Cons.hyps have 
        "map (uncurry (op \<squnion>)) \<Psi> \<preceq> \<^bold>\<sim> (map (uncurry (op \<setminus>)) (zip (tl \<Delta>) (map fst \<Psi>)))"
        by auto
      moreover
      {
        fix \<psi> \<gamma>
        have "\<turnstile> \<sim>(\<gamma> \<setminus> \<psi>) \<rightarrow> (\<psi> \<squnion> \<sim> \<gamma>)"
          unfolding disjunction_def
                    subtraction_def
                    conjunction_def
                    negation_def
          by (meson Modus_Ponens 
                    flip_implication 
                    hypothetical_syllogism)
      } note tautology = this
      have "(uncurry (op \<squnion>)) = (\<lambda> \<psi>. (fst \<psi>) \<squnion> (snd \<psi>))"
        by fastforce
      with \<gamma> have "(uncurry (op \<squnion>)) \<psi> = ?\<psi> \<squnion> \<sim> \<gamma>"
        by simp
      with tautology have "\<turnstile> \<sim>(\<gamma> \<setminus> ?\<psi>) \<rightarrow> (uncurry op \<squnion>) \<psi>"
        by simp
      ultimately have "map (uncurry op \<squnion>) (\<psi> # \<Psi>) \<preceq>
                       \<^bold>\<sim> (map (uncurry op \<setminus>) ((zip ((hd \<Delta>) # (tl \<Delta>)) (map fst (\<psi> # \<Psi>)))))"
        using stronger_theory_left_right_cons \<gamma>(2) 
        by simp
      hence "map (uncurry op \<squnion>) (\<psi> # \<Psi>) \<preceq> 
            \<^bold>\<sim> (map (uncurry op \<setminus>) (zip \<Delta> (map fst (\<psi> # \<Psi>))))"
        using \<open>map snd (\<psi> # \<Psi>) = \<^bold>\<sim> \<Delta>\<close> by force
    }
    thus ?case by blast
  qed
  with \<Psi>(2) \<Delta>(2) have "\<^bold>\<sim> (map (uncurry (op \<setminus>)) ?\<Psi>) :\<turnstile> \<phi>"
    using stronger_theory_deduction_monotonic by blast
  moreover
  have "(map (uncurry (op \<rightarrow>)) \<Psi> @ \<^bold>\<sim> \<Gamma> \<ominus> map snd \<Psi>) \<preceq> 
        \<^bold>\<sim> (map (uncurry (op \<sqinter>)) ?\<Psi> @ \<Gamma> \<ominus> (map fst ?\<Psi>))"
  proof -
    from \<Delta>(1) have "mset (\<^bold>\<sim> \<Gamma> \<ominus> \<^bold>\<sim> \<Delta>) = mset (\<^bold>\<sim> (\<Gamma> \<ominus> \<Delta>))"
      by (simp add: image_mset_Diff)
    hence "mset (\<^bold>\<sim> \<Gamma> \<ominus> map snd \<Psi>) = mset (\<^bold>\<sim> (\<Gamma> \<ominus> map fst ?\<Psi>))"
      using \<Psi>(1) \<Delta>(2) \<open>map fst ?\<Psi> = \<Delta>\<close> by simp
    hence "(\<^bold>\<sim> \<Gamma> \<ominus> map snd \<Psi>) \<preceq> \<^bold>\<sim> (\<Gamma> \<ominus> map fst ?\<Psi>)"
      by (simp add: msub_stronger_theory_intro)
    moreover have "\<forall> \<Delta>. map snd \<Psi> = \<^bold>\<sim> \<Delta> \<longrightarrow>
                         map (uncurry (op \<rightarrow>)) \<Psi> \<preceq> \<^bold>\<sim> (map (uncurry (op \<sqinter>)) (zip \<Delta> (map fst \<Psi>)))"
    proof (induct \<Psi>)
      case Nil
      then show ?case by simp
    next
      case (Cons \<psi> \<Psi>)
      let ?\<psi> = "fst \<psi>"
      {
        fix \<Delta>
        assume "map snd (\<psi> # \<Psi>) = \<^bold>\<sim> \<Delta>"
        from this obtain \<gamma> where \<gamma>: "\<sim> \<gamma> = snd \<psi>" "\<gamma> = hd \<Delta>" by auto
        from \<open>map snd (\<psi> # \<Psi>) = \<^bold>\<sim> \<Delta>\<close> have "map snd \<Psi> = \<^bold>\<sim> (tl \<Delta>)" by auto
        with Cons.hyps have 
          "map (uncurry (op \<rightarrow>)) \<Psi> \<preceq> \<^bold>\<sim> (map (uncurry (op \<sqinter>)) (zip (tl \<Delta>) (map fst \<Psi>)))"
          by simp
        moreover
        {
          fix \<psi> \<gamma>
          have "\<turnstile> \<sim>(\<gamma> \<sqinter> \<psi>) \<rightarrow> (\<psi> \<rightarrow> \<sim> \<gamma>)"
            unfolding disjunction_def
                      conjunction_def
                      negation_def
            by (meson Modus_Ponens 
                      flip_implication 
                      hypothetical_syllogism)
        } note tautology = this
        have "(uncurry (op \<rightarrow>)) = (\<lambda> \<psi>. (fst \<psi>) \<rightarrow> (snd \<psi>))"
          by fastforce
        with \<gamma> have "(uncurry (op \<rightarrow>)) \<psi> = ?\<psi> \<rightarrow> \<sim> \<gamma>"
          by simp
        with tautology have "\<turnstile> \<sim>(\<gamma> \<sqinter> ?\<psi>) \<rightarrow> (uncurry op \<rightarrow>) \<psi>"
          by simp
        ultimately have "map (uncurry op \<rightarrow>) (\<psi> # \<Psi>) \<preceq>
                         \<^bold>\<sim> (map (uncurry op \<sqinter>) ((zip ((hd \<Delta>) # (tl \<Delta>)) (map fst (\<psi> # \<Psi>)))))"
          using stronger_theory_left_right_cons \<gamma>(2) 
          by simp
        hence "map (uncurry op \<rightarrow>) (\<psi> # \<Psi>) \<preceq> 
              \<^bold>\<sim> (map (uncurry op \<sqinter>) (zip \<Delta> (map fst (\<psi> # \<Psi>))))"
          using \<open>map snd (\<psi> # \<Psi>) = \<^bold>\<sim> \<Delta>\<close> by force
      }
      then show ?case by blast
    qed
    ultimately have "(map (uncurry (op \<rightarrow>)) \<Psi> @ \<^bold>\<sim> \<Gamma> \<ominus> map snd \<Psi>) \<preceq>
                     (\<^bold>\<sim> (map (uncurry (op \<sqinter>)) ?\<Psi>) @ \<^bold>\<sim> (\<Gamma> \<ominus> (map fst ?\<Psi>)))"
      using stronger_theory_combine \<Delta>(2)
      by smt
    thus ?thesis by simp
  qed
  hence "\<^bold>\<sim> (map (uncurry (op \<sqinter>)) ?\<Psi> @ \<Gamma> \<ominus> (map fst ?\<Psi>)) $\<turnstile> \<Phi>"
    using \<Psi>(3) segmented_stronger_theory_left_monotonic
    by blast
  ultimately show "\<exists>\<Psi>. mset (map fst \<Psi>) \<subseteq># mset \<Gamma> \<and>
                        \<^bold>\<sim> (map (uncurry (op \<setminus>)) \<Psi>) :\<turnstile> \<phi> \<and>
                        \<^bold>\<sim> (map (uncurry (op \<sqinter>)) \<Psi> @ \<Gamma> \<ominus> (map fst \<Psi>)) $\<turnstile> \<Phi>"
    by metis
next
  assume "\<exists>\<Psi>. mset (map fst \<Psi>) \<subseteq># mset \<Gamma> \<and>
               \<^bold>\<sim> (map (uncurry op \<setminus>) \<Psi>) :\<turnstile> \<phi> \<and>
               \<^bold>\<sim> (map (uncurry op \<sqinter>) \<Psi> @ \<Gamma> \<ominus> map fst \<Psi>) $\<turnstile> \<Phi>"
  from this obtain \<Psi> where \<Psi>:
    "mset (map fst \<Psi>) \<subseteq># mset \<Gamma>"
    "\<^bold>\<sim> (map (uncurry op \<setminus>) \<Psi>) :\<turnstile> \<phi>"
    "\<^bold>\<sim> (map (uncurry op \<sqinter>) \<Psi> @ \<Gamma> \<ominus> map fst \<Psi>) $\<turnstile> \<Phi>"
    by auto
  let ?\<Psi> = "zip (map snd \<Psi>) (\<^bold>\<sim> (map fst \<Psi>))"
  from \<Psi>(1) have "mset (map snd ?\<Psi>) \<subseteq># mset (\<^bold>\<sim> \<Gamma>)"
    by (simp, metis image_mset_subseteq_mono multiset.map_comp)
  moreover have "\<^bold>\<sim> (map (uncurry op \<setminus>) \<Psi>) \<preceq> map (uncurry (op \<squnion>)) ?\<Psi>"
  proof (induct \<Psi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<psi> \<Psi>)
    let ?\<gamma> = "fst \<psi>"
    let ?\<psi> = "snd \<psi>"
    {
      fix \<psi> \<gamma>
      have "\<turnstile> (\<psi> \<squnion> \<sim> \<gamma>) \<rightarrow> \<sim>(\<gamma> \<setminus> \<psi>)"
        unfolding disjunction_def
                  subtraction_def
                  conjunction_def
                  negation_def
        by (meson Modus_Ponens 
                  flip_implication 
                  hypothetical_syllogism)
    } note tautology = this
    have "\<sim> \<circ> uncurry (op \<setminus>) = (\<lambda> \<psi>. \<sim> ((fst \<psi>) \<setminus> (snd \<psi>)))"
         "uncurry (op \<squnion>) = (\<lambda> (\<psi>,\<gamma>). \<psi> \<squnion> \<gamma>)"
      by fastforce+
    with tautology have "\<turnstile> uncurry (op \<squnion>) (?\<psi>, \<sim> ?\<gamma>) \<rightarrow> (\<sim> \<circ> uncurry (op \<setminus>)) \<psi>"
      by fastforce
    with Cons.hyps have 
      "((\<sim> \<circ> uncurry (op \<setminus>)) \<psi> # \<^bold>\<sim> (map (uncurry op \<setminus>) \<Psi>)) \<preceq> 
       (uncurry (op \<squnion>) (?\<psi>, \<sim> ?\<gamma>) # map (uncurry op \<squnion>) (zip (map snd \<Psi>) (\<^bold>\<sim> (map fst \<Psi>))))"
      using stronger_theory_left_right_cons by blast
    thus ?case by simp
  qed
  with \<Psi>(2) have "map (uncurry (op \<squnion>)) ?\<Psi> :\<turnstile> \<phi>"
    using stronger_theory_deduction_monotonic by blast
  moreover have "\<^bold>\<sim> (map (uncurry op \<sqinter>) \<Psi> @ \<Gamma> \<ominus> map fst \<Psi>) \<preceq> 
                 (map (uncurry (op \<rightarrow>)) ?\<Psi> @ \<^bold>\<sim> \<Gamma> \<ominus> map snd ?\<Psi>)"
  proof -
    have "\<^bold>\<sim> (map (uncurry op \<sqinter>) \<Psi>) \<preceq> map (uncurry (op \<rightarrow>)) ?\<Psi>"
    proof (induct \<Psi>)
      case Nil
      then show ?case by simp 
    next
      case (Cons \<psi> \<Psi>)
      let ?\<gamma> = "fst \<psi>"
      let ?\<psi> = "snd \<psi>"
      {
        fix \<psi> \<gamma>
        have "\<turnstile> (\<psi> \<rightarrow> \<sim> \<gamma>) \<rightarrow> \<sim>(\<gamma> \<sqinter> \<psi>)"
          unfolding disjunction_def
                    conjunction_def
                    negation_def
          by (meson Modus_Ponens 
                    flip_implication 
                    hypothetical_syllogism)
      } note tautology = this
      have "\<sim> \<circ> uncurry (op \<sqinter>) = (\<lambda> \<psi>. \<sim> ((fst \<psi>) \<sqinter> (snd \<psi>)))"
           "uncurry (op \<rightarrow>) = (\<lambda> (\<psi>,\<gamma>). \<psi> \<rightarrow> \<gamma>)"
        by fastforce+
      with tautology have "\<turnstile> uncurry (op \<rightarrow>) (?\<psi>, \<sim> ?\<gamma>) \<rightarrow> (\<sim> \<circ> uncurry (op \<sqinter>)) \<psi>"
        by fastforce
      with Cons.hyps have 
        "((\<sim> \<circ> uncurry (op \<sqinter>)) \<psi> # \<^bold>\<sim> (map (uncurry op \<sqinter>) \<Psi>)) \<preceq> 
         (uncurry (op \<rightarrow>) (?\<psi>, \<sim> ?\<gamma>) # map (uncurry op \<rightarrow>) (zip (map snd \<Psi>) (\<^bold>\<sim> (map fst \<Psi>))))"
        using stronger_theory_left_right_cons by blast
      then show ?case by simp
    qed
    moreover have "mset (\<^bold>\<sim> (\<Gamma> \<ominus> map fst \<Psi>)) = mset (\<^bold>\<sim> \<Gamma> \<ominus> map snd ?\<Psi>)"
      using \<Psi>(1)
      by (simp add: image_mset_Diff multiset.map_comp)
    hence "\<^bold>\<sim> (\<Gamma> \<ominus> map fst \<Psi>) \<preceq> (\<^bold>\<sim> \<Gamma> \<ominus> map snd ?\<Psi>)"
      using stronger_theory_reflexive 
            stronger_theory_right_permutation 
            mset_eq_perm 
      by blast
    ultimately show ?thesis
      using stronger_theory_combine
      by simp
  qed
  hence "map (uncurry (op \<rightarrow>)) ?\<Psi> @ \<^bold>\<sim> \<Gamma> \<ominus> map snd ?\<Psi> $\<turnstile> \<Phi>"
    using \<Psi>(3) segmented_stronger_theory_left_monotonic by blast
  ultimately show "\<^bold>\<sim> \<Gamma> $\<turnstile> (\<phi> # \<Phi>)"
    using segmented_deduction.simps(2) by blast
qed

lemma (in Weakly_Additive_Logical_Probability) Segmented_Deduction_Summation_Introduction:
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
      from this obtain \<Psi> where \<Psi>:
        "mset (map fst \<Psi>) \<subseteq># mset \<Gamma>" 
        "\<^bold>\<sim> (map (uncurry (op \<setminus>)) \<Psi>) :\<turnstile> \<sim> \<phi>"
        "\<^bold>\<sim> (map (uncurry (op \<sqinter>)) \<Psi> @ \<Gamma> \<ominus> (map fst \<Psi>)) $\<turnstile> \<^bold>\<sim> \<Phi>"
        using negated_segmented_deduction by blast
      let ?\<Gamma> = "\<Gamma> \<ominus> (map fst \<Psi>)"
      let ?\<Psi>\<^sub>1 = "map (uncurry (op \<setminus>)) \<Psi>"
      let ?\<Psi>\<^sub>2 = "map (uncurry (op \<sqinter>)) \<Psi>"
      have "(\<Sum>\<phi>'\<leftarrow>\<Phi>. Pr \<phi>') \<le> (\<Sum>\<phi>\<leftarrow>(?\<Psi>\<^sub>2 @ ?\<Gamma>). Pr \<phi>)"
        using Cons \<Psi>(3) by blast
      moreover
      {
        fix \<Phi>
        have "Pr (\<Squnion> \<Phi>) \<le> (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>)"
        by (induct \<Phi>, 
            simp, smt falsum_zero_probability, 
            simp, smt Non_Negative sum_rule sum_list.Cons)
        moreover assume "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Phi>"
        ultimately have "Pr \<phi> \<le> (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>)"
          using monotonicity by force
      }
      hence "Pr \<phi> \<le> (\<Sum>\<phi>\<leftarrow>?\<Psi>\<^sub>1. Pr \<phi>)"
        using \<Psi>(2)
              biconditional_weaken
              list_deduction_def 
              map_negation_list_implication 
              set_deduction_base_theory 
        by blast
      ultimately have "(\<Sum>\<phi>'\<leftarrow>(\<phi> # \<Phi>). Pr \<phi>') \<le> (\<Sum>\<gamma> \<leftarrow>(?\<Psi>\<^sub>1 @ ?\<Psi>\<^sub>2 @ ?\<Gamma>). Pr \<gamma>)"
        by simp
      moreover have "(\<Sum>\<phi>'\<leftarrow>(?\<Psi>\<^sub>1 @ ?\<Psi>\<^sub>2). Pr \<phi>') = (\<Sum>\<gamma>\<leftarrow>(map fst \<Psi>). Pr \<gamma>)"
      proof (induct \<Psi>)
        case Nil
        then show ?case by simp
      next
        case (Cons \<psi> \<Psi>)
        let ?\<Psi>\<^sub>1 = "map (uncurry (op \<setminus>)) \<Psi>"
        let ?\<Psi>\<^sub>2 = "map (uncurry (op \<sqinter>)) \<Psi>"
        let ?\<psi>\<^sub>1 = "uncurry (op \<setminus>) \<psi>"
        let ?\<psi>\<^sub>2 = "uncurry (op \<sqinter>) \<psi>"
        assume "(\<Sum>\<phi>'\<leftarrow>(?\<Psi>\<^sub>1 @ ?\<Psi>\<^sub>2). Pr \<phi>') = (\<Sum>\<gamma>\<leftarrow>(map fst \<Psi>). Pr \<gamma>)"
        moreover
        {
          let ?\<gamma> = "fst \<psi>"
          let ?\<psi> = "snd \<psi>"
          have "uncurry (op \<setminus>) = (\<lambda> \<psi>. (fst \<psi>) \<setminus> (snd \<psi>))"
               "uncurry (op \<sqinter>) = (\<lambda> \<psi>. (fst \<psi>) \<sqinter> (snd \<psi>))"
            by fastforce+
          moreover have "Pr ?\<gamma> = Pr (?\<gamma> \<setminus> ?\<psi>) + Pr (?\<gamma> \<sqinter> ?\<psi>)"
            by (simp add: subtraction_identity)
          ultimately have "Pr ?\<gamma> = Pr ?\<psi>\<^sub>1 + Pr ?\<psi>\<^sub>2"
            by simp
        }
        moreover have "mset (?\<psi>\<^sub>1 # ?\<psi>\<^sub>2 # (?\<Psi>\<^sub>1 @ ?\<Psi>\<^sub>2)) = 
                       mset (map (uncurry (op \<setminus>)) (\<psi> # \<Psi>) @ map (uncurry (op \<sqinter>)) (\<psi> # \<Psi>))"
          (is "mset _ = mset ?rhs")
          by simp
        hence "(\<Sum>\<phi>' \<leftarrow> (?\<psi>\<^sub>1 # ?\<psi>\<^sub>2 # (?\<Psi>\<^sub>1 @ ?\<Psi>\<^sub>2)). Pr \<phi>') = (\<Sum>\<gamma> \<leftarrow> ?rhs. Pr \<gamma>)"
          by auto 
        ultimately show ?case by simp
      qed
      moreover have "mset ((map fst \<Psi>) @ ?\<Gamma>) = mset \<Gamma>"
        using \<Psi>(1)
        by simp
      hence "(\<Sum>\<phi>'\<leftarrow>((map fst \<Psi>) @ ?\<Gamma>). Pr \<phi>') = (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
        by (metis mset_map sum_mset_sum_list)
      ultimately have "(\<Sum>\<phi>'\<leftarrow>(\<phi> # \<Phi>). Pr \<phi>') \<le>  (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
        by simp
    }
    then show ?case by blast
  qed
  thus ?thesis using assms by blast
qed

primrec (in Minimal_Logic) 
  firstComponent :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list"
  where
    "firstComponent \<Psi> [] = []"
  | "firstComponent \<Psi> (\<delta> # \<Delta>) =
       (case find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> of 
             None \<Rightarrow> firstComponent \<Psi> \<Delta> 
           | Some \<psi> \<Rightarrow> \<psi> # (firstComponent (remove1 \<psi> \<Psi>) \<Delta>))"
  
primrec (in Minimal_Logic) 
  secondComponent :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list"
  where
    "secondComponent \<Psi> [] = []"
  | "secondComponent \<Psi> (\<delta> # \<Delta>) = 
       (case find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> of 
             None \<Rightarrow> secondComponent \<Psi> \<Delta>
           | Some \<psi> \<Rightarrow> \<delta> # (secondComponent (remove1 \<psi> \<Psi>) \<Delta>))"

lemma (in Minimal_Logic) firstComponent_secondComponent_mset_connection:
  "mset (map (uncurry op \<rightarrow>) (firstComponent \<Psi> \<Delta>)) = mset (map snd (secondComponent \<Psi> \<Delta>))"
proof - 
  have "\<forall> \<Psi>. mset (map (uncurry op \<rightarrow>) (firstComponent \<Psi> \<Delta>))
           = mset (map snd (secondComponent \<Psi> \<Delta>))"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "mset (map (uncurry op \<rightarrow>) (firstComponent \<Psi> (\<delta> # \<Delta>))) =
            mset (map snd (secondComponent \<Psi> (\<delta> # \<Delta>)))"
      proof (cases "find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        then show ?thesis using Cons by simp
      next
        case False
        from this obtain \<psi> where
          "find (\<lambda>\<psi>. uncurry op \<rightarrow> \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
          "uncurry op \<rightarrow> \<psi> = snd \<delta>"
          using find_Some_predicate
          by fastforce
        then show ?thesis using Cons by simp
      qed
    }
    then show ?case by blast
  qed
  thus ?thesis by blast
qed
    
lemma (in Minimal_Logic) secondComponent_right_empty [simp]:
  "secondComponent [] \<Delta> = []" 
  by (induct \<Delta>, simp+)    

lemma (in Minimal_Logic) firstComponent_msub:
  "mset (firstComponent \<Psi> \<Delta>) \<subseteq># mset \<Psi>"
proof -
  have "\<forall> \<Psi>. mset (firstComponent \<Psi> \<Delta>) \<subseteq># mset \<Psi>"
  proof(induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "mset (firstComponent \<Psi> (\<delta> # \<Delta>)) \<subseteq># mset \<Psi>"
      proof (cases "find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        then show ?thesis using Cons by simp
      next
        case False
        from this obtain \<psi> where 
          \<psi>: "find (\<lambda>\<psi>. uncurry op \<rightarrow> \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
             "\<psi> \<in> set \<Psi>"
          using find_Some_set_membership
          by fastforce
        have "mset (firstComponent (remove1 \<psi> \<Psi>) \<Delta>) \<subseteq># mset (remove1 \<psi> \<Psi>)"
          using Cons by smt
        thus ?thesis using \<psi> by (simp add: insert_subset_eq_iff)
      qed
    }
    then show ?case by blast
  qed
  thus ?thesis by blast
qed    
    
lemma (in Minimal_Logic) secondComponent_msub:
  "mset (secondComponent \<Psi> \<Delta>) \<subseteq># mset \<Delta>"
proof -
  have "\<forall>\<Psi>. mset (secondComponent \<Psi> \<Delta>) \<subseteq># mset \<Delta>"  
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "mset (secondComponent \<Psi> (\<delta> # \<Delta>)) \<subseteq># mset (\<delta> # \<Delta>)"
      using Cons
      by (cases "find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> = None", 
           simp, 
           metis add_mset_remove_trivial 
                 diff_subset_eq_self 
                 subset_mset.order_trans,
           auto)
    }
    thus ?case by blast
  qed
  thus ?thesis by blast
qed

lemma (in Minimal_Logic) secondComponent_snd_projection_msub:
  "mset (map snd (secondComponent \<Psi> \<Delta>)) \<subseteq># mset (map (uncurry op \<rightarrow>) \<Psi>)"
proof -
  have "\<forall>\<Psi>. mset (map snd (secondComponent \<Psi> \<Delta>)) \<subseteq># mset (map (uncurry op \<rightarrow>) \<Psi>)"  
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "mset (map snd (secondComponent \<Psi> (\<delta> # \<Delta>))) \<subseteq># mset (map (uncurry op \<rightarrow>) \<Psi>)"
      proof (cases "find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        then show ?thesis
          using Cons by simp
      next
        case False
        from this obtain \<psi> where \<psi>: 
          "find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> = Some \<psi>" 
          by auto
        hence "secondComponent \<Psi> (\<delta> # \<Delta>) = \<delta> # (secondComponent (remove1 \<psi> \<Psi>) \<Delta>)"
          using \<psi> by fastforce
        with Cons have "mset (map snd (secondComponent \<Psi> (\<delta> # \<Delta>))) \<subseteq>#
                        mset ((snd \<delta>) # map (uncurry op \<rightarrow>) (remove1 \<psi> \<Psi>))"
          by (simp, metis mset_map mset_remove1)
        moreover from \<psi> have "snd \<delta> = (uncurry op \<rightarrow>) \<psi>"
          using find_Some_predicate by fastforce
        ultimately have "mset (map snd (secondComponent \<Psi> (\<delta> # \<Delta>))) \<subseteq>#
                         mset (map (uncurry op \<rightarrow>) (\<psi> # (remove1 \<psi> \<Psi>)))"
          by simp
        thus ?thesis
          by (metis \<psi> find_Some_set_membership mset_eq_perm mset_map perm_remove)          
      qed
    }
    thus ?case by blast
  qed
  thus ?thesis by blast
qed

lemma (in Minimal_Logic) secondComponent_diff_msub:
  assumes "mset (map snd \<Delta>) \<subseteq># mset (map (uncurry op \<rightarrow>) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>))"
  shows "mset (map snd (\<Delta> \<ominus> (secondComponent \<Psi> \<Delta>))) \<subseteq># mset (\<Gamma> \<ominus> (map snd \<Psi>))"
proof -
  have "\<forall> \<Psi> \<Gamma>. mset (map snd \<Delta>) \<subseteq># mset (map (uncurry op \<rightarrow>) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>)) \<longrightarrow> 
               mset (map snd (\<Delta> \<ominus> (secondComponent \<Psi> \<Delta>))) \<subseteq># mset (\<Gamma> \<ominus> (map snd \<Psi>))"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi> \<Gamma>
      assume \<diamondsuit>: "mset (map snd (\<delta> # \<Delta>)) \<subseteq># mset (map (uncurry op \<rightarrow>) \<Psi> @ \<Gamma> \<ominus> map snd \<Psi>)"
      have "mset (map snd ((\<delta> # \<Delta>) \<ominus> secondComponent \<Psi> (\<delta> # \<Delta>))) \<subseteq># mset (\<Gamma> \<ominus> map snd \<Psi>)"
      proof (cases "find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        hence "snd \<delta> \<notin> set (map (uncurry op \<rightarrow>) \<Psi>)"
        proof (induct \<Psi>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<psi> \<Psi>)
          then show ?case
            by (cases "uncurry op \<rightarrow> \<psi> = snd \<delta>", simp+)
        qed
        with \<diamondsuit> have "mset (map snd \<Delta>) \<subseteq># 
                     mset (map (uncurry op \<rightarrow>) \<Psi> @ (remove1 (snd \<delta>) \<Gamma>) \<ominus> map snd \<Psi>)"
          by (smt insert_subset_eq_iff 
                  list.map(2) 
                  listSubtract.simps(2) 
                  listSubtract_remove1_cons_perm 
                  mset.simps(2) 
                  mset_eq_perm mset_remove1 
                  remove1_append 
                  union_code)
        hence "mset (map snd (\<Delta> \<ominus> (secondComponent \<Psi> \<Delta>))) \<subseteq># 
               mset ((remove1 (snd \<delta>) \<Gamma>) \<ominus> (map snd \<Psi>))"
          using Cons by blast
        moreover have "snd \<delta> \<in> set \<Gamma>"  
          by (smt \<diamondsuit>
                  \<open>snd \<delta> \<notin> set (map (uncurry op \<rightarrow>) \<Psi>)\<close>
                  append.simps(2) 
                  diff_subset_eq_self 
                  in_multiset_in_set 
                  list.map(2) 
                  list.set_intros(1) 
                  listSubtract_mset_homomorphism 
                  subset_mset.add_diff_inverse 
                  union_code 
                  union_iff) 
        moreover have "secondComponent \<Psi> \<Delta> = secondComponent \<Psi> (\<delta> # \<Delta>)"
          using \<open>find (\<lambda>\<psi>. uncurry op \<rightarrow> \<psi> = snd \<delta>) \<Psi> = None\<close>
          by simp
        ultimately show ?thesis
          by (smt \<diamondsuit> 
                  \<open>snd \<delta> \<notin> set (map (uncurry op \<rightarrow>) \<Psi>)\<close> 
                  in_multiset_in_set 
                  insert_subset_eq_iff 
                  list.map(2) 
                  listSubtract.simps(2) 
                  listSubtract_cons 
                  listSubtract_remove1_cons_perm 
                  secondComponent_msub 
                  secondComponent_snd_projection_msub 
                  map_listSubtract_mset_equivalence 
                  mset.simps(2) 
                  mset_eq_perm 
                  mset_le_perm_append 
                  mset_remove1 
                  union_code 
                  union_iff)
      next
        case False
        from this obtain \<psi> where \<psi>: "find (\<lambda>\<psi>. uncurry op \<rightarrow> \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
          by auto
        let ?\<Psi>' = "remove1 \<psi> \<Psi>"
        let ?\<Gamma>' = "remove1 (snd \<psi>) \<Gamma>"
        have "snd \<delta> = uncurry op \<rightarrow> \<psi>" 
             "\<psi> \<in> set \<Psi>"
             "mset ((\<delta> # \<Delta>) \<ominus> secondComponent \<Psi> (\<delta> # \<Delta>)) = 
              mset (\<Delta> \<ominus> secondComponent ?\<Psi>' \<Delta>)"
          using \<psi> find_Some_predicate find_Some_set_membership 
          by fastforce+
        moreover 
        have "mset (\<Gamma> \<ominus> map snd \<Psi>) = mset (?\<Gamma>' \<ominus> map snd ?\<Psi>')"
          by (simp, metis \<open>\<psi> \<in> set \<Psi>\<close> image_mset_add_mset in_multiset_in_set insert_DiffM)  
        moreover have "snd \<delta> \<in> set (map (uncurry op \<rightarrow>) \<Psi>)"
          by (smt \<open>find (\<lambda>\<psi>. uncurry op \<rightarrow> \<psi> = snd \<delta>) \<Psi> \<noteq> None\<close> 
                  find_None_iff 
                  image_eqI 
                  image_set)
        ultimately show ?thesis
          by (smt Cons
                  \<diamondsuit>
                  add_mset_remove_trivial 
                  image_mset_add_mset 
                  in_multiset_in_set 
                  insert_DiffM 
                  insert_subset_eq_iff 
                  mset.simps(2) 
                  mset_map
                  mset_remove1 
                  remove1_append 
                  union_code)
      qed
    }
    then show ?case by blast
  qed
  thus ?thesis using assms by auto
qed
  
primrec (in Classical_Propositional_Logic) 
  mergeWitness :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list"
  where
    "mergeWitness \<Psi> [] = \<Psi>"
  | "mergeWitness \<Psi> (\<delta> # \<Delta>) = 
       (case find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> of 
             None \<Rightarrow> \<delta> # mergeWitness \<Psi> \<Delta>
           | Some \<psi> \<Rightarrow> (fst \<delta> \<sqinter> fst \<psi>, snd \<psi>) # (mergeWitness (remove1 \<psi> \<Psi>) \<Delta>))"
    
lemma (in Classical_Propositional_Logic) mergeWitness_right_empty [simp]:
  "mergeWitness [] \<Delta> = \<Delta>" 
  by (induct \<Delta>, simp+)

lemma (in Classical_Propositional_Logic) secondComponent_mergeWitness_snd_projection:
  "mset (map snd \<Psi> @ map snd (\<Delta> \<ominus> (secondComponent \<Psi> \<Delta>))) =
   mset (map snd (mergeWitness \<Psi> \<Delta>))"
proof -
  have "\<forall> \<Psi>. mset (map snd \<Psi> @ map snd (\<Delta> \<ominus> (secondComponent \<Psi> \<Delta>))) =
             mset (map snd (mergeWitness \<Psi> \<Delta>))"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "mset (map snd \<Psi> @ map snd ((\<delta> # \<Delta>) \<ominus> secondComponent \<Psi> (\<delta> # \<Delta>))) = 
            mset (map snd (mergeWitness \<Psi> (\<delta> # \<Delta>)))"
      proof (cases "find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        then show ?thesis 
          using Cons
          by (simp, 
              metis (no_types, lifting) 
                    ab_semigroup_add_class.add_ac(1) 
                    add_mset_add_single 
                    image_mset_single 
                    image_mset_union 
                    secondComponent_msub 
                    subset_mset.add_diff_assoc2)
      next
        case False
        from this obtain \<psi> where \<psi>: "find (\<lambda>\<psi>. uncurry op \<rightarrow> \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
          by auto
        moreover have "\<psi> \<in> set \<Psi>"
          by (meson \<psi> find_Some_set_membership)  
        moreover
        let ?\<Psi>' = "remove1 \<psi> \<Psi>"
        from Cons have
          "mset (map snd ?\<Psi>' @ map snd (\<Delta> \<ominus> secondComponent ?\<Psi>' \<Delta>)) = 
            mset (map snd (mergeWitness ?\<Psi>' \<Delta>))"
          by blast
        ultimately show ?thesis
          by (simp, 
              metis (no_types, lifting) 
                    add_mset_remove_trivial_eq 
                    image_mset_add_mset 
                    in_multiset_in_set 
                    union_mset_add_mset_left) 
      qed
    }
    then show ?case by blast
  qed
  thus ?thesis by blast
qed

lemma (in Classical_Propositional_Logic) secondComponent_mergeWitness_stronger_theory:
  "(map (uncurry op \<rightarrow>) \<Delta> @ map (uncurry op \<rightarrow>) \<Psi> \<ominus> map snd (secondComponent \<Psi> \<Delta>)) \<preceq> 
    map (uncurry op \<rightarrow>) (mergeWitness \<Psi> \<Delta>)"
proof -
  have "\<forall> \<Psi>. (map (uncurry op \<rightarrow>) \<Delta> @ 
              map (uncurry op \<rightarrow>) \<Psi> \<ominus> map snd (secondComponent \<Psi> \<Delta>)) \<preceq>
              map (uncurry op \<rightarrow>) (mergeWitness \<Psi> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case 
      by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "\<turnstile> (uncurry op \<rightarrow>) \<delta> \<rightarrow> (uncurry op \<rightarrow>) \<delta>"
        using Axiom_1 Modus_Ponens implication_absorption by blast
      have 
        "(map (uncurry op \<rightarrow>) (\<delta> # \<Delta>) @
          map (uncurry op \<rightarrow>) \<Psi> \<ominus> map snd (secondComponent \<Psi> (\<delta> # \<Delta>))) \<preceq>
          map (uncurry op \<rightarrow>) (mergeWitness \<Psi> (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        thus ?thesis
          using Cons
                \<open>\<turnstile> (uncurry op \<rightarrow>) \<delta> \<rightarrow> (uncurry op \<rightarrow>) \<delta>\<close>
          by (simp, smt stronger_theory_left_right_cons)
      next
        case False
        from this obtain \<psi> where \<psi>: "find (\<lambda>\<psi>. uncurry op \<rightarrow> \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
          by auto
        from \<psi> have "snd \<delta> = uncurry op \<rightarrow> \<psi>"
          using find_Some_predicate by fastforce
        from \<psi> \<open>snd \<delta> = uncurry op \<rightarrow> \<psi>\<close> have 
          "mset (map (uncurry op \<rightarrow>) (\<delta> # \<Delta>) @
                   map (uncurry op \<rightarrow>) \<Psi> \<ominus> map snd (secondComponent \<Psi> (\<delta> # \<Delta>))) = 
           mset (map (uncurry op \<rightarrow>) (\<delta> # \<Delta>) @
                   map (uncurry op \<rightarrow>) (remove1 \<psi> \<Psi>) \<ominus> 
                   map snd (secondComponent (remove1 \<psi> \<Psi>) \<Delta>))"
          by (simp add: find_Some_set_membership image_mset_Diff) 
        hence 
          "(map (uncurry op \<rightarrow>) (\<delta> # \<Delta>) @
              map (uncurry op \<rightarrow>) \<Psi> \<ominus> map snd (secondComponent \<Psi> (\<delta> # \<Delta>))) \<preceq>
           (map (uncurry op \<rightarrow>) (\<delta> # \<Delta>) @
              map (uncurry op \<rightarrow>) (remove1 \<psi> \<Psi>) \<ominus> map snd (secondComponent (remove1 \<psi> \<Psi>) \<Delta>))"
          by (simp add: msub_stronger_theory_intro)
        with Cons \<open>\<turnstile> (uncurry op \<rightarrow>) \<delta> \<rightarrow> (uncurry op \<rightarrow>) \<delta>\<close> have
          "(map (uncurry op \<rightarrow>) (\<delta> # \<Delta>) @ 
            map (uncurry op \<rightarrow>) \<Psi> \<ominus> map snd (secondComponent \<Psi> (\<delta> # \<Delta>)))
            \<preceq> ((uncurry op \<rightarrow>) \<delta> # map (uncurry op \<rightarrow>) (mergeWitness (remove1 \<psi> \<Psi>) \<Delta>))"
          apply simp
          using stronger_theory_left_right_cons 
                stronger_theory_transitive
          by blast
        moreover
        let ?\<alpha> = "fst \<delta>"
        let ?\<beta> = "fst \<psi>"
        let ?\<gamma> = "snd \<psi>"
        have "uncurry op \<rightarrow> = (\<lambda> \<delta>. fst \<delta> \<rightarrow> snd \<delta>)" by fastforce
        with \<psi> have "(uncurry op \<rightarrow>) \<delta> = ?\<alpha> \<rightarrow> ?\<beta> \<rightarrow> ?\<gamma>"
          using find_Some_predicate by fastforce
        hence "\<turnstile> ((?\<alpha> \<sqinter> ?\<beta>) \<rightarrow> ?\<gamma>) \<rightarrow> (uncurry op \<rightarrow>) \<delta>"
          using biconditional_def curry_uncurry by auto
        with \<psi> have
          "((uncurry op \<rightarrow>) \<delta> # map (uncurry op \<rightarrow>) (mergeWitness (remove1 \<psi> \<Psi>) \<Delta>)) \<preceq>
           map (uncurry op \<rightarrow>) (mergeWitness \<Psi> (\<delta> # \<Delta>))"
          using stronger_theory_left_right_cons by auto
        ultimately show ?thesis
          using stronger_theory_transitive
          by blast
      qed
    }
    then show ?case by simp
  qed
  thus ?thesis by simp
qed
    
lemma (in Classical_Propositional_Logic) mergeWitness_msub_intro:
  assumes "mset (map snd \<Psi>) \<subseteq># mset \<Gamma>"
      and "mset (map snd \<Delta>) \<subseteq># mset (map (uncurry (op \<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>))"
    shows "mset (map snd (mergeWitness \<Psi> \<Delta>)) \<subseteq># mset \<Gamma>"
proof -
  have "\<forall>\<Psi> \<Gamma>. mset (map snd \<Psi>) \<subseteq># mset \<Gamma> \<longrightarrow>
               mset (map snd \<Delta>) \<subseteq># mset (map (uncurry (op \<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>)) \<longrightarrow> 
               mset (map snd (mergeWitness \<Psi> \<Delta>)) \<subseteq># mset \<Gamma>"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi> :: "('a \<times> 'a) list"
      fix \<Gamma> :: "'a list"
      assume \<diamondsuit>: "mset (map snd \<Psi>) \<subseteq># mset \<Gamma>"
                "mset (map snd (\<delta> # \<Delta>)) \<subseteq># mset (map (uncurry (op \<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>))"
      have "mset (map snd (mergeWitness \<Psi> (\<delta> # \<Delta>))) \<subseteq># mset \<Gamma>"
      proof (cases "find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        hence "snd \<delta> \<notin> set (map (uncurry (op \<rightarrow>)) \<Psi>)"
        proof (induct \<Psi>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<psi> \<Psi>)
          hence "uncurry op \<rightarrow> \<psi> \<noteq> snd \<delta>" by fastforce
          with Cons show ?case by fastforce
        qed
        with \<diamondsuit>(2) have "snd \<delta> \<in># mset (\<Gamma> \<ominus> map snd \<Psi>)"
          using mset_subset_eq_insertD by fastforce
        with \<diamondsuit>(1) have "mset (map snd \<Psi>) \<subseteq># mset (remove1 (snd \<delta>) \<Gamma>)"
          by (metis listSubtract_mset_homomorphism 
                    mset_remove1 
                    single_subset_iff 
                    subset_mset.add_diff_assoc 
                    subset_mset.add_diff_inverse 
                    subset_mset.le_iff_add)
        moreover from \<diamondsuit>(2) have
          "mset (map snd \<Delta>) \<subseteq># 
           mset (map (uncurry (op \<rightarrow>)) \<Psi> @ (remove1 (snd \<delta>) \<Gamma>) \<ominus> (map snd \<Psi>))"
          by (simp,
              smt \<open>snd \<delta> \<in># mset (\<Gamma> \<ominus> map snd \<Psi>)\<close> 
                  add_mset_add_single 
                  diff_diff_add_mset 
                  insert_subset_eq_iff 
                  listSubtract_mset_homomorphism 
                  mset_map 
                  mset_subset_eq_single 
                  subset_mset.add_diff_assoc)
        ultimately have "mset (map snd (mergeWitness \<Psi> \<Delta>)) \<subseteq># mset (remove1 (snd \<delta>) \<Gamma>)"
          using Cons by blast
        hence "mset (map snd (\<delta> # (mergeWitness \<Psi> \<Delta>))) \<subseteq># mset \<Gamma>"
          by (simp, metis \<open>snd \<delta> \<in># mset (\<Gamma> \<ominus> map snd \<Psi>)\<close> 
                          cancel_ab_semigroup_add_class.diff_right_commute 
                          diff_single_trivial 
                          insert_subset_eq_iff 
                          listSubtract_mset_homomorphism 
                          multi_drop_mem_not_eq)
        with \<open>find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> = None\<close> 
        show ?thesis
          by simp
      next
        case False
        from this obtain \<psi> where \<psi>:
          "find (\<lambda>\<psi>. uncurry op \<rightarrow> \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
          by fastforce
        let ?\<chi> = "fst \<psi>"
        let ?\<gamma> = "snd \<psi>"
        have "uncurry op \<rightarrow> = (\<lambda> \<psi>. fst \<psi> \<rightarrow> snd \<psi>)"
          by fastforce
        hence "uncurry op \<rightarrow> \<psi> = ?\<chi> \<rightarrow> ?\<gamma>" by fastforce
        with \<psi> have A: "(?\<chi>, ?\<gamma>) \<in> set \<Psi>"
                and B: "snd \<delta> = ?\<chi> \<rightarrow> ?\<gamma>"
          by (simp add: find_Some_set_membership,
              smt find_Some_predicate)
        let ?\<Psi>' = "remove1 (?\<chi>, ?\<gamma>) \<Psi>"
        from B \<diamondsuit>(2) have 
          "mset (map snd \<Delta>) \<subseteq># mset (map (uncurry op \<rightarrow>) \<Psi> @ \<Gamma> \<ominus> map snd \<Psi>) - {# ?\<chi> \<rightarrow> ?\<gamma> #}"
          by (simp add: insert_subset_eq_iff)
        moreover from A have 
          "mset (map (uncurry op \<rightarrow>) \<Psi>) - {# ?\<chi> \<rightarrow> ?\<gamma> #} = mset (map (uncurry op \<rightarrow>) ?\<Psi>')"
          by (smt add_mset_remove_trivial 
                  image_mset_add_mset 
                  in_multiset_in_set 
                  insert_DiffM 
                  mset_map 
                  mset_remove1 
                  split_conv 
                  uncurry_def)
        ultimately have 
          "mset (map snd \<Delta>) \<subseteq># mset (map (uncurry op \<rightarrow>) ?\<Psi>' @ \<Gamma> \<ominus> map snd \<Psi>)"
          by (smt add_diff_cancel_left' 
                  add_diff_cancel_right 
                  diff_diff_add_mset 
                  diff_subset_eq_self 
                  mset_append 
                  subset_eq_diff_conv 
                  subset_mset.diff_add)
        moreover from A B \<diamondsuit> 
        have "mset (\<Gamma> \<ominus> map snd \<Psi>) = mset((remove1 ?\<gamma> \<Gamma>) \<ominus> (remove1 ?\<gamma> (map snd \<Psi>)))"
          by (metis image_eqI 
                    listSubtract_remove1_perm 
                    mset_eq_perm 
                    prod.sel(2) 
                    set_map)
        with A have "mset (\<Gamma> \<ominus> map snd \<Psi>) = mset((remove1 ?\<gamma> \<Gamma>) \<ominus> (map snd ?\<Psi>'))"
          by (metis remove1_pairs_list_projections_snd
                    in_multiset_in_set 
                    listSubtract_mset_homomorphism 
                    mset_remove1) 
        ultimately have "mset (map snd \<Delta>) \<subseteq># 
                         mset (map (uncurry op \<rightarrow>) ?\<Psi>' @ (remove1 ?\<gamma> \<Gamma>) \<ominus> map snd ?\<Psi>')"
          by simp
        hence "mset (map snd (mergeWitness ?\<Psi>' \<Delta>)) \<subseteq># mset (remove1 ?\<gamma> \<Gamma>)"
          using Cons \<diamondsuit>(1) A
          by (smt image_mset_add_mset 
                  in_multiset_in_set
                  insert_DiffM 
                  insert_subset_eq_iff 
                  mset_map 
                  mset_remove1 
                  prod.sel(2))
        with \<diamondsuit>(1) A have "mset (map snd (mergeWitness ?\<Psi>' \<Delta>)) + {# ?\<gamma> #} \<subseteq># mset \<Gamma>"
          by (metis add_mset_add_single 
                    image_eqI 
                    insert_subset_eq_iff 
                    mset_remove1 
                    mset_subset_eqD 
                    set_map 
                    set_mset_mset 
                    snd_conv)
        hence "mset (map snd ((fst \<delta> \<sqinter> ?\<chi>, ?\<gamma>) # (mergeWitness ?\<Psi>' \<Delta>))) \<subseteq># mset \<Gamma>"
          by simp
        moreover from \<psi> have 
          "mergeWitness \<Psi> (\<delta> # \<Delta>) = (fst \<delta> \<sqinter> ?\<chi>, ?\<gamma>) # (mergeWitness ?\<Psi>' \<Delta>)"
          by simp
        ultimately show ?thesis by simp
      qed
    }
    thus ?case by blast
  qed
  with assms show ?thesis by blast
qed

lemma (in Classical_Propositional_Logic) right_mergeWitness_stronger_theory:
  "map (uncurry op \<squnion>) \<Delta> \<preceq> map (uncurry (op \<squnion>)) (mergeWitness \<Psi> \<Delta>)"
proof -
  have "\<forall> \<Psi>. map (uncurry op \<squnion>) \<Delta> \<preceq> map (uncurry (op \<squnion>)) (mergeWitness \<Psi> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "map (uncurry op \<squnion>) (\<delta> # \<Delta>) \<preceq> map (uncurry op \<squnion>) (mergeWitness \<Psi> (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        hence "mergeWitness \<Psi> (\<delta> # \<Delta>) = \<delta> # mergeWitness \<Psi> \<Delta>"
          by simp
        moreover have "\<turnstile> (uncurry op \<squnion>) \<delta> \<rightarrow> (uncurry op \<squnion>) \<delta>"
          by (metis Axiom_1 Axiom_2 Modus_Ponens)
        ultimately show ?thesis using Cons
          by (simp add: stronger_theory_left_right_cons)
      next
        case False
        from this obtain \<psi> where \<psi>:
          "find (\<lambda>\<psi>. uncurry op \<rightarrow> \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
          by fastforce
        let ?\<chi> = "fst \<psi>"
        let ?\<gamma> = "snd \<psi>"
        let ?\<mu> = "fst \<delta>"
        have "uncurry op \<rightarrow> = (\<lambda> \<psi>. fst \<psi> \<rightarrow> snd \<psi>)"
             "uncurry op \<squnion> = (\<lambda> \<delta>. fst \<delta> \<squnion> snd \<delta>)"
          by fastforce+
        hence "uncurry op \<squnion> \<delta> = ?\<mu> \<squnion> (?\<chi> \<rightarrow> ?\<gamma>)"
          using \<psi> find_Some_predicate
          by fastforce
        moreover
        {
          fix \<mu> \<chi> \<gamma>
          have "\<turnstile> ((\<mu> \<sqinter> \<chi>) \<squnion> \<gamma>) \<rightarrow> (\<mu> \<squnion> (\<chi> \<rightarrow> \<gamma>))"
          proof -
            have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ((\<^bold>\<langle>\<mu>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<mu>\<^bold>\<rangle> \<squnion> (\<^bold>\<langle>\<chi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>))"
              by fastforce
            hence "\<turnstile> \<^bold>\<lparr> ((\<^bold>\<langle>\<mu>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<mu>\<^bold>\<rangle> \<squnion> (\<^bold>\<langle>\<chi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>)) \<^bold>\<rparr>"
              using propositional_semantics by blast
            thus ?thesis
              by simp
         qed
        }
        ultimately show ?thesis 
          using Cons \<psi> stronger_theory_left_right_cons
          by simp
      qed
    }
    thus ?case by blast
  qed
  thus ?thesis by blast
qed  
  
lemma (in Classical_Propositional_Logic) left_mergeWitness_stronger_theory:
  "map (uncurry op \<squnion>) \<Psi> \<preceq> map (uncurry (op \<squnion>)) (mergeWitness \<Psi> \<Delta>)"
proof -
  have "\<forall> \<Psi>. map (uncurry op \<squnion>) \<Psi> \<preceq> map (uncurry (op \<squnion>)) (mergeWitness \<Psi> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case
      by simp 
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "map (uncurry op \<squnion>) \<Psi> \<preceq> map (uncurry (op \<squnion>)) (mergeWitness \<Psi> (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        then show ?thesis 
          using Cons stronger_theory_right_cons 
          by auto 
      next
        case False
        from this obtain \<psi> where \<psi>:
          "find (\<lambda>\<psi>. uncurry op \<rightarrow> \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
          by fastforce
        let ?\<chi> = "fst \<psi>"
        let ?\<gamma> = "snd \<psi>"
        let ?\<mu> = "fst \<delta>"
        have "uncurry op \<rightarrow> = (\<lambda> \<psi>. fst \<psi> \<rightarrow> snd \<psi>)"
             "uncurry op \<squnion> = (\<lambda> \<delta>. fst \<delta> \<squnion> snd \<delta>)"
          by fastforce+
        hence 
          "uncurry op \<squnion> \<delta> = ?\<mu> \<squnion> (?\<chi> \<rightarrow> ?\<gamma>)"
          "uncurry op \<squnion> \<psi> = ?\<chi> \<squnion> ?\<gamma>"
          using \<psi> find_Some_predicate
          by fastforce+
        moreover
        {
          fix \<mu> \<chi> \<gamma>
          have "\<turnstile> ((\<mu> \<sqinter> \<chi>) \<squnion> \<gamma>) \<rightarrow> (\<chi> \<squnion> \<gamma>)"
          proof -
            have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ((\<^bold>\<langle>\<mu>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<chi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>)"
              by fastforce
            hence "\<turnstile> \<^bold>\<lparr> ((\<^bold>\<langle>\<mu>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<chi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<^bold>\<rparr>"
              using propositional_semantics by blast
            thus ?thesis
              by simp
         qed
       }
       ultimately have 
         "map (uncurry op \<squnion>) (\<psi> # (remove1 \<psi> \<Psi>)) \<preceq> 
          map (uncurry op \<squnion>) (mergeWitness \<Psi> (\<delta> # \<Delta>))"
         using Cons \<psi> stronger_theory_left_right_cons
         by simp
       moreover from \<psi> have "\<psi> \<in> set \<Psi>"
         by (simp add: find_Some_set_membership) 
       hence "mset (map (uncurry op \<squnion>) (\<psi> # (remove1 \<psi> \<Psi>))) =
              mset (map (uncurry op \<squnion>) \<Psi>)"
         by (metis insert_DiffM 
                   mset.simps(2) 
                   mset_map 
                   mset_remove1 
                   set_mset_mset)  
       hence "map (uncurry op \<squnion>) \<Psi> \<preceq> map (uncurry op \<squnion>) (\<psi> # (remove1 \<psi> \<Psi>))"
         by (simp add: msub_stronger_theory_intro)
       ultimately show ?thesis
         using stronger_theory_transitive by blast 
      qed
    }
    then show ?case by blast
  qed
  thus ?thesis by blast
qed

lemma (in Classical_Propositional_Logic) mergeWitness_segmented_deduction_intro:
  assumes "mset (map snd \<Delta>) \<subseteq># mset (map (uncurry op \<rightarrow>) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>))"
      and "map (uncurry op \<rightarrow>) \<Delta> @ (map (uncurry op \<rightarrow>) \<Psi> @ \<Gamma> \<ominus> map snd \<Psi>) \<ominus> map snd \<Delta> $\<turnstile> \<Phi>"
          (is "?\<Gamma>\<^sub>0 $\<turnstile> \<Phi>")
    shows "map (uncurry op \<rightarrow>) (mergeWitness \<Psi> \<Delta>) @ \<Gamma> \<ominus> map snd (mergeWitness \<Psi> \<Delta>) $\<turnstile> \<Phi>"
          (is "?\<Gamma> $\<turnstile> \<Phi>")
proof -
  let ?\<Sigma> = "secondComponent \<Psi> \<Delta>"
  let ?A = "map (uncurry op \<rightarrow>) \<Delta>"
  let ?B = "map (uncurry op \<rightarrow>) \<Psi>"
  let ?C = "map snd ?\<Sigma>"
  let ?D = "\<Gamma> \<ominus> (map snd \<Psi>)"
  let ?E = "map snd (\<Delta> \<ominus> ?\<Sigma>)"
  have \<Sigma>: "mset ?\<Sigma> \<subseteq># mset \<Delta>"
          "mset ?C \<subseteq># mset ?B"
          "mset ?E \<subseteq># mset ?D"
    using assms(1)
          secondComponent_msub
          secondComponent_snd_projection_msub
          secondComponent_diff_msub
    by simp+
  moreover from calculation have "mset ?\<Gamma>\<^sub>0 = mset (?A @ (?B \<ominus> ?C) @ (?D \<ominus> ?E))"
    by (simp, 
        smt add.commute 
            diff_diff_add 
            diff_subset_eq_self 
            image_mset_Diff 
            image_mset_union 
            listSubtract_mset_homomorphism 
            mset_map 
            mset_subset_eq_multiset_union_diff_commute 
            subset_mset.diff_add 
            subset_mset.order_trans 
            uncurry_def 
            union_code)
  moreover have "(?A @ (?B \<ominus> ?C)) \<preceq> map (uncurry op \<rightarrow>) (mergeWitness \<Psi> \<Delta>)"
    using secondComponent_mergeWitness_stronger_theory by simp
  moreover have "mset (?D \<ominus> ?E) = mset (\<Gamma> \<ominus> map snd (mergeWitness \<Psi> \<Delta>))"
    using secondComponent_mergeWitness_snd_projection
    by simp
  with calculation have "(?A @ (?B \<ominus> ?C) @ (?D \<ominus> ?E)) \<preceq> ?\<Gamma>"
    by (metis (no_types, lifting)
              stronger_theory_combine 
              append.assoc
              listSubtract_mset_homomorphism 
              msub_stronger_theory_intro 
              map_listSubtract_mset_containment 
              map_listSubtract_mset_equivalence 
              mset_subset_eq_add_right 
              subset_mset.add_diff_inverse 
              subset_mset.diff_add_assoc2)
  ultimately have "?\<Gamma>\<^sub>0 \<preceq> ?\<Gamma>"
    unfolding stronger_theory_relation_alt_def
    by simp
  thus ?thesis 
    using assms(2) segmented_stronger_theory_left_monotonic 
    by blast
qed

lemma (in Classical_Propositional_Logic) segmented_formula_right_split:
  "\<Gamma> $\<turnstile> (\<phi> # \<Phi>) = \<Gamma> $\<turnstile> (\<psi> \<squnion> \<phi> # \<psi> \<rightarrow> \<phi> # \<Phi>)"
proof (rule iffI)
  assume "\<Gamma> $\<turnstile> (\<phi> # \<Phi>)"
  from this obtain \<Psi> where \<Psi>:
    "mset (map snd \<Psi>) \<subseteq># mset \<Gamma>"
    "map (uncurry (op \<squnion>)) \<Psi> :\<turnstile> \<phi>"
    "(map (uncurry (op \<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>)) $\<turnstile> \<Phi>"
    by auto
  let ?\<Psi>\<^sub>1 = "zip (map (\<lambda> (\<chi>,\<gamma>). \<psi> \<squnion> \<chi>) \<Psi>) (map snd \<Psi>)"
  let ?\<Gamma>\<^sub>1 = "map (uncurry (op \<rightarrow>)) ?\<Psi>\<^sub>1 @ \<Gamma> \<ominus> (map snd ?\<Psi>\<^sub>1)"
  let ?\<Psi>\<^sub>2 = "zip (map (\<lambda> (\<chi>,\<gamma>). \<psi> \<rightarrow> \<chi>) \<Psi>) (map (uncurry (op \<rightarrow>)) ?\<Psi>\<^sub>1)"
  let ?\<Gamma>\<^sub>2 = "map (uncurry (op \<rightarrow>)) ?\<Psi>\<^sub>2 @ ?\<Gamma>\<^sub>1 \<ominus> (map snd ?\<Psi>\<^sub>2)"
  have "map (uncurry (op \<rightarrow>)) \<Psi> \<preceq> map (uncurry (op \<rightarrow>)) ?\<Psi>\<^sub>2"
  proof (induct \<Psi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Psi>)
    let ?\<chi> = "fst \<delta>"
    let ?\<gamma> = "snd \<delta>"
    let ?\<Psi>\<^sub>1 = "zip (map (\<lambda> (\<chi>,\<gamma>). \<psi> \<squnion> \<chi>) \<Psi>) (map snd \<Psi>)"
    let ?\<Psi>\<^sub>2 = "zip (map (\<lambda> (\<chi>,\<gamma>). \<psi> \<rightarrow> \<chi>) \<Psi>) (map (uncurry (op \<rightarrow>)) ?\<Psi>\<^sub>1)"
    let ?T\<^sub>1 = "\<lambda> \<Psi>. map (uncurry (op \<rightarrow>)) (zip (map (\<lambda> (\<chi>,\<gamma>). \<psi> \<squnion> \<chi>) \<Psi>) (map snd \<Psi>))"
    let ?T\<^sub>2 = "\<lambda> \<Psi>. map (uncurry (op \<rightarrow>)) (zip (map (\<lambda> (\<chi>,\<gamma>). \<psi> \<rightarrow> \<chi>) \<Psi>) (?T\<^sub>1 \<Psi>))"
    {
      fix \<delta> :: "'a \<times> 'a"
      have "(\<lambda> (\<chi>,\<gamma>). \<psi> \<squnion> \<chi>) = (\<lambda> \<delta>. \<psi> \<squnion> (fst \<delta>))"
           "(\<lambda> (\<chi>,\<gamma>). \<psi> \<rightarrow> \<chi>) = (\<lambda> \<delta>. \<psi> \<rightarrow> (fst \<delta>))"
        by fastforce+
      note functional_identities = this
      have "(\<lambda> (\<chi>,\<gamma>). \<psi> \<squnion> \<chi>) \<delta> = \<psi> \<squnion> (fst \<delta>)"
           "(\<lambda> (\<chi>,\<gamma>). \<psi> \<rightarrow> \<chi>) \<delta> = \<psi> \<rightarrow> (fst \<delta>)"
        by (simp add: functional_identities)+
    }
    hence "?T\<^sub>2 (\<delta> # \<Psi>) = ((\<psi> \<rightarrow> ?\<chi>) \<rightarrow> (\<psi> \<squnion> ?\<chi>) \<rightarrow> ?\<gamma>) # (map (uncurry (op \<rightarrow>)) ?\<Psi>\<^sub>2)"
      by simp
    moreover have "map (uncurry (op \<rightarrow>)) (\<delta> # \<Psi>) = (?\<chi> \<rightarrow> ?\<gamma>) # map (uncurry (op \<rightarrow>)) \<Psi>"
      by (simp add: case_prod_beta)
    moreover
    {
      fix \<chi> \<psi> \<gamma>
      have "\<turnstile> ((\<psi> \<rightarrow> \<chi>) \<rightarrow> (\<psi> \<squnion> \<chi>) \<rightarrow> \<gamma>) \<leftrightarrow> (\<chi> \<rightarrow> \<gamma>)"
      proof -
        have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ((\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<chi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>)"
          by fastforce
        hence "\<turnstile> \<^bold>\<lparr> ((\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<chi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<^bold>\<rparr>"
          using propositional_semantics by blast
        thus ?thesis by simp
      qed
    }
    hence identity: "\<turnstile> ((\<psi> \<rightarrow> ?\<chi>) \<rightarrow> (\<psi> \<squnion> ?\<chi>) \<rightarrow> ?\<gamma>) \<rightarrow> (?\<chi> \<rightarrow> ?\<gamma>)"
      using biconditional_def by auto
    assume "map (uncurry (op \<rightarrow>)) \<Psi> \<preceq> map (uncurry (op \<rightarrow>)) ?\<Psi>\<^sub>2"
    with identity have "((?\<chi> \<rightarrow> ?\<gamma>) # map (uncurry (op \<rightarrow>)) \<Psi>) \<preceq>
                        (((\<psi> \<rightarrow> ?\<chi>) \<rightarrow> (\<psi> \<squnion> ?\<chi>) \<rightarrow> ?\<gamma>) # (map (uncurry (op \<rightarrow>)) ?\<Psi>\<^sub>2))"
      using stronger_theory_left_right_cons by blast
    ultimately show ?case by simp
  qed
  hence "(map (uncurry (op \<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>)) \<preceq> 
         ((map (uncurry (op \<rightarrow>)) ?\<Psi>\<^sub>2) @ \<Gamma> \<ominus> (map snd \<Psi>))"
    using stronger_theory_combine stronger_theory_reflexive by blast
  moreover have "mset ?\<Gamma>\<^sub>2 = mset ((map (uncurry (op \<rightarrow>)) ?\<Psi>\<^sub>2) @ \<Gamma> \<ominus> (map snd ?\<Psi>\<^sub>1))"
    by simp
  ultimately have "(map (uncurry (op \<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>)) \<preceq> ?\<Gamma>\<^sub>2"
    by (simp add: stronger_theory_relation_def)
  hence "?\<Gamma>\<^sub>2 $\<turnstile> \<Phi>"
    using \<Psi>(3) segmented_stronger_theory_left_monotonic by blast
  moreover
  have "(map (uncurry (op \<squnion>)) ?\<Psi>\<^sub>2) :\<turnstile> \<psi> \<rightarrow> \<phi>"
  proof -
    let ?\<Gamma> = "map (\<lambda> (\<chi>, \<gamma>). (\<psi> \<rightarrow> \<chi>) \<squnion> (\<psi> \<squnion> \<chi>) \<rightarrow> \<gamma>) \<Psi>"
    let ?\<Sigma> = "map (\<lambda> (\<chi>, \<gamma>). (\<psi> \<rightarrow> (\<chi> \<squnion> \<gamma>))) \<Psi>"
    have "map (uncurry (op \<squnion>)) ?\<Psi>\<^sub>2 = ?\<Gamma>"
    proof (induct \<Psi>)
      case Nil
      then show ?case by simp
    next
      case (Cons \<chi> \<Psi>)
      have "(\<lambda> \<phi>. (case \<phi> of (\<chi>, \<gamma>) \<Rightarrow> \<psi> \<rightarrow> \<chi>) \<squnion> (case \<phi> of (\<chi>, \<gamma>) \<Rightarrow> \<psi> \<squnion> \<chi>) \<rightarrow> snd \<phi>) = 
            (\<lambda> \<phi>. (case \<phi> of (\<chi>, \<gamma>) \<Rightarrow> \<psi> \<rightarrow> \<chi> \<squnion> (\<psi> \<squnion> \<chi>) \<rightarrow> \<gamma>))"
        by fastforce
      hence "(case \<chi> of (\<chi>, \<gamma>) \<Rightarrow> \<psi> \<rightarrow> \<chi>) \<squnion> (case \<chi> of (\<chi>, \<gamma>) \<Rightarrow> \<psi> \<squnion> \<chi>) \<rightarrow> snd \<chi> = 
             (case \<chi> of (\<chi>, \<gamma>) \<Rightarrow> \<psi> \<rightarrow> \<chi> \<squnion> (\<psi> \<squnion> \<chi>) \<rightarrow> \<gamma>)"
        by smt
      with Cons show ?case by simp
    qed
    moreover have "?\<Sigma> \<preceq> ?\<Gamma>"
    proof (induct \<Psi>)
      case Nil
      then show ?case by simp
    next
      case (Cons \<delta> \<Psi>)
      let ?\<alpha> = "(\<lambda> (\<chi>, \<gamma>). (\<psi> \<rightarrow> \<chi>) \<squnion> (\<psi> \<squnion> \<chi>) \<rightarrow> \<gamma>) \<delta>"
      let ?\<beta> = "(\<lambda> (\<chi>, \<gamma>). (\<psi> \<rightarrow> (\<chi> \<squnion> \<gamma>))) \<delta>"
      let ?\<chi> = "fst \<delta>"
      let ?\<gamma> = "snd \<delta>"
      have "(\<lambda> \<delta>. (case \<delta> of (\<chi>, \<gamma>) \<Rightarrow> \<psi> \<rightarrow> \<chi> \<squnion> (\<psi> \<squnion> \<chi>) \<rightarrow> \<gamma>)) = 
            (\<lambda> \<delta>. \<psi> \<rightarrow> fst \<delta> \<squnion> (\<psi> \<squnion> fst \<delta>) \<rightarrow> snd \<delta>)"
           "(\<lambda> \<delta>. (case \<delta> of (\<chi>, \<gamma>) \<Rightarrow> \<psi> \<rightarrow> (\<chi> \<squnion> \<gamma>))) = (\<lambda> \<delta>. \<psi> \<rightarrow> (fst \<delta> \<squnion> snd \<delta>))"
        by fastforce+
      hence "?\<alpha> = (\<psi> \<rightarrow> ?\<chi>) \<squnion> (\<psi> \<squnion> ?\<chi>) \<rightarrow> ?\<gamma>"
            "?\<beta> = \<psi> \<rightarrow> (?\<chi> \<squnion> ?\<gamma>)"
        by smt+
      moreover
      {
        fix \<psi> \<chi> \<gamma>
        have "\<turnstile> ((\<psi> \<rightarrow> \<chi>) \<squnion> (\<psi> \<squnion> \<chi>) \<rightarrow> \<gamma>) \<rightarrow> (\<psi> \<rightarrow> (\<chi> \<squnion> \<gamma>))"
        proof -
          have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ((\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<squnion> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<chi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>))"
            by fastforce
          hence "\<turnstile> \<^bold>\<lparr> ((\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<squnion> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<chi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>)) \<^bold>\<rparr>"
            using propositional_semantics by blast
          thus ?thesis by simp
        qed
      }
      ultimately have "\<turnstile> ?\<alpha> \<rightarrow> ?\<beta>" by simp
      thus ?case
        using Cons
              stronger_theory_left_right_cons
        by simp
    qed
    moreover have "\<forall> \<phi>. (map (uncurry (op \<squnion>)) \<Psi>) :\<turnstile> \<phi> \<longrightarrow> ?\<Sigma> :\<turnstile> \<psi> \<rightarrow> \<phi>"
    proof (induct \<Psi>)
      case Nil
      then show ?case
        apply simp
        using Axiom_1 Modus_Ponens 
        by blast
    next
      case (Cons \<delta> \<Psi>)
      let ?\<delta>' = "(\<lambda> (\<chi>, \<gamma>). (\<psi> \<rightarrow> (\<chi> \<squnion> \<gamma>))) \<delta>"
      let ?\<Sigma> = "map (\<lambda> (\<chi>, \<gamma>). (\<psi> \<rightarrow> (\<chi> \<squnion> \<gamma>))) \<Psi>"
      let ?\<Sigma>' = "map (\<lambda> (\<chi>, \<gamma>). (\<psi> \<rightarrow> (\<chi> \<squnion> \<gamma>))) (\<delta> # \<Psi>)"
      {
        fix \<phi>
        assume "map (uncurry (op \<squnion>)) (\<delta> # \<Psi>) :\<turnstile> \<phi>"
        hence "map (uncurry (op \<squnion>)) \<Psi> :\<turnstile> (uncurry (op \<squnion>)) \<delta> \<rightarrow> \<phi>"
          using list_deduction_theorem
          by simp
        hence "?\<Sigma> :\<turnstile> \<psi> \<rightarrow> (uncurry (op \<squnion>)) \<delta> \<rightarrow> \<phi>"
          using Cons 
          by blast
        moreover
        {
          fix \<alpha> \<beta> \<gamma>
          have "\<turnstile> (\<alpha> \<rightarrow> \<beta> \<rightarrow> \<gamma>) \<rightarrow> ((\<alpha> \<rightarrow> \<beta>) \<rightarrow> \<alpha> \<rightarrow> \<gamma>)"
            using Axiom_2 by auto
        }
        ultimately have "?\<Sigma> :\<turnstile> (\<psi> \<rightarrow> (uncurry (op \<squnion>)) \<delta>) \<rightarrow> \<psi> \<rightarrow> \<phi>"
          using list_deduction_weaken [where ?\<Gamma>="?\<Sigma>"]
                list_deduction_modus_ponens [where ?\<Gamma>="?\<Sigma>"]
          by smt
        moreover
        have "(\<lambda> \<delta>. \<psi> \<rightarrow> (uncurry (op \<squnion>)) \<delta>) = (\<lambda> \<delta>. (\<lambda> (\<chi>, \<gamma>). (\<psi> \<rightarrow> (\<chi> \<squnion> \<gamma>))) \<delta>)"
          by fastforce
        ultimately have "?\<Sigma> :\<turnstile> (\<lambda> (\<chi>, \<gamma>). (\<psi> \<rightarrow> (\<chi> \<squnion> \<gamma>))) \<delta> \<rightarrow> \<psi> \<rightarrow> \<phi>"
          by smt
        hence "?\<Sigma>' :\<turnstile> \<psi> \<rightarrow> \<phi>"
          using list_deduction_theorem
          by simp
      }
      then show ?case by simp
    qed
    with \<Psi>(2) have "?\<Sigma> :\<turnstile> \<psi> \<rightarrow> \<phi>"
      by blast
    ultimately show ?thesis
      using stronger_theory_deduction_monotonic by auto
  qed
  moreover have "mset (map snd ?\<Psi>\<^sub>2) \<subseteq># mset ?\<Gamma>\<^sub>1" by simp
  ultimately have "?\<Gamma>\<^sub>1 $\<turnstile> (\<psi> \<rightarrow> \<phi> # \<Phi>)" using segmented_deduction.simps(2) by blast
  moreover have "\<turnstile> (map (uncurry op \<squnion>) \<Psi> :\<rightarrow> \<phi>) \<rightarrow> (map (uncurry op \<squnion>) ?\<Psi>\<^sub>1) :\<rightarrow> (\<psi> \<squnion> \<phi>)"
  proof (induct \<Psi>)
    case Nil
    then show ?case
      unfolding disjunction_def
      apply simp
      using Axiom_1 Modus_Ponens 
      by blast
  next
    case (Cons \<nu> \<Psi>)
    let ?\<Delta> = "map (uncurry op \<squnion>) \<Psi>"
    let ?\<Delta>' = "map (uncurry op \<squnion>) (\<nu> # \<Psi>)"
    let ?\<Sigma> = "map (uncurry op \<squnion>) (zip (map (\<lambda> (\<chi>,\<gamma>). \<psi> \<squnion> \<chi>) \<Psi>) (map snd \<Psi>))"
    let ?\<Sigma>' = "map (uncurry op \<squnion>) (zip (map (\<lambda> (\<chi>,\<gamma>). \<psi> \<squnion> \<chi>) (\<nu> # \<Psi>)) (map snd (\<nu> # \<Psi>)))"
    have "\<turnstile> (?\<Delta>' :\<rightarrow>  \<phi>) \<rightarrow> (uncurry op \<squnion>) \<nu> \<rightarrow> ?\<Delta> :\<rightarrow> \<phi>"
      by (simp, metis Axiom_1 Axiom_2 Modus_Ponens)
    with Cons have "\<turnstile> (?\<Delta>' :\<rightarrow>  \<phi>) \<rightarrow> (uncurry op \<squnion>) \<nu> \<rightarrow> ?\<Sigma> :\<rightarrow> (\<psi> \<squnion> \<phi>)"
      using hypothetical_syllogism Modus_Ponens
      by blast
    hence "(?\<Delta>' :\<rightarrow>  \<phi>) # ((uncurry op \<squnion>) \<nu>) # ?\<Sigma> :\<turnstile> \<psi> \<squnion> \<phi>"
      by (simp add: list_deduction_def)
    moreover have "set ((?\<Delta>' :\<rightarrow>  \<phi>) # ((uncurry op \<squnion>) \<nu>) # ?\<Sigma>) = 
                   set (((uncurry op \<squnion>) \<nu>) # (?\<Delta>' :\<rightarrow>  \<phi>) # ?\<Sigma>)"
      by fastforce
    ultimately have "((uncurry op \<squnion>) \<nu>) # (?\<Delta>' :\<rightarrow>  \<phi>) # ?\<Sigma> :\<turnstile> \<psi> \<squnion> \<phi>"
      by (smt insert_subset list.simps(15) list_deduction_monotonic set_subset_Cons)
    hence "(?\<Delta>' :\<rightarrow>  \<phi>) # ?\<Sigma> :\<turnstile> ((uncurry (op \<squnion>)) \<nu>) \<rightarrow> (\<psi> \<squnion> \<phi>)"
      using list_deduction_theorem
      by simp
    moreover
    let ?\<chi> = "fst \<nu>"
    let ?\<gamma> = "snd \<nu>"
    have "(\<lambda> \<nu> . (uncurry (op \<squnion>)) \<nu>) = (\<lambda> \<nu>. fst \<nu> \<squnion> snd \<nu>)"
      by fastforce
    hence "(uncurry (op \<squnion>)) \<nu> = ?\<chi> \<squnion> ?\<gamma>" by simp
    ultimately have "(?\<Delta>' :\<rightarrow>  \<phi>) # ?\<Sigma> :\<turnstile> (?\<chi> \<squnion> ?\<gamma>) \<rightarrow> (\<psi> \<squnion> \<phi>)" by simp
    moreover
    {
      fix \<alpha> \<beta> \<delta> \<gamma>
      have "\<turnstile> ((\<beta> \<squnion> \<alpha>) \<rightarrow> (\<gamma> \<squnion> \<delta>)) \<rightarrow> ((\<gamma> \<squnion> \<beta>) \<squnion> \<alpha>) \<rightarrow> (\<gamma> \<squnion> \<delta>)"
      proof -
        have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ((\<^bold>\<langle>\<beta>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<alpha>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<gamma>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<delta>\<^bold>\<rangle>)) \<rightarrow> ((\<^bold>\<langle>\<gamma>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<beta>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>\<alpha>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<gamma>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<delta>\<^bold>\<rangle>)"
          by fastforce
        hence "\<turnstile> \<^bold>\<lparr> ((\<^bold>\<langle>\<beta>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<alpha>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<gamma>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<delta>\<^bold>\<rangle>)) \<rightarrow> ((\<^bold>\<langle>\<gamma>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<beta>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>\<alpha>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<gamma>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<delta>\<^bold>\<rangle>) \<^bold>\<rparr>"
          using propositional_semantics by blast
        thus ?thesis by simp
      qed
    }
    hence "(?\<Delta>' :\<rightarrow>  \<phi>) # ?\<Sigma> :\<turnstile> ((?\<chi> \<squnion> ?\<gamma>) \<rightarrow> (\<psi> \<squnion> \<phi>)) \<rightarrow> ((\<psi> \<squnion> ?\<chi>) \<squnion> ?\<gamma>) \<rightarrow> (\<psi> \<squnion> \<phi>)"
      using list_deduction_weaken by blast
    ultimately have "(?\<Delta>' :\<rightarrow>  \<phi>) # ?\<Sigma> :\<turnstile> ((\<psi> \<squnion> ?\<chi>) \<squnion> ?\<gamma>) \<rightarrow> (\<psi> \<squnion> \<phi>)"
      using list_deduction_modus_ponens by blast
    hence "((\<psi> \<squnion> ?\<chi>) \<squnion> ?\<gamma>) # (?\<Delta>' :\<rightarrow>  \<phi>) # ?\<Sigma> :\<turnstile> \<psi> \<squnion> \<phi>"
      using list_deduction_theorem
      by simp
    moreover have "set (((\<psi> \<squnion> ?\<chi>) \<squnion> ?\<gamma>) # (?\<Delta>' :\<rightarrow>  \<phi>) # ?\<Sigma>) =
                   set ((?\<Delta>' :\<rightarrow>  \<phi>) # ((\<psi> \<squnion> ?\<chi>) \<squnion> ?\<gamma>) # ?\<Sigma>)"
      by fastforce
    ultimately have "(?\<Delta>' :\<rightarrow>  \<phi>) # ((\<psi> \<squnion> ?\<chi>) \<squnion> ?\<gamma>) # ?\<Sigma> :\<turnstile> \<psi> \<squnion> \<phi>"
      by (smt insert_subset list.simps(15) list_deduction_monotonic set_subset_Cons)
    moreover
    have "(\<lambda> \<nu>. \<psi> \<squnion> fst \<nu>) = (\<lambda> (\<chi>, \<gamma>). \<psi> \<squnion> \<chi>)"
      by fastforce
    hence "\<psi> \<squnion> fst \<nu> = (\<lambda> (\<chi>, \<gamma>). \<psi> \<squnion> \<chi>) \<nu>"
      by smt
    hence "((\<psi> \<squnion> ?\<chi>) \<squnion> ?\<gamma>) # ?\<Sigma> = ?\<Sigma>'"
      by simp
    ultimately have "(?\<Delta>' :\<rightarrow>  \<phi>) # ?\<Sigma>' :\<turnstile> \<psi> \<squnion> \<phi>" by simp
    then show ?case by (simp add: list_deduction_def)
  qed
  with \<Psi>(2) have "map (uncurry (op \<squnion>)) ?\<Psi>\<^sub>1 :\<turnstile> (\<psi> \<squnion> \<phi>)"
    unfolding list_deduction_def
    using Modus_Ponens
    by blast
  moreover have "mset (map snd ?\<Psi>\<^sub>1) \<subseteq># mset \<Gamma>" using \<Psi>(1) by simp
  ultimately show "\<Gamma> $\<turnstile> (\<psi> \<squnion> \<phi> # \<psi> \<rightarrow> \<phi> # \<Phi>)" 
    using segmented_deduction.simps(2) by blast
next
  assume "\<Gamma> $\<turnstile> (\<psi> \<squnion> \<phi> # \<psi> \<rightarrow> \<phi> # \<Phi>)"
  from this obtain \<Psi> where \<Psi>:
    "mset (map snd \<Psi>) \<subseteq># mset \<Gamma>"
    "map (uncurry (op \<squnion>)) \<Psi> :\<turnstile> \<psi> \<squnion> \<phi>"
    "map (uncurry (op \<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>) $\<turnstile> (\<psi> \<rightarrow> \<phi> # \<Phi>)"
    using segmented_deduction.simps(2) by blast
  let ?\<Gamma>' = "map (uncurry (op \<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>)"
  from \<Psi> obtain \<Delta> where \<Delta>:
    "mset (map snd \<Delta>) \<subseteq># mset ?\<Gamma>'"
    "map (uncurry (op \<squnion>)) \<Delta> :\<turnstile> \<psi> \<rightarrow> \<phi>"
    "(map (uncurry (op \<rightarrow>)) \<Delta> @ ?\<Gamma>' \<ominus> (map snd \<Delta>)) $\<turnstile> \<Phi>"
    using segmented_deduction.simps(2) by blast
  let ?\<Omega> = "mergeWitness \<Psi> \<Delta>"
  have "mset (map snd ?\<Omega>) \<subseteq># mset \<Gamma>"
    using \<Delta>(1) \<Psi>(1) mergeWitness_msub_intro 
    by blast 
  moreover have "map (uncurry (op \<squnion>)) ?\<Omega> :\<turnstile> \<phi>"
  proof -
    have "map (uncurry (op \<squnion>)) ?\<Omega> :\<turnstile> \<psi> \<squnion> \<phi>"
         "map (uncurry (op \<squnion>)) ?\<Omega> :\<turnstile> \<psi> \<rightarrow> \<phi>"
      using \<Psi>(2) \<Delta>(2)
            stronger_theory_deduction_monotonic
            right_mergeWitness_stronger_theory
            left_mergeWitness_stronger_theory
      by blast+
    moreover
    have "\<turnstile> (\<psi> \<squnion> \<phi>) \<rightarrow> (\<psi> \<rightarrow> \<phi>) \<rightarrow> \<phi>"
      unfolding disjunction_def
      using Modus_Ponens excluded_middle_elimination flip_implication 
      by blast  
    ultimately show ?thesis 
      using list_deduction_weaken list_deduction_modus_ponens
      by blast
  qed
  moreover have "map (uncurry (op \<rightarrow>)) ?\<Omega> @ \<Gamma> \<ominus> (map snd ?\<Omega>) $\<turnstile> \<Phi>"
    using \<Delta>(1) \<Delta>(3) \<Psi>(1) mergeWitness_segmented_deduction_intro by blast
  ultimately show "\<Gamma> $\<turnstile> (\<phi> # \<Phi>)"
    using segmented_deduction.simps(2) by blast
qed

primrec (in Minimal_Logic) 
  AWitness :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list"
  where
    "AWitness \<Psi> [] = []"
  | "AWitness \<Psi> (\<delta> # \<Delta>) =
       (case find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> of 
             None \<Rightarrow> \<delta> # AWitness \<Psi> \<Delta> 
           | Some \<psi> \<Rightarrow> (fst \<psi> \<rightarrow> fst \<delta>, snd \<psi>) # (AWitness (remove1 \<psi> \<Psi>) \<Delta>))"  

primrec (in Minimal_Logic) 
  AComponent :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list"
  where
    "AComponent \<Psi> [] = []"
  | "AComponent \<Psi> (\<delta> # \<Delta>) =
       (case find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> of 
             None \<Rightarrow> AComponent \<Psi> \<Delta> 
           | Some \<psi> \<Rightarrow> (fst \<psi> \<rightarrow> fst \<delta>, snd \<psi>) # (AComponent (remove1 \<psi> \<Psi>) \<Delta>))"    
    
primrec (in Minimal_Logic) 
  BWitness :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list"
  where
    "BWitness \<Psi> [] = \<Psi>"
  | "BWitness \<Psi> (\<delta> # \<Delta>) =
       (case find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> of 
             None \<Rightarrow> BWitness \<Psi> \<Delta> 
           | Some \<psi> \<Rightarrow> (fst \<psi>, (fst \<psi> \<rightarrow> fst \<delta>) \<rightarrow> snd \<psi>) # 
                       (BWitness (remove1 \<psi> \<Psi>) \<Delta>))"

primrec (in Minimal_Logic) 
  BComponent :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list"
  where
    "BComponent \<Psi> [] = []"
  | "BComponent \<Psi> (\<delta> # \<Delta>) =
       (case find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> of 
             None \<Rightarrow> BComponent \<Psi> \<Delta> 
           | Some \<psi> \<Rightarrow> (fst \<psi>, (fst \<psi> \<rightarrow> fst \<delta>) \<rightarrow> snd \<psi>) # 
                       (BComponent (remove1 \<psi> \<Psi>) \<Delta>))"
    
lemma (in Minimal_Logic) AWitness_right_empty [simp]:
  "AWitness [] \<Delta> = \<Delta>" 
  by (induct \<Delta>, simp+)    

lemma (in Minimal_Logic) BWitness_right_empty [simp]:
  "BWitness [] \<Delta> = []" 
  by (induct \<Delta>, simp+)

lemma (in Minimal_Logic) AWitness_map_snd_decomposition:
   "mset (map snd (AWitness \<Psi> \<Delta>)) 
  = mset (map snd ((firstComponent \<Psi> \<Delta>) @ (\<Delta> \<ominus> (secondComponent \<Psi> \<Delta>))))"
proof -
  have "\<forall>\<Psi>. mset (map snd (AWitness \<Psi> \<Delta>))
         =  mset (map snd ((firstComponent \<Psi> \<Delta>) @ (\<Delta> \<ominus> (secondComponent \<Psi> \<Delta>))))"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "mset (map snd (AWitness \<Psi> (\<delta> # \<Delta>))) =
            mset (map snd (firstComponent \<Psi> (\<delta> # \<Delta>) @ 
                           (\<delta> # \<Delta>) \<ominus> secondComponent \<Psi> (\<delta> # \<Delta>)))"
      using Cons
      by (cases "find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> = None",
          simp, 
          metis (no_types, lifting) 
                add_mset_add_single 
                image_mset_single 
                image_mset_union 
                mset_subset_eq_multiset_union_diff_commute 
                secondComponent_msub,
         fastforce)
    }
    then show ?case by blast
  qed
  thus ?thesis by blast
qed

lemma (in Minimal_Logic) BWitness_map_snd_decomposition:
   "mset (map snd (BWitness \<Psi> \<Delta>)) 
  = mset (map snd ((\<Psi> \<ominus> (firstComponent \<Psi> \<Delta>)) @ (BComponent \<Psi> \<Delta>)))"
proof -
  have "\<forall> \<Psi>. mset (map snd (BWitness \<Psi> \<Delta>)) 
           = mset (map snd ((\<Psi> \<ominus> (firstComponent \<Psi> \<Delta>)) @ (BComponent \<Psi> \<Delta>)))"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "mset (map snd (BWitness \<Psi> (\<delta> # \<Delta>))) 
          = mset (map snd (\<Psi> \<ominus> firstComponent \<Psi> (\<delta> # \<Delta>) @ BComponent \<Psi> (\<delta> # \<Delta>)))"
        using Cons
        by (cases "find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> = None", fastforce+)
    }
    then show ?case by blast
  qed
  thus ?thesis by blast
qed
  
lemma (in Minimal_Logic) AWitness_msub:
  assumes "mset (map snd \<Psi>) \<subseteq># mset \<Gamma>"
      and "mset (map snd \<Delta>) \<subseteq># mset (map (uncurry (op \<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>))"
    shows "mset (map snd (AWitness \<Psi> \<Delta>)) \<subseteq># mset \<Gamma>"
proof -
  have "mset (map snd (\<Delta> \<ominus> (secondComponent \<Psi> \<Delta>))) \<subseteq># mset (\<Gamma> \<ominus> (map snd \<Psi>))"
    using assms secondComponent_diff_msub by blast
  moreover have "mset (map snd (firstComponent \<Psi> \<Delta>)) \<subseteq># mset (map snd \<Psi>)"
    using firstComponent_msub
    by (simp add: image_mset_subseteq_mono)
  moreover have "mset ((map snd \<Psi>) @ (\<Gamma> \<ominus> map snd \<Psi>)) = mset \<Gamma>"
    using assms(1)
    by simp
  moreover have "image_mset snd (mset (firstComponent \<Psi> \<Delta>)) + 
                 image_mset snd (mset (\<Delta> \<ominus> secondComponent \<Psi> \<Delta>)) 
               = mset (map snd (AWitness \<Psi> \<Delta>))"
      using AWitness_map_snd_decomposition by force
  ultimately
  show ?thesis
    by (metis (no_types) mset_append mset_map subset_mset.add_mono)
qed

lemma (in Minimal_Logic) BComponent_msub:
  "mset (map snd (BComponent \<Psi> \<Delta>)) \<subseteq># mset (map (uncurry op \<rightarrow>) (AWitness \<Psi> \<Delta>))"
proof -
  have "\<forall> \<Psi>. mset (map snd (BComponent \<Psi> \<Delta>)) \<subseteq># mset (map (uncurry op \<rightarrow>) (AWitness \<Psi> \<Delta>))"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "mset (map snd (BComponent \<Psi> (\<delta> # \<Delta>))) \<subseteq>#
            mset (map (uncurry op \<rightarrow>) (AWitness \<Psi> (\<delta> # \<Delta>)))"
        using Cons
        by (cases "find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> = None", 
            simp, metis add_mset_add_single 
                        mset_subset_eq_add_left 
                        subset_mset.order_trans,
            fastforce)
    }
    then show ?case by blast
  qed
  thus ?thesis by blast
qed
  
lemma (in Minimal_Logic) BWitness_msub:
  assumes "mset (map snd \<Psi>) \<subseteq># mset \<Gamma>"
      and "mset (map snd \<Delta>) \<subseteq># mset (map (uncurry (op \<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>))"
    shows "mset (map snd (BWitness \<Psi> \<Delta>)) \<subseteq># 
           mset (map (uncurry op \<rightarrow>) (AWitness \<Psi> \<Delta>) @ \<Gamma> \<ominus> map snd (AWitness \<Psi> \<Delta>))"
proof -
  have "mset (map snd (\<Psi> \<ominus> firstComponent \<Psi> \<Delta>)) \<subseteq># mset (\<Gamma> \<ominus> map snd (AWitness \<Psi> \<Delta>))"
    using assms AWitness_map_snd_decomposition
    by (simp, 
        smt add.commute 
            add.left_commute 
            image_mset_Diff 
            listSubtract_mset_homomorphism 
            AWitness_msub 
            firstComponent_msub 
            secondComponent_diff_msub 
            mset_map 
            subset_eq_diff_conv 
            subset_mset.add_le_cancel_left 
            subset_mset.diff_add 
            subset_mset.le_diff_conv2)
  thus ?thesis 
    using BComponent_msub
          BWitness_map_snd_decomposition
    by (simp add: mset_subset_eq_mono_add union_commute)
qed 
  
lemma (in Classical_Propositional_Logic) AWitness_right_stronger_theory:
  "map (uncurry op \<squnion>) \<Delta> \<preceq> map (uncurry op \<squnion>) (AWitness \<Psi> \<Delta>)"
proof -
  have "\<forall> \<Psi>. map (uncurry op \<squnion>) \<Delta> \<preceq> map (uncurry op \<squnion>) (AWitness \<Psi> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "map (uncurry op \<squnion>) (\<delta> # \<Delta>) \<preceq> map (uncurry op \<squnion>) (AWitness \<Psi> (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        then show ?thesis 
          using Cons
          by (simp add: stronger_theory_left_right_cons 
                        trivial_implication) 
      next
        case False
        from this obtain \<psi> where 
          \<psi>: "find (\<lambda>\<psi>. uncurry op \<rightarrow> \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
             "\<psi> \<in> set \<Psi>"
             "(fst \<psi> \<rightarrow> snd \<psi>) = snd \<delta>"
          using find_Some_set_membership
                find_Some_predicate
          by fastforce
        let ?\<Psi>' = "remove1 \<psi> \<Psi>"
        let ?\<alpha> = "fst \<psi>"
        let ?\<beta> = "snd \<psi>"
        let ?\<gamma> = "fst \<delta>"
        have "map (uncurry op \<squnion>) \<Delta> \<preceq> map (uncurry op \<squnion>) (AWitness ?\<Psi>' \<Delta>)"
          using Cons by simp
        moreover
        have "(uncurry op \<squnion>) = (\<lambda> \<delta>. fst \<delta> \<squnion> snd \<delta>)" by fastforce
        hence "(uncurry op \<squnion>) \<delta> = ?\<gamma> \<squnion> (?\<alpha> \<rightarrow> ?\<beta>)" using \<psi>(3) by fastforce
        moreover
        {
          fix \<alpha> \<beta> \<gamma>
          have "\<turnstile> (\<alpha> \<rightarrow> \<gamma> \<squnion> \<beta>) \<rightarrow> (\<gamma> \<squnion> (\<alpha> \<rightarrow> \<beta>))"
          proof -
            let ?\<phi> = "(\<^bold>\<langle>\<alpha>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<gamma>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<beta>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<gamma>\<^bold>\<rangle> \<squnion> (\<^bold>\<langle>\<alpha>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<beta>\<^bold>\<rangle>))"
            have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
            hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
            thus ?thesis by simp
          qed
        }
        hence "\<turnstile> (?\<alpha> \<rightarrow> ?\<gamma> \<squnion> ?\<beta>) \<rightarrow> (?\<gamma> \<squnion> (?\<alpha> \<rightarrow> ?\<beta>))" by simp
        ultimately 
        show ?thesis using \<psi> 
          by (simp add: stronger_theory_left_right_cons)
      qed
    }
    then show ?case by simp
  qed
  thus ?thesis by simp
qed
  
lemma (in Classical_Propositional_Logic) BWitness_left_stronger_theory:
  "map (uncurry op \<squnion>) \<Psi> \<preceq> map (uncurry op \<squnion>) (BWitness \<Psi> \<Delta>)"
proof -
  have "\<forall> \<Psi>. map (uncurry op \<squnion>) \<Psi> \<preceq> map (uncurry op \<squnion>) (BWitness \<Psi> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "map (uncurry op \<squnion>) \<Psi> \<preceq> map (uncurry op \<squnion>) (BWitness \<Psi> (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        then show ?thesis using Cons by simp
      next
        case False
        from this obtain \<psi> where 
          \<psi>: "find (\<lambda>\<psi>. uncurry op \<rightarrow> \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
             "\<psi> \<in> set \<Psi>"
             "(uncurry op \<squnion>) \<psi> = fst \<psi> \<squnion> snd \<psi>"
          using find_Some_set_membership
          by fastforce
        let ?\<phi> = "fst \<psi> \<squnion> (fst \<psi> \<rightarrow> fst \<delta>) \<rightarrow> snd \<psi>"
        let ?\<Psi>' = "remove1 \<psi> \<Psi>"
        have "map (uncurry op \<squnion>) ?\<Psi>' \<preceq> map (uncurry op \<squnion>) (BWitness ?\<Psi>' \<Delta>)"
          using Cons by simp
        moreover 
        {
          fix \<alpha> \<beta> \<gamma>
          have "\<turnstile> (\<alpha> \<squnion> (\<alpha> \<rightarrow> \<gamma>) \<rightarrow> \<beta>) \<rightarrow> (\<alpha> \<squnion> \<beta>)"
          proof -
            let ?\<phi> = "(\<^bold>\<langle>\<alpha>\<^bold>\<rangle> \<squnion> (\<^bold>\<langle>\<alpha>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>\<beta>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<alpha>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<beta>\<^bold>\<rangle>)"
            have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
            hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
            thus ?thesis by simp
          qed
        }
        hence "\<turnstile> ?\<phi> \<rightarrow> (uncurry op \<squnion>) \<psi>" using \<psi>(3) by auto
        ultimately 
        have "map (uncurry op \<squnion>) (\<psi> # ?\<Psi>') \<preceq> (?\<phi> # map (uncurry op \<squnion>) (BWitness ?\<Psi>' \<Delta>))"
          by (simp add: stronger_theory_left_right_cons)
        moreover
        from \<psi> have "mset (map (uncurry op \<squnion>) (\<psi> # ?\<Psi>')) = mset (map (uncurry op \<squnion>) \<Psi>)"
          by (metis mset_eq_perm mset_map perm_remove)
        ultimately show ?thesis
          using stronger_theory_relation_alt_def \<psi>(1) by auto
      qed
    }
    then show ?case by blast
  qed
  thus ?thesis by blast
qed

lemma (in Minimal_Logic) AWitness_secondComponent_diff_decomposition:
  "mset (AWitness \<Psi> \<Delta>) = mset (AComponent \<Psi> \<Delta> @ \<Delta> \<ominus> secondComponent \<Psi> \<Delta>)"
proof -
  have "\<forall> \<Psi>. mset (AWitness \<Psi> \<Delta>) = mset (AComponent \<Psi> \<Delta> @ \<Delta> \<ominus> secondComponent \<Psi> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "mset (AWitness \<Psi> (\<delta> # \<Delta>)) = 
            mset (AComponent \<Psi> (\<delta> # \<Delta>) @ (\<delta> # \<Delta>) \<ominus> secondComponent \<Psi> (\<delta> # \<Delta>))"
        using Cons
        by (cases "find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> = None",
            simp, metis add_mset_add_single secondComponent_msub subset_mset.diff_add_assoc2,
            fastforce)
    }
    then show ?case by blast
  qed
  thus ?thesis by blast
qed  
  
lemma (in Minimal_Logic) BWitness_firstComponent_diff_decomposition:
  "mset (BWitness \<Psi> \<Delta>) = mset (\<Psi> \<ominus> firstComponent \<Psi> \<Delta> @ BComponent \<Psi> \<Delta>)"
proof -
  have "\<forall> \<Psi>. mset (BWitness \<Psi> \<Delta>) = mset (\<Psi> \<ominus> firstComponent \<Psi> \<Delta> @ BComponent \<Psi> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "mset (BWitness \<Psi> (\<delta> # \<Delta>)) = 
            mset (\<Psi> \<ominus> firstComponent \<Psi> (\<delta> # \<Delta>) @ BComponent \<Psi> (\<delta> # \<Delta>))"
      using Cons
        by (cases "find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> = None", simp, fastforce)
    }
    then show ?case by blast
  qed
  thus ?thesis by blast
qed
  
lemma (in Minimal_Logic) BWitness_right_stronger_theory:
    "map (uncurry op \<rightarrow>) \<Delta> 
  \<preceq>  map (uncurry op \<rightarrow>) (BWitness \<Psi> \<Delta> \<ominus> (\<Psi> \<ominus> firstComponent \<Psi> \<Delta>) @ (\<Delta> \<ominus> secondComponent \<Psi> \<Delta>))" 
proof -
  let ?\<ff> = "\<lambda>\<Psi> \<Delta>. (\<Psi> \<ominus> firstComponent \<Psi> \<Delta>)"
  let ?\<gg> = "\<lambda> \<Psi> \<Delta>. (\<Delta> \<ominus> secondComponent \<Psi> \<Delta>)"
  have "\<forall> \<Psi>. map (uncurry op \<rightarrow>) \<Delta> \<preceq>  map (uncurry op \<rightarrow>) (BWitness \<Psi> \<Delta> \<ominus> ?\<ff> \<Psi> \<Delta> @ ?\<gg> \<Psi> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    let ?\<delta> = "(uncurry op \<rightarrow>) \<delta>"
    {
      fix \<Psi>
      have "map (uncurry op \<rightarrow>) (\<delta> # \<Delta>)
          \<preceq> map (uncurry op \<rightarrow>) (BWitness \<Psi> (\<delta> # \<Delta>) \<ominus> ?\<ff> \<Psi> (\<delta> # \<Delta>) @ ?\<gg> \<Psi> (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        moreover
        from Cons have 
          "map (uncurry op \<rightarrow>) (\<delta> # \<Delta>) 
         \<preceq> map (uncurry op \<rightarrow>) (\<delta> # BWitness \<Psi> \<Delta> \<ominus> ?\<ff> \<Psi> \<Delta> @ ?\<gg> \<Psi> \<Delta>)"
          by (simp add: stronger_theory_left_right_cons trivial_implication)
        moreover 
        have "mset (map (uncurry op \<rightarrow>) (\<delta> # BWitness \<Psi> \<Delta> \<ominus> ?\<ff> \<Psi> \<Delta> @ ?\<gg> \<Psi> \<Delta>))
            = mset (map (uncurry op \<rightarrow>) (BWitness \<Psi> \<Delta> \<ominus> ?\<ff> \<Psi> \<Delta> @ 
                                         ((\<delta> # \<Delta>) \<ominus> secondComponent \<Psi> \<Delta>)))" 
          by (simp, 
              metis (no_types, lifting) 
                    add_mset_add_single 
                    image_mset_single 
                    image_mset_union 
                    secondComponent_msub 
                    mset_subset_eq_multiset_union_diff_commute)
        ultimately show ?thesis
          by (simp, 
              smt list.simps(9) 
                  stronger_theory_relation_def 
                  map_append 
                  uncurry_def) 
      next
        case False
        from this obtain \<psi> where  
          \<psi>: "find (\<lambda>\<psi>. uncurry op \<rightarrow> \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
             "uncurry op \<rightarrow> \<psi> = snd \<delta>"
          using find_Some_predicate
          by fastforce
        let ?\<alpha> = "fst \<psi>"
        let ?\<beta> = "fst \<delta>"
        let ?\<gamma> = "snd \<psi>"
        have "(\<lambda> \<delta>. fst \<delta> \<rightarrow> snd \<delta>) = uncurry op \<rightarrow>" by fastforce
        hence "?\<beta> \<rightarrow> ?\<alpha> \<rightarrow> ?\<gamma> = uncurry op \<rightarrow> \<delta>" using \<psi>(2) by smt
        moreover
        let ?A = "BWitness (remove1 \<psi> \<Psi>) \<Delta>"
        let ?B = "firstComponent (remove1 \<psi> \<Psi>) \<Delta>"
        let ?C = "secondComponent (remove1 \<psi> \<Psi>) \<Delta>"
        let ?D = "?A \<ominus> ((remove1 \<psi> \<Psi>) \<ominus> ?B)"
        have "mset ((remove1 \<psi> \<Psi>) \<ominus> ?B) \<subseteq># mset ?A"
          using BWitness_firstComponent_diff_decomposition by simp 
        hence "mset (map (uncurry op \<rightarrow>) 
                    (((?\<alpha>, (?\<alpha> \<rightarrow> ?\<beta>) \<rightarrow> ?\<gamma>) # ?A) \<ominus> remove1 \<psi> (\<Psi> \<ominus> ?B) 
                    @ (remove1 \<delta> ((\<delta> # \<Delta>) \<ominus> ?C))))
            = mset ((?\<alpha> \<rightarrow> (?\<alpha> \<rightarrow> ?\<beta>) \<rightarrow> ?\<gamma>) # map (uncurry op \<rightarrow>) (?D @ (\<Delta> \<ominus> ?C)))"
          by (simp,
              smt add_mset_add_single 
                  image_mset_single 
                  image_mset_union
                  prod.simps(2) 
                  subset_mset.add_diff_assoc2)
        moreover
        have "\<turnstile> (?\<alpha> \<rightarrow> (?\<alpha> \<rightarrow> ?\<beta>) \<rightarrow> ?\<gamma>) \<rightarrow> ?\<beta> \<rightarrow> ?\<alpha> \<rightarrow> ?\<gamma>"
        proof -
          let ?\<Gamma> = "[(?\<alpha> \<rightarrow> (?\<alpha> \<rightarrow> ?\<beta>) \<rightarrow> ?\<gamma>), ?\<beta>, ?\<alpha>]"
          have "?\<Gamma> :\<turnstile> ?\<alpha> \<rightarrow> (?\<alpha> \<rightarrow> ?\<beta>) \<rightarrow> ?\<gamma>" 
               "?\<Gamma> :\<turnstile> ?\<alpha>"
            by (simp add: list_deduction_reflection)+
          hence "?\<Gamma> :\<turnstile> (?\<alpha> \<rightarrow> ?\<beta>) \<rightarrow> ?\<gamma>"
            using list_deduction_modus_ponens by blast
          moreover have "?\<Gamma> :\<turnstile> ?\<beta>"
            by (simp add: list_deduction_reflection)
          hence "?\<Gamma> :\<turnstile> ?\<alpha> \<rightarrow> ?\<beta>"
            using Axiom_1 list_deduction_modus_ponens list_deduction_weaken by blast
          ultimately have "?\<Gamma> :\<turnstile> ?\<gamma>"
            using list_deduction_modus_ponens by blast
          thus ?thesis
            unfolding list_deduction_def by simp
        qed 
        hence "(?\<beta> \<rightarrow> ?\<alpha> \<rightarrow> ?\<gamma> # map (uncurry op \<rightarrow>) \<Delta>) \<preceq> 
                (?\<alpha> \<rightarrow> (?\<alpha> \<rightarrow> ?\<beta>) \<rightarrow> ?\<gamma> # map (uncurry op \<rightarrow>) (?D @ (\<Delta> \<ominus> ?C)))"
          using Cons stronger_theory_left_right_cons by blast      
        ultimately show ?thesis 
          using \<psi> by (simp add: stronger_theory_relation_alt_def)
      qed
    }
    then show ?case by blast
  qed
  thus ?thesis by blast
qed

lemma (in Minimal_Logic) AComponent_BComponent_connection:
  "map (uncurry op \<rightarrow>) (AComponent \<Psi> \<Delta>) = map snd (BComponent \<Psi> \<Delta>)"
proof -
  have "\<forall> \<Psi>. map (uncurry op \<rightarrow>) (AComponent \<Psi> \<Delta>) = map snd (BComponent \<Psi> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "map (uncurry op \<rightarrow>) (AComponent \<Psi> (\<delta> # \<Delta>)) = map snd (BComponent \<Psi> (\<delta> # \<Delta>))"
        using Cons
        by (cases "find (\<lambda> \<psi>. (uncurry op \<rightarrow>) \<psi> = snd \<delta>) \<Psi> = None", simp, fastforce)
    }
    then show ?case by blast
  qed
  thus ?thesis by blast
qed
  
lemma (in Classical_Propositional_Logic) AWitness_BWitness_segmented_deduction_intro:
  assumes "mset (map snd \<Psi>) \<subseteq># mset \<Gamma>"
      and "mset (map snd \<Delta>) \<subseteq># mset (map (uncurry op \<rightarrow>) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>))"
      and "map (uncurry op \<rightarrow>) \<Delta> @ (map (uncurry op \<rightarrow>) \<Psi> @ \<Gamma> \<ominus> map snd \<Psi>) \<ominus> map snd \<Delta> $\<turnstile> \<Phi>"
          (is "?\<Gamma>\<^sub>0 $\<turnstile> \<Phi>")
        shows "map (uncurry op \<rightarrow>) (BWitness \<Psi> \<Delta>) @ 
                (map (uncurry op \<rightarrow>) (AWitness \<Psi> \<Delta>) @ \<Gamma> \<ominus> map snd (AWitness \<Psi> \<Delta>)) \<ominus> 
                 map snd (BWitness \<Psi> \<Delta>) $\<turnstile> \<Phi>"
          (is "?\<Gamma> $\<turnstile> \<Phi>")
proof -
  let ?A = "map (uncurry op \<rightarrow>) (BWitness \<Psi> \<Delta>)"
  let ?B = "map (uncurry op \<rightarrow>) (AWitness \<Psi> \<Delta>)"
  let ?C = "\<Psi> \<ominus> firstComponent \<Psi> \<Delta>"
  let ?D = "map (uncurry op \<rightarrow>) ?C"
  let ?E = "\<Delta> \<ominus> secondComponent \<Psi> \<Delta>"
  let ?F = "map (uncurry op \<rightarrow>) ?E"
  let ?G = "map snd (secondComponent \<Psi> \<Delta>)"
  let ?H = "map (uncurry op \<rightarrow>) (AComponent \<Psi> \<Delta>)"
  let ?I = "firstComponent \<Psi> \<Delta>"
  let ?J = "map snd (AWitness \<Psi> \<Delta>)"
  let ?K = "map snd (BWitness \<Psi> \<Delta>)"
  have "mset (map (uncurry op \<rightarrow>) (BWitness \<Psi> \<Delta> \<ominus> ?C @ ?E)) = mset (?A \<ominus> ?D @ ?F)" 
    by (simp add: BWitness_firstComponent_diff_decomposition) 
  hence "(map (uncurry op \<rightarrow>) \<Delta>) \<preceq> (?A \<ominus> ?D @ ?F)"
    using BWitness_right_stronger_theory
    by (smt stronger_theory_relation_alt_def)
  hence "?\<Gamma>\<^sub>0 \<preceq> ((?A \<ominus> ?D @ ?F) @ (map (uncurry op \<rightarrow>) \<Psi> @ \<Gamma> \<ominus> map snd \<Psi>) \<ominus> map snd \<Delta>)"
    using stronger_theory_combine stronger_theory_reflexive by blast
  moreover
  have \<spadesuit>: "mset ?G \<subseteq># mset (map (uncurry op \<rightarrow>) \<Psi>)"
          "mset (secondComponent \<Psi> \<Delta>) \<subseteq># mset \<Delta>"
          "mset (map snd ?E) \<subseteq># mset (\<Gamma> \<ominus> map snd \<Psi>)"
          "mset (map (uncurry op \<rightarrow>) \<Psi> \<ominus> ?G) = mset ?D"
          "mset ?D \<subseteq># mset ?A"
          "mset (map snd ?I) \<subseteq># mset (map snd \<Psi>)"
          "mset (map snd ?I) \<subseteq># mset \<Gamma>"
          "mset (map snd (?I @ ?E)) = mset ?J"
    using secondComponent_msub
          secondComponent_diff_msub
          secondComponent_snd_projection_msub
          firstComponent_secondComponent_mset_connection
          AWitness_map_snd_decomposition
    by (simp, simp,
        metis assms(2),
        simp add: image_mset_Diff firstComponent_msub,
        simp add: BWitness_firstComponent_diff_decomposition,
        simp add: image_mset_subseteq_mono firstComponent_msub,
        metis assms(1) firstComponent_msub map_monotonic subset_mset.dual_order.trans,
        simp)
  hence "mset ((map (uncurry op \<rightarrow>) \<Psi> @ \<Gamma> \<ominus> map snd \<Psi>) \<ominus> map snd \<Delta>)
      = mset (?D @ (\<Gamma> \<ominus> ?J) \<ominus> map snd ?C)"
    by (simp,
        smt Multiset.diff_add 
            image_mset_union 
            firstComponent_msub
            AWitness_map_snd_decomposition
            subset_mset.add_diff_assoc 
            subset_mset.diff_add 
            union_commute)
  ultimately have "?\<Gamma>\<^sub>0 \<preceq> ((?A \<ominus> ?D @ ?F) @ ?D @ (\<Gamma> \<ominus> ?J) \<ominus> map snd ?C)"
    unfolding stronger_theory_relation_alt_def
    by simp
  moreover
  have "mset ?F = mset (?B \<ominus> ?H)"
       "mset ?D \<subseteq># mset ?A"
       "mset (map snd (\<Psi> \<ominus> ?I)) \<subseteq># mset (\<Gamma> \<ominus> ?J)"
    by (simp add: AWitness_secondComponent_diff_decomposition,
        simp add: BWitness_firstComponent_diff_decomposition,
        smt \<spadesuit> assms 
            ab_semigroup_add_class.add_ac(1) 
            listSubtract_mset_homomorphism 
            AWitness_msub 
            firstComponent_msub 
            map_append 
            map_listSubtract_mset_equivalence 
            mset_append 
            subset_mset.diff_add 
            subset_mset.le_diff_conv2 union_commute)
  hence "mset ((?A \<ominus> ?D @ ?F) @ ?D @ (\<Gamma> \<ominus> ?J) \<ominus> map snd ?C)
       = mset (?A @ (?B \<ominus> ?H @ \<Gamma> \<ominus> ?J) \<ominus> map snd ?C)"
        "mset ?H \<subseteq># mset ?B"
    by (simp add: subset_mset.diff_add_assoc,
        simp add: AWitness_secondComponent_diff_decomposition)
  hence "mset ((?A \<ominus> ?D @ ?F) @ ?D @ (\<Gamma> \<ominus> ?J) \<ominus> map snd ?C)
       = mset (?A @ (?B @ \<Gamma> \<ominus> ?J) \<ominus> (?H @ map snd ?C))"
    by (simp add: subset_mset.diff_add_assoc)
  hence "mset ((?A \<ominus> ?D @ ?F) @ ?D @ (\<Gamma> \<ominus> ?J) \<ominus> map snd ?C)
       = mset (?A @ (?B @ \<Gamma> \<ominus> ?J) \<ominus> ?K)"
    by (simp, 
        smt add.commute 
            listSubtract_mset_homomorphism 
            AComponent_BComponent_connection 
            BWitness_map_snd_decomposition 
            map_append mset_map uncurry_def 
            union_code)
  ultimately have "?\<Gamma>\<^sub>0 \<preceq> (?A @ (?B @ \<Gamma> \<ominus> ?J) \<ominus> ?K)"
    unfolding stronger_theory_relation_alt_def
    by smt
  thus ?thesis
    using assms(3) segmented_stronger_theory_left_monotonic 
    by blast 
qed
    
lemma (in Classical_Propositional_Logic) segmented_cons_cons_right_permute:
  assumes "\<Gamma> $\<turnstile> (\<phi> # \<psi> # \<Phi>)"
  shows "\<Gamma> $\<turnstile> (\<psi> # \<phi> # \<Phi>)"
proof -
  from assms obtain \<Psi> where \<Psi>:
    "mset (map snd \<Psi>) \<subseteq># mset \<Gamma>"
    "map (uncurry (op \<squnion>)) \<Psi> :\<turnstile> \<phi>"
    "map (uncurry (op \<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>) $\<turnstile> (\<psi> # \<Phi>)"
    by fastforce
  let ?\<Gamma>\<^sub>0 = "map (uncurry (op \<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>)"
  from \<Psi>(3) obtain \<Delta> where \<Delta>:
    "mset (map snd \<Delta>) \<subseteq># mset ?\<Gamma>\<^sub>0"
    "map (uncurry (op \<squnion>)) \<Delta> :\<turnstile> \<psi>"
    "(map (uncurry (op \<rightarrow>)) \<Delta> @ ?\<Gamma>\<^sub>0 \<ominus> (map snd \<Delta>)) $\<turnstile> \<Phi>"
    using segmented_deduction.simps(2) by blast
  let ?\<Psi>' = "AWitness \<Psi> \<Delta>"
  let ?\<Gamma>\<^sub>1 = "map (uncurry (op \<rightarrow>)) ?\<Psi>' @ \<Gamma> \<ominus> (map snd ?\<Psi>')"
  let ?\<Delta>' = "BWitness \<Psi> \<Delta>"
  have "(map (uncurry (op \<rightarrow>)) ?\<Delta>' @ ?\<Gamma>\<^sub>1 \<ominus> (map snd ?\<Delta>')) $\<turnstile> \<Phi>"
       "map (uncurry (op \<squnion>)) \<Psi> \<preceq> map (uncurry (op \<squnion>)) ?\<Delta>'"
    using \<Psi>(1) \<Delta>(1) \<Delta>(3) 
          AWitness_BWitness_segmented_deduction_intro 
          BWitness_left_stronger_theory 
    by auto
  hence "?\<Gamma>\<^sub>1 $\<turnstile> (\<phi> # \<Phi>)"
    using \<Psi>(1) \<Psi>(2) \<Delta>(1) 
          BWitness_msub segmented_deduction.simps(2)
          stronger_theory_deduction_monotonic
    by blast
  thus ?thesis
    using \<Psi>(1) \<Delta>(1) \<Delta>(2) 
          AWitness_msub 
          AWitness_right_stronger_theory
          segmented_deduction.simps(2)
          stronger_theory_deduction_monotonic
    by blast
qed

lemma (in Classical_Propositional_Logic) segmented_cons_remove1:
  assumes "\<phi> \<in> set \<Phi>"
    shows "\<Gamma> $\<turnstile> \<Phi> = \<Gamma> $\<turnstile> (\<phi> # (remove1 \<phi> \<Phi>))"
proof -
  from \<open>\<phi> \<in> set \<Phi>\<close>
  have "\<forall> \<Gamma>. \<Gamma> $\<turnstile> \<Phi> = \<Gamma> $\<turnstile> (\<phi> # (remove1 \<phi> \<Phi>))"
  proof (induct \<Phi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<chi> \<Phi>)
    {
      fix \<Gamma>
      have "\<Gamma> $\<turnstile> (\<chi> # \<Phi>) = \<Gamma> $\<turnstile> (\<phi> # (remove1 \<phi> (\<chi> # \<Phi>)))"
      proof (cases "\<chi> = \<phi>")
        case True
        then show ?thesis by simp
      next
        case False
        hence "\<phi> \<in> set \<Phi>"
          using Cons.prems by simp
        with Cons.hyps have "\<Gamma> $\<turnstile> (\<chi> # \<Phi>) = \<Gamma> $\<turnstile> (\<chi> # \<phi> # (remove1 \<phi> \<Phi>))"
          by fastforce
        hence "\<Gamma> $\<turnstile> (\<chi> # \<Phi>) = \<Gamma> $\<turnstile> (\<phi> # \<chi> # (remove1 \<phi> \<Phi>))"
          using segmented_cons_cons_right_permute by blast
        then show ?thesis using \<open>\<chi> \<noteq> \<phi>\<close> by simp
      qed
    }
    then show ?case by blast
  qed
  thus ?thesis using assms by blast
qed

lemma (in Classical_Propositional_Logic) witness_stronger_theory:
  assumes "mset (map snd \<Psi>) \<subseteq># mset \<Gamma>"
  shows "(map (uncurry (op \<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>)) \<preceq> \<Gamma>"
proof -
  have "\<forall> \<Gamma>. mset (map snd \<Psi>) \<subseteq># mset \<Gamma> \<longrightarrow>
             (map (uncurry (op \<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>)) \<preceq> \<Gamma>"
  proof (induct \<Psi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<psi> \<Psi>)
    let ?\<gamma> = "snd \<psi>"
    {
      fix \<Gamma>
      assume "mset (map snd (\<psi> # \<Psi>)) \<subseteq># mset \<Gamma>"
      hence "mset (map snd \<Psi>) \<subseteq># mset (remove1 (snd \<psi>) \<Gamma>)"
        by (simp add: insert_subset_eq_iff)
      with Cons have 
        "(map (uncurry (op \<rightarrow>)) \<Psi> @ (remove1 (snd \<psi>) \<Gamma>) \<ominus> (map snd \<Psi>)) \<preceq> (remove1 ?\<gamma> \<Gamma>)"
        by blast
      hence "(map (uncurry (op \<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd (\<psi> # \<Psi>))) \<preceq> (remove1 ?\<gamma> \<Gamma>)"
        by (simp add: stronger_theory_relation_alt_def)
      moreover
      have "(uncurry (op \<rightarrow>)) = (\<lambda> \<psi>. fst \<psi> \<rightarrow> snd \<psi>)" 
        by fastforce
      hence "\<turnstile> ?\<gamma> \<rightarrow> uncurry (op \<rightarrow>) \<psi>"
        using Axiom_1 by simp
      ultimately have 
        "(map (uncurry (op \<rightarrow>)) (\<psi> # \<Psi>) @ \<Gamma> \<ominus> (map snd (\<psi> # \<Psi>))) \<preceq> (?\<gamma> # (remove1 ?\<gamma> \<Gamma>))"
        using stronger_theory_left_right_cons by auto
      hence "(map (uncurry (op \<rightarrow>)) (\<psi> # \<Psi>) @ \<Gamma> \<ominus> (map snd (\<psi> # \<Psi>))) \<preceq> \<Gamma>"
        using stronger_theory_relation_alt_def 
              \<open>mset (map snd (\<psi> # \<Psi>)) \<subseteq># mset \<Gamma>\<close>  
              mset_subset_eqD 
        by fastforce
    }
    then show ?case by blast
  qed
  thus ?thesis using assms by blast
qed

lemma (in Classical_Propositional_Logic) segmented_msub_weaken:
  assumes "mset \<Psi> \<subseteq># mset \<Phi>"
      and "\<Gamma> $\<turnstile> \<Phi>"
    shows "\<Gamma> $\<turnstile> \<Psi>"
proof -
  have "\<forall>\<Psi> \<Gamma>. mset \<Psi> \<subseteq># mset \<Phi> \<longrightarrow> \<Gamma> $\<turnstile> \<Phi> \<longrightarrow> \<Gamma> $\<turnstile> \<Psi>"
  proof (induct \<Phi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<phi> \<Phi>)
    {
      fix \<Psi> \<Gamma>
      assume "mset \<Psi> \<subseteq># mset (\<phi> # \<Phi>)"
             "\<Gamma> $\<turnstile> (\<phi> # \<Phi>)"
      hence "\<Gamma> $\<turnstile> \<Phi>"
        using segmented_deduction.simps(2) 
              segmented_stronger_theory_left_monotonic 
              witness_stronger_theory 
        by blast
      have "\<Gamma> $\<turnstile> \<Psi>"
      proof (cases "\<phi> \<in> set \<Psi>")
        case True
        hence "mset (remove1 \<phi> \<Psi>) \<subseteq># mset \<Phi>"
          using \<open>mset \<Psi> \<subseteq># mset (\<phi> # \<Phi>)\<close> 
                subset_eq_diff_conv 
          by force
        hence "\<forall>\<Gamma>. \<Gamma> $\<turnstile> \<Phi> \<longrightarrow> \<Gamma> $\<turnstile> (remove1 \<phi> \<Psi>)"
          using Cons by blast 
        hence "\<Gamma> $\<turnstile> (\<phi> # (remove1 \<phi> \<Psi>))"
          using \<open>\<Gamma> $\<turnstile> (\<phi> # \<Phi>)\<close> by fastforce
        then show ?thesis
          using \<open>\<phi> \<in> set \<Psi>\<close> 
                segmented_cons_remove1 
          by blast
      next
        case False
        hence "mset \<Psi> \<subseteq># mset \<Phi>"
          by (smt \<open>mset \<Psi> \<subseteq># mset (\<phi> # \<Phi>)\<close> 
                  diff_single_trivial 
                  in_multiset_in_set 
                  mset.simps(1) 
                  mset.simps(2) 
                  mset_append mset_eq_perm 
                  perm_append_single 
                  subset_eq_diff_conv)
        then show ?thesis 
          using \<open>\<Gamma> $\<turnstile> \<Phi>\<close> 
                Cons
          by blast
      qed
    }
    then show ?case by blast
  qed
  with assms show ?thesis by blast
qed

lemma (in Classical_Propositional_Logic) segmented_stronger_theory_right_antitonic:
  assumes "\<Psi> \<preceq> \<Phi>"
      and "\<Gamma> $\<turnstile> \<Phi>"
    shows "\<Gamma> $\<turnstile> \<Psi>"
proof -
  have "\<forall>\<Psi> \<Gamma>. \<Psi> \<preceq> \<Phi> \<longrightarrow> \<Gamma> $\<turnstile> \<Phi> \<longrightarrow> \<Gamma> $\<turnstile> \<Psi>"
  proof (induct \<Phi>)
    case Nil
    then show ?case
      using segmented_deduction.simps(1) 
            stronger_theory_empty_list_intro 
      by blast 
  next
    case (Cons \<phi> \<Phi>)
    {
      fix \<Psi> \<Gamma>
      assume "\<Gamma> $\<turnstile> (\<phi> # \<Phi>)"
             "\<Psi> \<preceq> (\<phi> # \<Phi>)"
      from this obtain \<Sigma> where 
        \<Sigma>: "map snd \<Sigma> = \<Psi>"
           "mset (map fst \<Sigma>) \<subseteq># mset (\<phi> # \<Phi>)"
           "\<forall>(\<phi>,\<psi>)\<in>set \<Sigma>. \<turnstile> \<phi> \<rightarrow> \<psi>"
        unfolding stronger_theory_relation_def
        by auto
      hence "\<Gamma> $\<turnstile> \<Psi>"
      proof (cases "\<phi> \<in> set (map fst \<Sigma>)")
        case True
        from this obtain \<psi> where "(\<phi>,\<psi>) \<in> set \<Sigma>"
          by (induct \<Sigma>, simp, fastforce)
        hence "mset (map snd (remove1 (\<phi>, \<psi>) \<Sigma>)) = mset (remove1 \<psi> \<Psi>)"
              "mset (map fst (remove1 (\<phi>, \<psi>) \<Sigma>)) \<subseteq># mset \<Phi>"
              "\<forall>(\<phi>,\<psi>)\<in>set (remove1 (\<phi>, \<psi>) \<Sigma>). \<turnstile> \<phi> \<rightarrow> \<psi>"
          using \<Sigma> remove1_pairs_list_projections_snd 
                  remove1_pairs_list_projections_fst 
                  subset_eq_diff_conv 
          apply (fastforce,fastforce)
          using \<Sigma>(3) by fastforce  
        hence "(remove1 \<psi> \<Psi>) \<preceq> \<Phi>"
          unfolding stronger_theory_relation_alt_def by blast
        moreover
        from \<open>\<Gamma> $\<turnstile> (\<phi> # \<Phi>)\<close> obtain \<Delta> where 
          \<Delta>: "mset (map snd \<Delta>) \<subseteq># mset \<Gamma>"
              "map (uncurry (op \<squnion>)) \<Delta> :\<turnstile> \<phi>"
              "(map (uncurry (op \<rightarrow>)) \<Delta> @ \<Gamma> \<ominus> (map snd \<Delta>)) $\<turnstile> \<Phi>"
          by auto
        ultimately have "(map (uncurry (op \<rightarrow>)) \<Delta> @ \<Gamma> \<ominus> (map snd \<Delta>)) $\<turnstile> remove1 \<psi> \<Psi>"
          using Cons by blast
        moreover have "map (uncurry (op \<squnion>)) \<Delta> :\<turnstile> \<psi>"
          using \<Delta>(2) \<Sigma>(3) \<open>(\<phi>,\<psi>) \<in> set \<Sigma>\<close> 
                list_deduction_weaken 
                list_deduction_modus_ponens 
          by blast
        ultimately have \<open>\<Gamma> $\<turnstile> (\<psi> # (remove1 \<psi> \<Psi>))\<close>
          using \<Delta>(1) by auto
        moreover from \<open>(\<phi>,\<psi>) \<in> set \<Sigma>\<close> \<Sigma>(1) have "\<psi> \<in> set \<Psi>"
          by force
        hence "mset \<Psi> \<subseteq># mset (\<psi> # (remove1 \<psi> \<Psi>))"
          by auto
        ultimately show ?thesis using segmented_msub_weaken by blast
      next
        case False
        hence "mset (map fst \<Sigma>) \<subseteq># mset \<Phi>"
          using \<Sigma>(2)
          by (simp, 
             metis add_mset_add_single 
                   diff_single_trivial 
                   mset_map set_mset_mset 
                   subset_eq_diff_conv)
        hence "\<Psi> \<preceq> \<Phi>"
          using \<Sigma>(1) \<Sigma>(3)
          unfolding stronger_theory_relation_def
          by auto
        moreover from \<open>\<Gamma> $\<turnstile> (\<phi> # \<Phi>)\<close> have "\<Gamma> $\<turnstile> \<Phi>"
          using segmented_deduction.simps(2) 
              segmented_stronger_theory_left_monotonic 
              witness_stronger_theory 
          by blast
        ultimately show ?thesis using Cons by blast
      qed
    }
    then show ?case by blast
  qed
  thus ?thesis using assms by blast
qed
  
lemma (in Classical_Propositional_Logic) segmented_witness_right_split:
  assumes "mset (map snd \<Psi>) \<subseteq># mset \<Phi>"
  shows "\<Gamma> $\<turnstile> \<Phi> = 
         \<Gamma> $\<turnstile> (map (uncurry (op \<squnion>)) \<Psi> @ map (uncurry (op \<rightarrow>)) \<Psi> @ \<Phi> \<ominus> (map snd \<Psi>))"
proof -
  have "\<forall> \<Gamma> \<Phi>. mset (map snd \<Psi>) \<subseteq># mset \<Phi> \<longrightarrow> 
      \<Gamma> $\<turnstile> \<Phi> = \<Gamma> $\<turnstile> (map (uncurry (op \<squnion>)) \<Psi> @ map (uncurry (op \<rightarrow>)) \<Psi> @ \<Phi> \<ominus> (map snd \<Psi>))"
  proof (induct \<Psi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<psi> \<Psi>)
    {
      fix \<Gamma> \<Phi>
      let ?\<chi> = "fst \<psi>"
      let ?\<phi> = "snd \<psi>"
      let ?\<Phi>' = "map (uncurry op \<squnion>) (\<psi> # \<Psi>) @
                 map (uncurry op \<rightarrow>) (\<psi> # \<Psi>) @
                 \<Phi> \<ominus> map snd (\<psi> # \<Psi>)"
      let ?\<Phi>\<^sub>0 = "map (uncurry op \<squnion>) \<Psi> @ 
                 map (uncurry op \<rightarrow>) \<Psi> @ 
                 (remove1 ?\<phi> \<Phi>) \<ominus> map snd \<Psi>"
      assume "mset (map snd (\<psi> # \<Psi>)) \<subseteq># mset \<Phi>"
      hence "mset (map snd \<Psi>) \<subseteq># mset (remove1 ?\<phi> \<Phi>)"
            "mset (?\<phi> # remove1 ?\<phi> \<Phi>) = mset \<Phi>"
        by (simp add: insert_subset_eq_iff)+
      hence "\<Gamma> $\<turnstile> \<Phi> = \<Gamma> $\<turnstile> (?\<phi> # remove1 ?\<phi> \<Phi>)"
            "\<forall> \<Gamma>. \<Gamma> $\<turnstile> (remove1 ?\<phi> \<Phi>) = \<Gamma> $\<turnstile> ?\<Phi>\<^sub>0"
         by (metis list.set_intros(1) segmented_cons_remove1 set_mset_mset,
             metis Cons.hyps)
      moreover
      have "(uncurry op \<squnion>) = (\<lambda> \<psi>. fst \<psi> \<squnion> snd \<psi>)"
           "(uncurry op \<rightarrow>) = (\<lambda> \<psi>. fst \<psi> \<rightarrow> snd \<psi>)"
        by fastforce+
      hence "mset ?\<Phi>' = mset (?\<chi> \<squnion> ?\<phi> # ?\<chi> \<rightarrow> ?\<phi> # ?\<Phi>\<^sub>0)"
        by fastforce
      hence "\<Gamma> $\<turnstile> ?\<Phi>' = \<Gamma> $\<turnstile> (?\<phi> # ?\<Phi>\<^sub>0)"
        by (smt segmented_formula_right_split 
                segmented_msub_weaken 
                subset_mset.dual_order.refl)       
      ultimately have "\<Gamma> $\<turnstile> \<Phi> = \<Gamma> $\<turnstile> ?\<Phi>'"
        by fastforce
    }
    then show ?case by blast
  qed
  with assms show ?thesis by blast
qed

primrec (in Classical_Propositional_Logic)
  submergeWitness :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list"
  where
    "submergeWitness \<Sigma> [] = map (\<lambda> \<sigma>. (\<bottom>, (uncurry op \<squnion>) \<sigma>)) \<Sigma>"
  | "submergeWitness \<Sigma> (\<delta> # \<Delta>) = 
       (case find (\<lambda> \<sigma>. (uncurry op \<rightarrow>) \<sigma> = snd \<delta>) \<Sigma> of 
             None \<Rightarrow> submergeWitness \<Sigma> \<Delta>
           | Some \<sigma> \<Rightarrow> (fst \<sigma>, (fst \<delta> \<sqinter> fst \<sigma>) \<squnion> snd \<sigma>) # (submergeWitness (remove1 \<sigma> \<Sigma>) \<Delta>))"
    
lemma (in Classical_Propositional_Logic) submergeWitness_stronger_theory_left:    
   "map (uncurry op \<squnion>) \<Sigma> \<preceq> map (uncurry op \<squnion>) (submergeWitness \<Sigma> \<Delta>)"
proof -
  have "\<forall> \<Sigma>. map (uncurry op \<squnion>) \<Sigma> \<preceq> map (uncurry op \<squnion>) (submergeWitness \<Sigma> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    {
      fix \<Sigma>
      {
        fix \<phi>
        have "\<turnstile> (\<bottom> \<squnion> \<phi>) \<rightarrow> \<phi>"
          unfolding disjunction_def
          using Ex_Falso_Quodlibet Modus_Ponens excluded_middle_elimination by blast
      }
      note tautology = this
      have "map (uncurry op \<squnion>) \<Sigma> \<preceq> map (uncurry op \<squnion>) (submergeWitness \<Sigma> [])"
        by (induct \<Sigma>, 
            simp, 
            simp add: stronger_theory_left_right_cons tautology) 
    }
    then show ?case by auto
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Sigma>
      have "map (uncurry op \<squnion>) \<Sigma> \<preceq> map (uncurry op \<squnion>) (submergeWitness \<Sigma> (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<sigma>. (uncurry op \<rightarrow>) \<sigma> = snd \<delta>) \<Sigma> = None")
        case True
        then show ?thesis using Cons by simp
      next
        case False
        from this obtain \<sigma> where  
          \<sigma>: "find (\<lambda>\<sigma>. uncurry op \<rightarrow> \<sigma> = snd \<delta>) \<Sigma> = Some \<sigma>"
             "uncurry op \<rightarrow> \<sigma> = snd \<delta>"
             "\<sigma> \<in> set \<Sigma>"
          using find_Some_predicate find_Some_set_membership
          by fastforce
        {
          fix \<alpha> \<beta> \<gamma>
          have "\<turnstile> (\<alpha> \<squnion> (\<gamma> \<sqinter> \<alpha>) \<squnion> \<beta>) \<rightarrow> (\<alpha> \<squnion> \<beta>)"
          proof -
            let ?\<phi> = "(\<^bold>\<langle>\<alpha>\<^bold>\<rangle> \<squnion> (\<^bold>\<langle>\<gamma>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<alpha>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>\<beta>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<alpha>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<beta>\<^bold>\<rangle>)"
            have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
            hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
            thus ?thesis by simp
          qed
        }
        note tautology = this
        let ?\<alpha> = "fst \<sigma>"
        let ?\<beta> = "snd \<sigma>"
        let ?\<gamma> = "fst \<delta>"
        have "(uncurry op \<squnion>) = (\<lambda> \<sigma>. fst \<sigma> \<squnion> snd \<sigma>)" by fastforce
        hence "(uncurry op \<squnion>) \<sigma> = ?\<alpha> \<squnion> ?\<beta>" by simp
        hence "\<turnstile> (?\<alpha> \<squnion> (?\<gamma> \<sqinter> ?\<alpha>) \<squnion> ?\<beta>) \<rightarrow> (uncurry op \<squnion>) \<sigma>" using tautology by simp
        moreover
        have "map (uncurry op \<squnion>) (remove1 \<sigma> \<Sigma>) 
             \<preceq> map (uncurry op \<squnion>) (submergeWitness (remove1 \<sigma> \<Sigma>) \<Delta>)" 
          using Cons by simp
        ultimately have 
          "map (uncurry op \<squnion>) (\<sigma> # (remove1 \<sigma> \<Sigma>))
           \<preceq> (?\<alpha> \<squnion> (?\<gamma> \<sqinter> ?\<alpha>) \<squnion> ?\<beta> # map (uncurry op \<squnion>) (submergeWitness (remove1 \<sigma> \<Sigma>) \<Delta>))"
          apply simp
          using stronger_theory_left_right_cons by blast
        moreover from \<sigma>(3) have "mset \<Sigma> = mset (\<sigma> # (remove1 \<sigma> \<Sigma>))"
          by simp
        hence "mset (map (uncurry op \<squnion>) \<Sigma>) = mset (map (uncurry op \<squnion>) (\<sigma> # (remove1 \<sigma> \<Sigma>)))"
          by (metis mset_map)
        hence "map (uncurry op \<squnion>) \<Sigma> \<preceq> map (uncurry op \<squnion>) (\<sigma> # (remove1 \<sigma> \<Sigma>))"
          by (simp add: msub_stronger_theory_intro)
        ultimately show ?thesis using \<sigma> 
          apply simp
          using stronger_theory_transitive by blast  
      qed
    }
    then show ?case by auto
  qed
  thus ?thesis by blast
qed

lemma (in Classical_Propositional_Logic) submergeWitness_msub:
  "mset (map snd (submergeWitness \<Sigma> \<Delta>)) \<subseteq># mset (map (uncurry op \<squnion>) (mergeWitness \<Sigma> \<Delta>))"
proof -
  have "\<forall> \<Sigma>. mset (map snd (submergeWitness \<Sigma> \<Delta>)) \<subseteq># 
             mset (map (uncurry op \<squnion>) (mergeWitness \<Sigma> \<Delta>))"
  proof (induct \<Delta>)
    case Nil
    {
      fix \<Sigma>
      have "mset (map snd (submergeWitness \<Sigma> [])) \<subseteq># 
            mset (map (uncurry op \<squnion>) (mergeWitness \<Sigma> []))"
        by (induct \<Sigma>, simp+)
    }
    then show ?case by blast
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Sigma>
      have "mset (map snd (submergeWitness \<Sigma> (\<delta> # \<Delta>))) \<subseteq># 
            mset (map (uncurry op \<squnion>) (mergeWitness \<Sigma> (\<delta> # \<Delta>)))"
        using Cons
        by (cases "find (\<lambda> \<sigma>. (uncurry op \<rightarrow>) \<sigma> = snd \<delta>) \<Sigma> = None", 
            simp, 
            meson diff_subset_eq_self 
                  insert_subset_eq_iff 
                  mset_subset_eq_add_mset_cancel 
                  subset_mset.dual_order.trans, 
            fastforce)
    }
    then show ?case by blast
  qed
  thus ?thesis by blast
qed
  
lemma (in Classical_Propositional_Logic) submergeWitness_stronger_theory_right:
   "map (uncurry op \<squnion>) \<Delta>
    \<preceq>  (  map (uncurry op \<rightarrow>) (submergeWitness \<Sigma> \<Delta>) 
         @ map (uncurry op \<squnion>) (mergeWitness \<Sigma> \<Delta>) 
           \<ominus> map snd (submergeWitness \<Sigma> \<Delta>))"
proof -
  have "\<forall> \<Sigma>. map (uncurry op \<squnion>) \<Delta> 
           \<preceq> (  map (uncurry op \<rightarrow>) (submergeWitness \<Sigma> \<Delta>) 
              @ map (uncurry op \<squnion>) (mergeWitness \<Sigma> \<Delta>) 
                \<ominus> map snd (submergeWitness \<Sigma> \<Delta>))"
  proof(induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Sigma>
      have "map (uncurry op \<squnion>) (\<delta> # \<Delta>) \<preceq>
           (  map (uncurry op \<rightarrow>) (submergeWitness \<Sigma> (\<delta> # \<Delta>)) 
            @ map (uncurry op \<squnion>) (mergeWitness \<Sigma> (\<delta> # \<Delta>)) 
               \<ominus> map snd (submergeWitness \<Sigma> (\<delta> # \<Delta>)))"
      proof (cases "find (\<lambda> \<sigma>. (uncurry op \<rightarrow>) \<sigma> = snd \<delta>) \<Sigma> = None")
        case True
        from Cons obtain \<Phi> where \<Phi>: 
          "map snd \<Phi> = map (uncurry op \<squnion>) \<Delta>"
          "mset (map fst \<Phi>) \<subseteq>#
             mset (map (uncurry op \<rightarrow>) (submergeWitness \<Sigma> \<Delta>) 
                   @ map (uncurry op \<squnion>) (mergeWitness \<Sigma> \<Delta>) \<ominus> map snd (submergeWitness \<Sigma> \<Delta>))"
          "\<forall>(\<gamma>, \<sigma>)\<in>set \<Phi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>" 
          unfolding stronger_theory_relation_def
          by fastforce
        let ?\<Phi>' = "((uncurry op \<squnion>) \<delta>, (uncurry op \<squnion>) \<delta>) # \<Phi>"
        have "map snd ?\<Phi>' = map (uncurry op \<squnion>) (\<delta> # \<Delta>)" using \<Phi>(1) by simp
        moreover have 
          "mset (map fst ?\<Phi>') \<subseteq>#
             mset (map (uncurry op \<rightarrow>) (submergeWitness \<Sigma> (\<delta> # \<Delta>)) 
                   @ map (uncurry op \<squnion>) (mergeWitness \<Sigma> (\<delta> # \<Delta>)) 
                      \<ominus> map snd (submergeWitness \<Sigma> (\<delta> # \<Delta>)))"
          using True \<Phi>(2)
          by (simp, 
              smt Multiset.diff_right_commute 
                  add_mset_add_single 
                  add_mset_remove_trivial 
                  submergeWitness_msub 
                  mset_map 
                  subset_eq_diff_conv 
                  subset_mset.diff_diff_right 
                  subset_mset.le_add_diff 
                  uncurry_def) 
        moreover have "\<forall>(\<gamma>, \<sigma>)\<in>set ?\<Phi>'. \<turnstile> \<gamma> \<rightarrow> \<sigma>"
          using \<Phi>(3) trivial_implication by auto
        ultimately show ?thesis
          unfolding stronger_theory_relation_def
          by blast
      next
        case False
        from this obtain \<sigma> where  
          \<sigma>: "find (\<lambda>\<sigma>. uncurry op \<rightarrow> \<sigma> = snd \<delta>) \<Sigma> = Some \<sigma>"
             "uncurry op \<rightarrow> \<sigma> = snd \<delta>"
          using find_Some_predicate
          by fastforce
        moreover from Cons have
          "map (uncurry op \<squnion>) \<Delta> \<preceq>
          (map (uncurry op \<rightarrow>) (submergeWitness (remove1 \<sigma> \<Sigma>) \<Delta>) @
            remove1 ((fst \<delta> \<sqinter> fst \<sigma>) \<squnion> snd \<sigma>)
             (((fst \<delta> \<sqinter> fst \<sigma>) \<squnion> snd \<sigma> # map (uncurry op \<squnion>) (mergeWitness (remove1 \<sigma> \<Sigma>) \<Delta>)) 
                \<ominus> map snd (submergeWitness (remove1 \<sigma> \<Sigma>) \<Delta>)))"
          unfolding stronger_theory_relation_alt_def
          by simp
        moreover
        {
          fix \<alpha> \<beta> \<gamma>
          have "\<turnstile> (\<alpha> \<rightarrow> ((\<gamma> \<sqinter> \<alpha>) \<squnion> \<beta>)) \<rightarrow> (\<gamma> \<squnion> (\<alpha> \<rightarrow> \<beta>))"
          proof -
            let ?\<phi> = "(\<^bold>\<langle>\<alpha>\<^bold>\<rangle> \<rightarrow> ((\<^bold>\<langle>\<gamma>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<alpha>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>\<beta>\<^bold>\<rangle>)) \<rightarrow> (\<^bold>\<langle>\<gamma>\<^bold>\<rangle> \<squnion> (\<^bold>\<langle>\<alpha>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<beta>\<^bold>\<rangle>))"
            have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
            hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
            thus ?thesis by simp
          qed
        }
        note tautology = this
        let ?\<alpha> = "fst \<sigma>"
        let ?\<beta> = "snd \<sigma>"
        let ?\<gamma> = "fst \<delta>"
        have "(\<lambda> \<delta>. uncurry op \<squnion> \<delta>) = (\<lambda> \<delta>. fst \<delta> \<squnion> snd \<delta>)"
             "(\<lambda> \<sigma>. uncurry op \<rightarrow> \<sigma>) = (\<lambda> \<sigma>. fst \<sigma> \<rightarrow> snd \<sigma>)" by fastforce+
        hence "(uncurry op \<squnion> \<delta>) = (?\<gamma> \<squnion> (?\<alpha> \<rightarrow> ?\<beta>))" using \<sigma>(2) by simp
        hence "\<turnstile> (?\<alpha> \<rightarrow> ((?\<gamma> \<sqinter> ?\<alpha>) \<squnion> ?\<beta>)) \<rightarrow> (uncurry op \<squnion> \<delta>)" using tautology by auto
        ultimately show ?thesis 
          apply simp
          using stronger_theory_left_right_cons 
          by blast 
      qed
    }
    then show ?case by auto
  qed
  thus ?thesis by simp
qed

lemma (in Classical_Propositional_Logic) mergeWitness_cons_segmented_deduction:
  assumes "map (uncurry (op \<squnion>)) \<Sigma> :\<turnstile> \<phi>"
      and "mset (map snd \<Delta>) \<subseteq># mset (map (uncurry op \<rightarrow>) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma>)"
      and "map (uncurry op \<squnion>) \<Delta> $\<turnstile> \<Phi>"
    shows "map (uncurry op \<squnion>) (mergeWitness \<Sigma> \<Delta>) $\<turnstile> (\<phi> # \<Phi>)"
proof -
  let ?\<Sigma>' = "submergeWitness \<Sigma> \<Delta>"
  let ?\<Gamma> = "map (uncurry op \<rightarrow>) ?\<Sigma>' @ map (uncurry op \<squnion>) (mergeWitness \<Sigma> \<Delta>) \<ominus> map snd ?\<Sigma>'"
  have "?\<Gamma> $\<turnstile> \<Phi>"
    using assms(3) 
          submergeWitness_stronger_theory_right
          segmented_stronger_theory_left_monotonic 
    by blast
  moreover have "map (uncurry (op \<squnion>)) ?\<Sigma>' :\<turnstile> \<phi>"
    using assms(1) 
          stronger_theory_deduction_monotonic 
          submergeWitness_stronger_theory_left
    by blast 
  ultimately show ?thesis
    using submergeWitness_msub
    by fastforce
qed

primrec (in Classical_Propositional_Logic)
  recoverWitnessA :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list"
  where
    "recoverWitnessA \<Sigma> [] = \<Sigma>"
  | "recoverWitnessA \<Sigma> (\<delta> # \<Delta>) = 
       (case find (\<lambda> \<sigma>. snd \<sigma> = (uncurry op \<squnion>) \<delta>) \<Sigma> of 
             None \<Rightarrow> recoverWitnessA \<Sigma> \<Delta>
           | Some \<sigma> \<Rightarrow> (fst \<sigma> \<squnion> fst \<delta>, snd \<delta>) # (recoverWitnessA (remove1 \<sigma> \<Sigma>) \<Delta>))"

primrec (in Classical_Propositional_Logic)
  recoverComplementA :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list"
  where
    "recoverComplementA \<Sigma> [] = []"
  | "recoverComplementA \<Sigma> (\<delta> # \<Delta>) = 
       (case find (\<lambda> \<sigma>. snd \<sigma> = (uncurry op \<squnion>) \<delta>) \<Sigma> of 
             None \<Rightarrow> \<delta> # recoverComplementA \<Sigma> \<Delta>
           | Some \<sigma> \<Rightarrow> (recoverComplementA (remove1 \<sigma> \<Sigma>) \<Delta>))"    
    
primrec (in Classical_Propositional_Logic)
  recoverWitnessB :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list"
  where
    "recoverWitnessB \<Sigma> [] = []"
  | "recoverWitnessB \<Sigma> (\<delta> # \<Delta>) = 
       (case find (\<lambda> \<sigma>. (snd \<sigma>) = (uncurry op \<squnion>) \<delta>) \<Sigma> of 
             None \<Rightarrow> \<delta> # recoverWitnessB \<Sigma> \<Delta>
           | Some \<sigma> \<Rightarrow> (fst \<delta>, (fst \<sigma> \<squnion> fst \<delta>) \<rightarrow> snd \<delta>) # (recoverWitnessB (remove1 \<sigma> \<Sigma>) \<Delta>))"
    
lemma (in Classical_Propositional_Logic) recoverWitnessA_left_stronger_theory:
  "map (uncurry op \<squnion>) \<Sigma> \<preceq> map (uncurry op \<squnion>) (recoverWitnessA \<Sigma> \<Delta>)"
proof -
  have "\<forall> \<Sigma>. map (uncurry op \<squnion>) \<Sigma> \<preceq> map (uncurry op \<squnion>) (recoverWitnessA \<Sigma> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    {
      fix \<Sigma>
      have "map (uncurry op \<squnion>) \<Sigma> \<preceq> map (uncurry op \<squnion>) (recoverWitnessA \<Sigma> [])"
        by(induct \<Sigma>, simp+)
    }
    then show ?case by auto
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Sigma>
      have "map (uncurry op \<squnion>) \<Sigma> \<preceq> map (uncurry op \<squnion>) (recoverWitnessA \<Sigma> (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<sigma>. snd \<sigma> = uncurry op \<squnion> \<delta>) \<Sigma> = None")
        case True
        then show ?thesis using Cons by simp
      next
        case False
        from this obtain \<sigma> where  
          \<sigma>: "find (\<lambda>\<sigma>. snd \<sigma> = uncurry op \<squnion> \<delta>) \<Sigma> = Some \<sigma>"
             "snd \<sigma> = uncurry op \<squnion> \<delta>"
             "\<sigma> \<in> set \<Sigma>"
          using find_Some_predicate 
                find_Some_set_membership
          by fastforce
        let ?\<alpha> = "fst \<sigma>"
        let ?\<beta> = "fst \<delta>"
        let ?\<gamma> = "snd \<delta>"
        have "uncurry op \<squnion> = (\<lambda>\<delta>. fst \<delta> \<squnion> snd \<delta>)" by fastforce
        hence "\<turnstile> ((?\<alpha> \<squnion> ?\<beta>) \<squnion> ?\<gamma>) \<rightarrow> uncurry op \<squnion> \<sigma>"
          using \<sigma>(2) biconditional_def disjunction_associativity 
          by auto 
        moreover
        have "map (uncurry op \<squnion>) (remove1 \<sigma> \<Sigma>)
            \<preceq> map (uncurry op \<squnion>) (recoverWitnessA (remove1 \<sigma> \<Sigma>) \<Delta>)"
          using Cons by simp
        ultimately have "map (uncurry op \<squnion>) (\<sigma> # (remove1 \<sigma> \<Sigma>)) 
                       \<preceq> map (uncurry op \<squnion>) (recoverWitnessA \<Sigma> (\<delta> # \<Delta>))"
          using \<sigma>(1)
          apply simp
          using stronger_theory_left_right_cons by blast
        moreover
        from \<sigma>(3) have "mset \<Sigma> = mset (\<sigma> # (remove1 \<sigma> \<Sigma>))"
          by simp
        hence "mset (map (uncurry op \<squnion>) \<Sigma>) = mset (map (uncurry op \<squnion>) (\<sigma> # (remove1 \<sigma> \<Sigma>)))"
          by (metis mset_map)
        hence "map (uncurry op \<squnion>) \<Sigma> \<preceq> map (uncurry op \<squnion>) (\<sigma> # (remove1 \<sigma> \<Sigma>))"
          by (simp add: msub_stronger_theory_intro)
        ultimately show ?thesis
          using stronger_theory_transitive by blast 
      qed
    }
    then show ?case by blast
  qed
  thus ?thesis by auto
qed

lemma (in Classical_Propositional_Logic) recoverWitnessA_mset_equiv:
  assumes "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry op \<squnion>) \<Delta>)"
  shows "mset (map snd (recoverWitnessA \<Sigma> \<Delta> @ recoverComplementA \<Sigma> \<Delta>)) = mset (map snd \<Delta>)"
proof -
  have "\<forall> \<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry op \<squnion>) \<Delta>)
         \<longrightarrow> mset (map snd (recoverWitnessA \<Sigma> \<Delta> @ recoverComplementA \<Sigma> \<Delta>)) = mset (map snd \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Sigma> :: "('a \<times> 'a) list"
      assume \<star>: "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry op \<squnion>) (\<delta> # \<Delta>))"
      have "mset (map snd (recoverWitnessA \<Sigma> (\<delta> # \<Delta>) @ recoverComplementA \<Sigma> (\<delta> # \<Delta>))) 
          = mset (map snd (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<sigma>. snd \<sigma> = uncurry op \<squnion> \<delta>) \<Sigma> = None")
        case True
        hence "uncurry op \<squnion> \<delta> \<notin> set (map snd \<Sigma>)"
        proof (induct \<Sigma>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<sigma> \<Sigma>)
          then show ?case
            by (cases "(uncurry op \<squnion>) \<delta> = snd \<sigma>", fastforce+)
        qed
        with \<star> have "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry op \<squnion>) \<Delta>)"
          by (smt diff_single_trivial 
                  in_multiset_in_set 
                  list.map(2) 
                  mset.simps(1) 
                  mset.simps(2) 
                  mset_eq_perm 
                  perm_append_single 
                  subset_eq_diff_conv union_code)
        then show ?thesis using Cons True by simp
      next
        case False
        from this obtain \<sigma> where  
          \<sigma>: "find (\<lambda>\<sigma>. snd \<sigma> = uncurry op \<squnion> \<delta>) \<Sigma> = Some \<sigma>"
             "snd \<sigma> = uncurry op \<squnion> \<delta>"
             "\<sigma> \<in> set \<Sigma>"
          using find_Some_predicate 
                find_Some_set_membership
          by fastforce
        with \<star> have "mset (map snd (remove1 \<sigma> \<Sigma>)) \<subseteq># mset (map (uncurry op \<squnion>) \<Delta>)"
          by (smt list.map(2) 
                  mset.simps(1) 
                  mset.simps(2)
                  prod.collapse
                  mset_append mset_eq_perm perm_append_single
                  remove1_pairs_list_projections_snd 
                  set_mset_mset subset_eq_diff_conv)
        with \<sigma>(1) Cons show ?thesis by simp
      qed
    }
    then show ?case by simp
  qed
  with assms show ?thesis by blast
qed

lemma (in Classical_Propositional_Logic) recoverWitnessB_stronger_theory:
  assumes "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry op \<squnion>) \<Delta>)"
  shows "(map (uncurry op \<rightarrow>) \<Sigma> @ map (uncurry op \<squnion>) \<Delta> \<ominus> map snd \<Sigma>) 
         \<preceq> map (uncurry op \<squnion>) (recoverWitnessB \<Sigma> \<Delta>)"
proof -
  have "\<forall> \<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry op \<squnion>) \<Delta>)
        \<longrightarrow> (map (uncurry op \<rightarrow>) \<Sigma> @ map (uncurry op \<squnion>) \<Delta> \<ominus> map snd \<Sigma>) 
            \<preceq> map (uncurry op \<squnion>) (recoverWitnessB \<Sigma> \<Delta>)"
  proof(induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Sigma> :: "('a \<times> 'a) list"
      assume \<star>: "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry op \<squnion>) (\<delta> # \<Delta>))"
      have "(map (uncurry op \<rightarrow>) \<Sigma> @ map (uncurry op \<squnion>) (\<delta> # \<Delta>) \<ominus> map snd \<Sigma>) 
            \<preceq> map (uncurry op \<squnion>) (recoverWitnessB \<Sigma> (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<sigma>. snd \<sigma> = uncurry op \<squnion> \<delta>) \<Sigma> = None")
        case True
        hence "uncurry op \<squnion> \<delta> \<notin> set (map snd \<Sigma>)"
        proof (induct \<Sigma>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<sigma> \<Sigma>)
          then show ?case
            by (cases "uncurry op \<squnion> \<delta> = snd \<sigma>", fastforce+)
        qed  
        hence "mset (map (uncurry op \<rightarrow>) \<Sigma> @ (map (uncurry op \<squnion>) (\<delta> # \<Delta>)) \<ominus> map snd \<Sigma>)
             = mset (uncurry op \<squnion> \<delta> # map (uncurry op \<rightarrow>) \<Sigma> 
                     @ map (uncurry op \<squnion>) \<Delta> \<ominus> map snd \<Sigma>)"
              "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry op \<squnion>) \<Delta>)"
          using \<star>
          by (simp, simp, 
              metis add_mset_add_single 
                    diff_single_trivial 
                    image_set 
                    mset_map 
                    set_mset_mset 
                    subset_eq_diff_conv)
        moreover from this have 
          "(map (uncurry op \<rightarrow>) \<Sigma> @ map (uncurry op \<squnion>) \<Delta> \<ominus> map snd \<Sigma>) 
           \<preceq> map (uncurry op \<squnion>) (recoverWitnessB \<Sigma> \<Delta>)"
          using Cons
          by auto
        hence "(uncurry op \<squnion> \<delta> # map (uncurry op \<rightarrow>) \<Sigma> @ map (uncurry op \<squnion>) \<Delta> \<ominus> map snd \<Sigma>) 
               \<preceq> map (uncurry op \<squnion>) (recoverWitnessB \<Sigma> (\<delta> # \<Delta>))"
          using True
          by (simp add: stronger_theory_left_right_cons trivial_implication)
        ultimately show ?thesis 
          unfolding stronger_theory_relation_alt_def 
          by simp
      next
        case False
        let ?\<Gamma> = "map (uncurry op \<rightarrow>) \<Sigma> @ (map (uncurry op \<squnion>) (\<delta> # \<Delta>)) \<ominus> map snd \<Sigma>"
        from False obtain \<sigma> where  
          \<sigma>: "find (\<lambda>\<sigma>. snd \<sigma> = uncurry op \<squnion> \<delta>) \<Sigma> = Some \<sigma>"
             "snd \<sigma> = uncurry op \<squnion> \<delta>"
             "\<sigma> \<in> set \<Sigma>"
          using find_Some_predicate 
                find_Some_set_membership
          by fastforce
        let ?\<Gamma>\<^sub>0 = "map (uncurry op \<rightarrow>) (remove1 \<sigma> \<Sigma>)
                    @ (map (uncurry op \<squnion>) \<Delta>) \<ominus> map snd (remove1 \<sigma> \<Sigma>)"
        let ?\<alpha> = "fst \<sigma>"
        let ?\<beta> = "fst \<delta>"
        let ?\<gamma> = "snd \<delta>"
        have "uncurry op \<squnion> = (\<lambda> \<sigma>. fst \<sigma> \<squnion> snd \<sigma>)"
             "uncurry op \<rightarrow> = (\<lambda> \<sigma>. fst \<sigma> \<rightarrow> snd \<sigma>)"
          by fastforce+
        hence "uncurry op \<rightarrow> \<sigma> = ?\<alpha> \<rightarrow> (?\<beta> \<squnion> ?\<gamma>)"
          using \<sigma>(2)
          by simp
        from \<sigma>(3) have "mset (\<sigma> # (remove1 \<sigma> \<Sigma>)) = mset \<Sigma>" by simp
        hence \<spadesuit>: "mset (map snd (\<sigma> # (remove1 \<sigma> \<Sigma>))) = mset (map snd \<Sigma>)"
                 "mset (map (uncurry op \<rightarrow>) (\<sigma> # (remove1 \<sigma> \<Sigma>))) = mset (map (uncurry op \<rightarrow>) \<Sigma>)"
          by (metis mset_map)+
        hence "mset ?\<Gamma> = mset (map (uncurry op \<rightarrow>) (\<sigma> # (remove1 \<sigma> \<Sigma>))
                                   @ (uncurry op \<squnion> \<delta> # map (uncurry op \<squnion>) \<Delta>)
                                        \<ominus> map snd (\<sigma> # (remove1 \<sigma> \<Sigma>)))"
          by simp
        hence "?\<Gamma> \<preceq> (?\<alpha> \<rightarrow> (?\<beta> \<squnion> ?\<gamma>) # ?\<Gamma>\<^sub>0)"
          using \<sigma>(2) \<open>uncurry op \<rightarrow> \<sigma> = ?\<alpha> \<rightarrow> (?\<beta> \<squnion> ?\<gamma>)\<close>
          by (simp add: msub_stronger_theory_intro)
        moreover have "mset (map snd (remove1 \<sigma> \<Sigma>)) \<subseteq># mset (map (uncurry op \<squnion>) \<Delta>)"
          using \<spadesuit>(1)
          by (simp,
              metis (no_types, lifting) 
                    \<star> \<sigma>(2)
                    list.simps(9)
                    mset.simps(2)
                    mset_map
                    uncurry_def
                    mset_subset_eq_add_mset_cancel)
        with Cons have \<heartsuit>: "?\<Gamma>\<^sub>0 \<preceq> map (uncurry op \<squnion>) (recoverWitnessB (remove1 \<sigma> \<Sigma>) \<Delta>)" by simp
        {
          fix \<alpha> \<beta> \<gamma>
          have "\<turnstile> (\<beta> \<squnion> (\<alpha> \<squnion> \<beta>) \<rightarrow> \<gamma>) \<rightarrow> (\<alpha> \<rightarrow> (\<beta> \<squnion> \<gamma>))"
          proof -
            let ?\<phi> = "(\<^bold>\<langle>\<beta>\<^bold>\<rangle> \<squnion> (\<^bold>\<langle>\<alpha>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<beta>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<alpha>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<beta>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>))"
            have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
            hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
            thus ?thesis by simp
          qed
        }
        hence "\<turnstile> (?\<beta> \<squnion> (?\<alpha> \<squnion> ?\<beta>) \<rightarrow> ?\<gamma>) \<rightarrow> (?\<alpha> \<rightarrow> (?\<beta> \<squnion> ?\<gamma>))"
          by simp
        hence "(?\<alpha> \<rightarrow> (?\<beta> \<squnion> ?\<gamma>) # ?\<Gamma>\<^sub>0) \<preceq> map (uncurry op \<squnion>) (recoverWitnessB \<Sigma> (\<delta> # \<Delta>))"
          using \<sigma>(1) \<heartsuit>
          apply simp
          using stronger_theory_left_right_cons 
          by blast
        ultimately show ?thesis
          using stronger_theory_transitive by blast 
      qed
    }
    then show ?case by simp
  qed
  thus ?thesis using assms by blast
qed

lemma (in Classical_Propositional_Logic) recoverWitnessB_mset_equiv:
  assumes "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry op \<squnion>) \<Delta>)"
  shows "mset (map snd (recoverWitnessB \<Sigma> \<Delta>)) 
       = mset (map (uncurry op \<rightarrow>) (recoverWitnessA \<Sigma> \<Delta>) 
               @ map snd \<Delta> \<ominus> map snd (recoverWitnessA \<Sigma> \<Delta>))"
proof -
  have "\<forall> \<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry op \<squnion>) \<Delta>)
       \<longrightarrow>   mset (map snd (recoverWitnessB \<Sigma> \<Delta>))  
           = mset (map (uncurry op \<rightarrow>) (recoverWitnessA \<Sigma> \<Delta>) @ map snd (recoverComplementA \<Sigma> \<Delta>))"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Sigma> :: "('a \<times> 'a) list"
      assume \<star>: "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry op \<squnion>) (\<delta> # \<Delta>))"
      have "mset (map snd (recoverWitnessB \<Sigma> (\<delta> # \<Delta>))) 
         =  mset (map (uncurry op \<rightarrow>) (recoverWitnessA \<Sigma> (\<delta> # \<Delta>)) @ 
                  map snd (recoverComplementA \<Sigma> (\<delta> # \<Delta>)))"
      proof (cases "find (\<lambda> \<sigma>. snd \<sigma> = uncurry op \<squnion> \<delta>) \<Sigma> = None")
        case True
        hence "uncurry op \<squnion> \<delta> \<notin> set (map snd \<Sigma>)"
        proof (induct \<Sigma>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<sigma> \<Sigma>)
          then show ?case
            by (cases "(uncurry op \<squnion>) \<delta> = snd \<sigma>", fastforce+)
        qed
        with \<star> have "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry op \<squnion>) \<Delta>)"
          by (smt diff_single_trivial 
                  in_multiset_in_set 
                  list.map(2) 
                  mset.simps(1) 
                  mset.simps(2) 
                  mset_eq_perm 
                  perm_append_single 
                  subset_eq_diff_conv union_code)
        then show ?thesis using True Cons by simp
      next
        case False
        from this obtain \<sigma> where  
          \<sigma>: "find (\<lambda>\<sigma>. snd \<sigma> = uncurry op \<squnion> \<delta>) \<Sigma> = Some \<sigma>"
             "snd \<sigma> = uncurry op \<squnion> \<delta>"
             "\<sigma> \<in> set \<Sigma>"
          using find_Some_predicate 
                find_Some_set_membership
          by fastforce
        with \<star> have "mset (map snd (remove1 \<sigma> \<Sigma>)) \<subseteq># mset (map (uncurry op \<squnion>) \<Delta>)"
          by (smt list.map(2) 
                  mset.simps(1) 
                  mset.simps(2)
                  prod.collapse
                  mset_append mset_eq_perm perm_append_single
                  remove1_pairs_list_projections_snd 
                  set_mset_mset subset_eq_diff_conv)
        with \<sigma>(1) Cons show ?thesis by simp
      qed
    }
    then show ?case by blast
  qed
  thus ?thesis 
    using assms recoverWitnessA_mset_equiv
    by (simp, metis add_diff_cancel_left')
qed
  
lemma (in Classical_Propositional_Logic) recoverWitnessB_right_stronger_theory:
  "map (uncurry op \<rightarrow>) \<Delta> \<preceq> map (uncurry op \<rightarrow>) (recoverWitnessB \<Sigma> \<Delta>)"
proof -
  have "\<forall> \<Sigma>. map (uncurry op \<rightarrow>) \<Delta> \<preceq> map (uncurry op \<rightarrow>) (recoverWitnessB \<Sigma> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Sigma>
      have "map (uncurry op \<rightarrow>) (\<delta> # \<Delta>) \<preceq> map (uncurry op \<rightarrow>) (recoverWitnessB \<Sigma> (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<sigma>. snd \<sigma> = uncurry op \<squnion> \<delta>) \<Sigma> = None")
        case True
        then show ?thesis 
          using Cons
          by (simp add: stronger_theory_left_right_cons trivial_implication) 
      next
        case False
        from this obtain \<sigma> where \<sigma>: 
          "find (\<lambda>\<sigma>. snd \<sigma> = uncurry op \<squnion> \<delta>) \<Sigma> = Some \<sigma>"
          by fastforce
        let ?\<alpha> = "fst \<delta>"
        let ?\<beta> = "snd \<delta>"
        let ?\<gamma> = "fst \<sigma>"
        have "uncurry op \<rightarrow> = (\<lambda>\<delta>. fst \<delta> \<rightarrow> snd \<delta>)" by fastforce
        hence "uncurry op \<rightarrow> \<delta> = ?\<alpha> \<rightarrow> ?\<beta>" by auto
        moreover have "\<turnstile> (?\<alpha> \<rightarrow> (?\<gamma> \<squnion> ?\<alpha>) \<rightarrow> ?\<beta>) \<rightarrow> ?\<alpha> \<rightarrow> ?\<beta>"
          unfolding disjunction_def
          using Axiom_1 Axiom_2 Modus_Ponens flip_implication 
          by blast
        ultimately show ?thesis 
          using Cons \<sigma> 
          by (simp add: stronger_theory_left_right_cons)
      qed
    }
    then show ?case by simp
  qed
  thus ?thesis by simp
qed

lemma (in Classical_Propositional_Logic) recoverWitnesses_mset_equiv:
  assumes "mset (map snd \<Delta>) \<subseteq># mset \<Gamma>"
      and "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry op \<squnion>) \<Delta>)"
    shows "mset (\<Gamma> \<ominus> map snd \<Delta>) =
           mset ((map (uncurry op \<rightarrow>) (recoverWitnessA \<Sigma> \<Delta>) 
                 @ \<Gamma> \<ominus> map snd (recoverWitnessA \<Sigma> \<Delta>)) \<ominus> map snd (recoverWitnessB \<Sigma> \<Delta>))"
proof -
  have "mset (\<Gamma> \<ominus> map snd \<Delta>) = 
        mset (\<Gamma> \<ominus> map snd (recoverComplementA \<Sigma> \<Delta>) \<ominus> map snd (recoverWitnessA \<Sigma> \<Delta>))"
    using assms(2) recoverWitnessA_mset_equiv
    by (simp add: union_commute)
  moreover have "\<forall> \<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry op \<squnion>) \<Delta>)
                  \<longrightarrow> mset (\<Gamma> \<ominus> map snd (recoverComplementA \<Sigma> \<Delta>)) = 
                      mset (map (uncurry op \<rightarrow>) (recoverWitnessA \<Sigma> \<Delta>) @ 
                            \<Gamma> \<ominus> map snd (recoverWitnessB \<Sigma> \<Delta>))"
    using assms(1)
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    from Cons.prems have "snd \<delta> \<in> set \<Gamma>"
      using mset_subset_eqD by fastforce
    from Cons.prems have \<heartsuit>: "mset (map snd \<Delta>) \<subseteq># mset \<Gamma>"
      using subset_mset.dual_order.trans
      by fastforce 
    {
      fix \<Sigma> :: "('a \<times> 'a) list"
      assume \<star>: "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry op \<squnion>) (\<delta> # \<Delta>))"
      have "mset (\<Gamma> \<ominus> map snd (recoverComplementA \<Sigma> (\<delta> # \<Delta>))) =
            mset (map (uncurry op \<rightarrow>) (recoverWitnessA \<Sigma> (\<delta> # \<Delta>)) @
                  \<Gamma> \<ominus> map snd (recoverWitnessB \<Sigma> (\<delta> # \<Delta>)))"
      proof (cases "find (\<lambda> \<sigma>. snd \<sigma> = uncurry op \<squnion> \<delta>) \<Sigma> = None")
        case True
        hence "uncurry op \<squnion> \<delta> \<notin> set (map snd \<Sigma>)"
        proof (induct \<Sigma>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<sigma> \<Sigma>)
          then show ?case
            by (cases "(uncurry op \<squnion>) \<delta> = snd \<sigma>", fastforce+)
        qed
        with \<star> have "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry op \<squnion>) \<Delta>)"
          by (smt diff_single_trivial 
                  in_multiset_in_set 
                  list.map(2) 
                  mset.simps(1) 
                  mset.simps(2) 
                  mset_eq_perm 
                  perm_append_single 
                  subset_eq_diff_conv union_code)
        with Cons.hyps \<heartsuit> have "mset (\<Gamma> \<ominus> map snd (recoverComplementA \<Sigma> \<Delta>)) = 
                               mset (map (uncurry op \<rightarrow>) (recoverWitnessA \<Sigma> \<Delta>) @
                                     \<Gamma> \<ominus> map snd (recoverWitnessB \<Sigma> \<Delta>))"
          by simp
        with True \<open>snd \<delta> \<in> set \<Gamma>\<close> show ?thesis apply simp 
      next
        case False
        then show ?thesis sorry
      qed
    }
    then show ?case sorry
  qed
    
  ultimately 
  show ?thesis 
    using assms recoverWitnessA_mset_equiv
    by (simp, 
        smt Multiset.diff_add diff_union_cancelL 
            listSubtract_mset_homomorphism 
            recoverWitnessB_mset_equiv 
            mset_append mset_map uncurry_def)
qed
  
lemma (in Classical_Propositional_Logic) segmented_deduction_generalized_witness:
  "\<Gamma> $\<turnstile> (\<Phi> @ \<Psi>) = (\<exists> \<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset \<Gamma> \<and> 
                         map (uncurry (op \<squnion>)) \<Sigma> $\<turnstile> \<Phi> \<and> 
                         (map (uncurry (op \<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> (map snd \<Sigma>)) $\<turnstile> \<Psi>)"
proof -
  have "\<forall> \<Gamma> \<Psi>. \<Gamma> $\<turnstile> (\<Phi> @ \<Psi>) = (\<exists> \<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset \<Gamma> \<and> 
                                      map (uncurry (op \<squnion>)) \<Sigma> $\<turnstile> \<Phi> \<and> 
                                     (map (uncurry (op \<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> (map snd \<Sigma>)) $\<turnstile> \<Psi>)"
  proof (induct \<Phi>)
    case Nil
    {
      fix \<Gamma> \<Psi>
      have "\<Gamma> $\<turnstile> ([] @ \<Psi>) = (\<exists>\<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset \<Gamma> \<and> 
                                  map (uncurry op \<squnion>) \<Sigma> $\<turnstile> [] \<and> 
                                  map (uncurry op \<rightarrow>) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> $\<turnstile> \<Psi>)"
      proof (rule iffI)
        assume "\<Gamma> $\<turnstile> ([] @ \<Psi>)"
        moreover
        have "\<Gamma> $\<turnstile> ([] @ \<Psi>) = (mset (map snd []) \<subseteq># mset \<Gamma> \<and> 
                                map (uncurry (op \<squnion>)) [] $\<turnstile> [] \<and> 
                                map (uncurry (op \<rightarrow>)) [] @ \<Gamma> \<ominus> (map snd []) $\<turnstile> \<Psi>)"
          by simp
        ultimately show "\<exists>\<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset \<Gamma> \<and> 
                              map (uncurry op \<squnion>) \<Sigma> $\<turnstile> [] \<and> 
                              map (uncurry op \<rightarrow>) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> $\<turnstile> \<Psi>"
          by smt
      next
        assume "\<exists>\<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset \<Gamma> \<and> 
                    map (uncurry op \<squnion>) \<Sigma> $\<turnstile> [] \<and> 
                    map (uncurry op \<rightarrow>) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> $\<turnstile> \<Psi>"
        from this obtain \<Sigma> where
          \<Sigma>: "mset (map snd \<Sigma>) \<subseteq># mset \<Gamma>"
             "map (uncurry op \<rightarrow>) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> $\<turnstile> ([] @ \<Psi>)"
          by fastforce
        hence "(map (uncurry op \<rightarrow>) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma>) \<preceq> \<Gamma>"
          using witness_stronger_theory by auto
        with \<Sigma>(2) show "\<Gamma> $\<turnstile> ([] @ \<Psi>)"
          using segmented_stronger_theory_left_monotonic by blast 
      qed
    }
    then show ?case by blast
  next
    case (Cons \<phi> \<Phi>)
    {
      fix \<Gamma> \<Psi>
      have "\<Gamma> $\<turnstile> ((\<phi> # \<Phi>) @ \<Psi>) = (\<exists>\<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset \<Gamma> \<and> 
                                       map (uncurry op \<squnion>) \<Sigma> $\<turnstile> (\<phi> # \<Phi>) \<and> 
                                       map (uncurry op \<rightarrow>) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> $\<turnstile> \<Psi>)"
      proof (rule iffI)
        assume "\<Gamma> $\<turnstile> ((\<phi> # \<Phi>) @ \<Psi>)"
        from this obtain \<Sigma> where 
          \<Sigma>: "mset (map snd \<Sigma>) \<subseteq># mset \<Gamma>"
             "map (uncurry (op \<squnion>)) \<Sigma> :\<turnstile> \<phi>"
             "map (uncurry (op \<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> (map snd \<Sigma>) $\<turnstile> (\<Phi> @ \<Psi>)"
             (is "?\<Gamma>\<^sub>0 $\<turnstile> (\<Phi> @ \<Psi>)")
          by auto
        from this(3) obtain \<Delta> where
          \<Delta>: "mset (map snd \<Delta>) \<subseteq># mset ?\<Gamma>\<^sub>0"
             "map (uncurry (op \<squnion>)) \<Delta> $\<turnstile> \<Phi>"
             "map (uncurry (op \<rightarrow>)) \<Delta> @ ?\<Gamma>\<^sub>0 \<ominus> (map snd \<Delta>) $\<turnstile> \<Psi>"
          using Cons
          by auto
        let ?\<Sigma>' = "mergeWitness \<Sigma> \<Delta>"
        have "map (uncurry (op \<squnion>)) ?\<Sigma>' $\<turnstile> (\<phi> # \<Phi>)"
          using \<Delta>(1) \<Delta>(2) \<Sigma>(2) mergeWitness_cons_segmented_deduction by blast
        moreover have "mset (map snd ?\<Sigma>') \<subseteq># mset \<Gamma>"
          using \<Delta>(1) \<Sigma>(1) mergeWitness_msub_intro by blast
        moreover have "map (uncurry op \<rightarrow>) ?\<Sigma>' @ \<Gamma> \<ominus> map snd ?\<Sigma>' $\<turnstile> \<Psi>"
          using \<Delta>(1) \<Delta>(3) mergeWitness_segmented_deduction_intro by blast
        ultimately show 
          "\<exists>\<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset \<Gamma> \<and> 
               map (uncurry op \<squnion>) \<Sigma> $\<turnstile> (\<phi> # \<Phi>) \<and> 
               map (uncurry op \<rightarrow>) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> $\<turnstile> \<Psi>"
          by fast
      next
        assume "\<exists>\<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset \<Gamma> \<and> 
                    map (uncurry op \<squnion>) \<Sigma> $\<turnstile> (\<phi> # \<Phi>) \<and> 
                    map (uncurry op \<rightarrow>) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> $\<turnstile> \<Psi>"
        from this obtain \<Delta> where \<Delta>:
          "mset (map snd \<Delta>) \<subseteq># mset \<Gamma>"
          "map (uncurry op \<squnion>) \<Delta> $\<turnstile> (\<phi> # \<Phi>)"
          "map (uncurry op \<rightarrow>) \<Delta> @ \<Gamma> \<ominus> map snd \<Delta> $\<turnstile> \<Psi>"
          by auto
        from this obtain \<Sigma> where \<Sigma>:
          "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry op \<squnion>) \<Delta>)"
          "map (uncurry op \<squnion>) \<Sigma> :\<turnstile> \<phi>"
          "map (uncurry op \<rightarrow>) \<Sigma> @ (map (uncurry op \<squnion>) \<Delta>) \<ominus> map snd \<Sigma> $\<turnstile> \<Phi>"
          by auto
        let ?\<Omega> = "recoverWitnessA \<Sigma> \<Delta>"
        let ?\<Xi> = "recoverWitnessB \<Sigma> \<Delta>"
        let ?\<Gamma>\<^sub>0 = "map (uncurry op \<rightarrow>) ?\<Omega> @ \<Gamma> \<ominus> map snd ?\<Omega>"
        let ?\<Gamma>\<^sub>1 = "map (uncurry op \<rightarrow>) ?\<Xi> @ ?\<Gamma>\<^sub>0 \<ominus> map snd ?\<Xi>"
        have "mset (\<Gamma> \<ominus> map snd \<Delta>) = mset (?\<Gamma>\<^sub>0 \<ominus> map snd ?\<Xi>)"
          using \<Delta>(1) \<Sigma>(1) recoverWitnesses_mset_equiv by blast
        hence "(\<Gamma> \<ominus> map snd \<Delta>) \<preceq> (?\<Gamma>\<^sub>0 \<ominus> map snd ?\<Xi>)"
          by (simp add: msub_stronger_theory_intro)
        hence "?\<Gamma>\<^sub>1 $\<turnstile> \<Psi>"
          using \<Delta>(3) segmented_stronger_theory_left_monotonic
                stronger_theory_combine 
                recoverWitnessB_right_stronger_theory 
          by blast 
        moreover
        have "mset (map snd ?\<Xi>) \<subseteq># mset ?\<Gamma>\<^sub>0" 
          using \<Sigma>(1) \<Delta>(1) recoverWitnessB_mset_equiv
          by (simp, 
              metis listSubtract_monotonic 
                    listSubtract_mset_homomorphism 
                    mset_map)
        moreover
        have "map (uncurry op \<squnion>) ?\<Xi> $\<turnstile> \<Phi>"
          using \<Sigma>(1) recoverWitnessB_stronger_theory 
                \<Sigma>(3) segmented_stronger_theory_left_monotonic by blast 
        ultimately have "?\<Gamma>\<^sub>0 $\<turnstile> (\<Phi> @ \<Psi>)"
          using Cons by fast
        moreover
        have "mset (map snd ?\<Omega>) \<subseteq># mset (map snd \<Delta>)"
          using \<Sigma>(1) recoverWitnessA_mset_equiv
          by (simp, metis mset_subset_eq_add_left) 
        hence "mset (map snd ?\<Omega>) \<subseteq># mset \<Gamma>" using \<Delta>(1) by simp
        moreover 
        have "map (uncurry op \<squnion>) ?\<Omega> :\<turnstile> \<phi>"
          using \<Sigma>(2)
                recoverWitnessA_left_stronger_theory
                stronger_theory_deduction_monotonic 
          by blast 
        ultimately show "\<Gamma> $\<turnstile> ((\<phi> # \<Phi>) @ \<Psi>)"
          by (simp, blast)
      qed
    }
    then show ?case by smt
  qed
  thus ?thesis by blast
qed

lemma (in Classical_Propositional_Logic) segmented_list_deduction_antitonic:
  assumes "\<Gamma> $\<turnstile> \<Psi>"
      and "\<Psi> :\<turnstile> \<phi>"
    shows "\<Gamma> :\<turnstile> \<phi>"
proof -
  have "\<forall> \<Gamma> \<phi>. \<Gamma> $\<turnstile> \<Psi> \<longrightarrow> \<Psi> :\<turnstile> \<phi> \<longrightarrow> \<Gamma> :\<turnstile> \<phi>"
  proof (induct \<Psi>)
    case Nil
    then show ?case 
      using list_deduction_weaken 
      by simp
  next
    case (Cons \<psi> \<Psi>)
    {
      fix \<Gamma> \<phi>
      assume "\<Gamma> $\<turnstile> (\<psi> # \<Psi>)"
         and "\<psi> # \<Psi> :\<turnstile> \<phi>"
      hence "\<Psi> :\<turnstile> \<psi> \<rightarrow> \<phi>"
        using list_deduction_theorem by blast
      from \<open>\<Gamma> $\<turnstile> (\<psi> # \<Psi>)\<close> obtain \<Sigma> where \<Sigma>:
        "mset (map snd \<Sigma>) \<subseteq># mset \<Gamma>"
        "map (uncurry op \<squnion>) \<Sigma> :\<turnstile> \<psi>"
        "map (uncurry op \<rightarrow>) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> $\<turnstile> \<Psi>"
        by auto
      hence "\<Gamma> :\<turnstile> \<psi> \<rightarrow> \<phi>"
        using segmented_stronger_theory_left_monotonic 
              witness_stronger_theory
              \<open>\<Psi> :\<turnstile> \<psi> \<rightarrow> \<phi>\<close>
              Cons
        by blast
      moreover
      have "\<Gamma> :\<turnstile> \<psi>"
        using \<Sigma>(1) \<Sigma>(2)
              stronger_theory_deduction_monotonic 
              witness_weaker_theory 
        by blast 
      ultimately have "\<Gamma> :\<turnstile> \<phi>" using list_deduction_modus_ponens by auto
    }
    then show ?case by simp
  qed
  thus ?thesis using assms by auto
qed
  
lemma (in Classical_Propositional_Logic) segmented_transitive:
  assumes "\<Gamma> $\<turnstile> \<Lambda>"
      and "\<Lambda> $\<turnstile> \<Delta>"
    shows "\<Gamma> $\<turnstile> \<Delta>"
proof -
  have "\<forall> \<Gamma> \<Lambda>. \<Gamma> $\<turnstile> \<Lambda> \<longrightarrow> \<Lambda> $\<turnstile> \<Delta> \<longrightarrow> \<Gamma> $\<turnstile> \<Delta>"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Gamma> \<Lambda>
      assume "\<Lambda> $\<turnstile> (\<delta> # \<Delta>)"
      from this obtain \<Sigma> where \<Sigma>:
          "mset (map snd \<Sigma>) \<subseteq># mset \<Lambda>"
          "map (uncurry op \<squnion>) \<Sigma> :\<turnstile> \<delta>"
          "map (uncurry op \<rightarrow>) \<Sigma> @ \<Lambda> \<ominus> map snd \<Sigma> $\<turnstile> \<Delta>"
          by auto
      assume "\<Gamma> $\<turnstile> \<Lambda>"
      hence "\<Gamma> $\<turnstile> (map (uncurry op \<squnion>) \<Sigma> @ map (uncurry op \<rightarrow>) \<Sigma> @ \<Lambda> \<ominus> (map snd \<Sigma>))"
        using \<Sigma>(1) segmented_witness_right_split 
        by simp
      from this obtain \<Psi> where \<Psi>:
        "mset (map snd \<Psi>) \<subseteq># mset \<Gamma>"
        "map (uncurry op \<squnion>) \<Psi> $\<turnstile> map (uncurry op \<squnion>) \<Sigma>"
        "map (uncurry op \<rightarrow>) \<Psi> @ \<Gamma> \<ominus> map snd \<Psi> $\<turnstile> (map (uncurry op \<rightarrow>) \<Sigma> @ \<Lambda> \<ominus> map snd \<Sigma>)"
        using segmented_deduction_generalized_witness
        by fastforce
      have "map (uncurry op \<rightarrow>) \<Psi> @ \<Gamma> \<ominus> map snd \<Psi> $\<turnstile> \<Delta>"
        using \<Sigma>(3) \<Psi>(3) Cons
        by auto
      moreover
      have "map (uncurry op \<squnion>) \<Psi> :\<turnstile> \<delta>"
        using \<Psi>(2) \<Sigma>(2) segmented_list_deduction_antitonic 
        by blast 
      ultimately have "\<Gamma> $\<turnstile> (\<delta> # \<Delta>)"
        using \<Psi>(1)
        by fastforce
    }
    then show ?case by auto
  qed
  with assms show ?thesis by simp
qed

lemma (in Classical_Propositional_Logic) segmented_formula_left_split:
  "\<phi> # \<Gamma> $\<turnstile> \<Phi> = \<psi> \<squnion> \<phi> # \<psi> \<rightarrow> \<phi> # \<Gamma> $\<turnstile> \<Phi>"
proof (rule iffI)
  assume "\<phi> # \<Gamma> $\<turnstile> \<Phi>"
  have "\<psi> \<squnion> \<phi> # \<psi> \<rightarrow> \<phi> # \<Gamma> $\<turnstile> (\<psi> \<squnion> \<phi> # \<psi> \<rightarrow> \<phi> # \<Gamma>)"
    using segmented_stronger_theory_intro 
          stronger_theory_reflexive 
    by blast
  hence "\<psi> \<squnion> \<phi> # \<psi> \<rightarrow> \<phi> # \<Gamma> $\<turnstile> (\<phi> # \<Gamma>)"
    using segmented_formula_right_split by blast
  with \<open>\<phi> # \<Gamma> $\<turnstile> \<Phi>\<close> show "\<psi> \<squnion> \<phi> # \<psi> \<rightarrow> \<phi> # \<Gamma> $\<turnstile> \<Phi>"
    using segmented_transitive by blast
next
  assume "\<psi> \<squnion> \<phi> # \<psi> \<rightarrow> \<phi> # \<Gamma> $\<turnstile> \<Phi>"
  have "\<phi> # \<Gamma> $\<turnstile> (\<phi> # \<Gamma>)"
    using segmented_stronger_theory_intro 
          stronger_theory_reflexive 
    by blast
  hence "\<phi> # \<Gamma> $\<turnstile> (\<psi> \<squnion> \<phi> # \<psi> \<rightarrow> \<phi> # \<Gamma>)"
    using segmented_formula_right_split by blast
  with \<open>\<psi> \<squnion> \<phi> # \<psi> \<rightarrow> \<phi> # \<Gamma> $\<turnstile> \<Phi>\<close> show "\<phi> # \<Gamma> $\<turnstile> \<Phi>"
    using segmented_transitive by blast
qed
  
lemma (in Classical_Propositional_Logic) segmented_biconditional_cancel:
  assumes "\<turnstile> \<gamma> \<leftrightarrow> \<phi>"
  shows "\<Gamma> $\<turnstile> \<Phi> = (\<gamma> # \<Gamma>) $\<turnstile> (\<phi> # \<Phi>)"
  sorry
    
  
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