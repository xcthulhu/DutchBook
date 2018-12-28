theory Logical_Probability_Completeness
  imports "Logical_Probability"
begin

sledgehammer_params [smt_proofs = false]

(* TODO: Move utility stuff *)

definition uncurry :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c"
  where uncurry_def [simp]: "uncurry f = (\<lambda> (x, y). f x y)"

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

lemma (in Classical_Propositional_Logic) conjunction_monotonic_identity:
  "\<turnstile> (\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<phi> \<sqinter> \<chi>) \<rightarrow> (\<psi> \<sqinter> \<chi>)"
  unfolding conjunction_def
  using Modus_Ponens
        flip_hypothetical_syllogism
  by blast

lemma (in Classical_Propositional_Logic) conjunction_monotonic:
  assumes "\<turnstile> \<phi> \<rightarrow> \<psi>"
  shows "\<turnstile> (\<phi> \<sqinter> \<chi>) \<rightarrow> (\<psi> \<sqinter> \<chi>)"
  using assms
        Modus_Ponens
        conjunction_monotonic_identity
  by blast

lemma (in Classical_Propositional_Logic) disjunction_monotonic_identity:
  "\<turnstile> (\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<phi> \<squnion> \<chi>) \<rightarrow> (\<psi> \<squnion> \<chi>)"
  unfolding disjunction_def
  using Modus_Ponens
        flip_hypothetical_syllogism
  by blast

lemma (in Classical_Propositional_Logic) disjunction_monotonic:
  assumes "\<turnstile> \<phi> \<rightarrow> \<psi>"
  shows "\<turnstile> (\<phi> \<squnion> \<chi>) \<rightarrow> (\<psi> \<squnion> \<chi>)"
  using assms
        Modus_Ponens
        disjunction_monotonic_identity
  by blast

lemma (in Classical_Propositional_Logic) conj_dnf_distribute:
  "\<turnstile> \<Squnion> (map (\<Sqinter> \<circ> (\<lambda> \<phi>s. \<phi> # \<phi>s)) \<Lambda>) \<leftrightarrow> (\<phi> \<sqinter> \<Squnion> (map \<Sqinter> \<Lambda>))"
proof(induct \<Lambda>)
  case Nil
  have "\<turnstile> \<bottom> \<leftrightarrow> (\<phi> \<sqinter> \<bottom>)"
  proof -
    let ?\<phi> = "\<bottom> \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<bottom>)"
    have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
    hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis by simp
  qed
  then show ?case by simp
next
  case (Cons \<Psi> \<Lambda>)
  assume "\<turnstile> \<Squnion> (map (\<Sqinter> \<circ> (\<lambda> \<phi>s. \<phi> # \<phi>s)) \<Lambda>) \<leftrightarrow> (\<phi> \<sqinter> \<Squnion> (map \<Sqinter> \<Lambda>))"
    (is "\<turnstile> ?A \<leftrightarrow> (\<phi> \<sqinter> ?B)")
  moreover
  have "\<turnstile> (?A \<leftrightarrow> (\<phi> \<sqinter> ?B)) \<rightarrow> (((\<phi> \<sqinter> \<Sqinter> \<Psi>) \<squnion> ?A) \<leftrightarrow> (\<phi> \<sqinter> \<Sqinter> \<Psi> \<squnion> ?B))"
  proof -
    let ?\<phi> = "(\<^bold>\<langle>?A\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>?B\<^bold>\<rangle>)) \<rightarrow> (((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> \<Psi>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>?A\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> \<Psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>?B\<^bold>\<rangle>))"
    have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
    hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis
      by simp
  qed
  ultimately have "\<turnstile> ((\<phi> \<sqinter> \<Sqinter> \<Psi>) \<squnion> ?A) \<leftrightarrow> (\<phi> \<sqinter> \<Sqinter> \<Psi> \<squnion> ?B)"
    using Modus_Ponens
    by blast
  moreover
  have "map (\<Sqinter> \<circ> (\<lambda> \<phi>s. \<phi> # \<phi>s)) \<Lambda> = map (\<lambda>\<Psi>. \<phi> \<sqinter> \<Sqinter> \<Psi>) \<Lambda>" by simp
  ultimately show ?case by simp
qed

lemma (in Classical_Propositional_Logic) append_dnf_distribute:
  "\<turnstile> \<Squnion> (map (\<Sqinter> \<circ> (\<lambda> \<Psi>. \<Phi> @ \<Psi>)) \<Lambda>) \<leftrightarrow> (\<Sqinter> \<Phi> \<sqinter> \<Squnion> (map \<Sqinter> \<Lambda>))"
proof(induct \<Phi>)
  case Nil
  have "\<turnstile> \<Squnion> (map \<Sqinter> \<Lambda>) \<leftrightarrow> (\<top> \<sqinter> \<Squnion> (map \<Sqinter> \<Lambda>))"
    (is "\<turnstile> ?A \<leftrightarrow> (\<top> \<sqinter> ?A)")
  proof -
    let ?\<phi> = "\<^bold>\<langle>?A\<^bold>\<rangle> \<leftrightarrow> ((\<bottom> \<rightarrow> \<bottom>) \<sqinter> \<^bold>\<langle>?A\<^bold>\<rangle>)"
    have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by simp
    hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis
      unfolding verum_def
      by simp
  qed
  then show ?case by simp
next
  case (Cons \<phi> \<Phi>)
  have "\<turnstile> \<Squnion> (map (\<Sqinter> \<circ> (@) \<Phi>) \<Lambda>) \<leftrightarrow> (\<Sqinter> \<Phi> \<sqinter> \<Squnion> (map \<Sqinter> \<Lambda>))
       = \<turnstile> \<Squnion> (map \<Sqinter> (map ((@) \<Phi>) \<Lambda>)) \<leftrightarrow> (\<Sqinter> \<Phi> \<sqinter> \<Squnion> (map \<Sqinter> \<Lambda>))"
    by simp
  with Cons have "\<turnstile> \<Squnion> (map \<Sqinter> (map (\<lambda> \<Psi>. \<Phi> @ \<Psi>) \<Lambda>)) \<leftrightarrow> (\<Sqinter> \<Phi> \<sqinter> \<Squnion> (map \<Sqinter> \<Lambda>))"
    (is "\<turnstile> \<Squnion> (map \<Sqinter> ?A) \<leftrightarrow> (?B \<sqinter> ?C)")
    by meson
  moreover have "\<turnstile> \<Squnion> (map \<Sqinter> ?A) \<leftrightarrow> (?B \<sqinter> ?C)
                \<rightarrow> (\<Squnion> (map (\<Sqinter> \<circ> (\<lambda> \<phi>s. \<phi> # \<phi>s)) ?A) \<leftrightarrow> (\<phi> \<sqinter> \<Squnion> (map \<Sqinter> ?A)))
                \<rightarrow> \<Squnion> (map (\<Sqinter> \<circ> (\<lambda> \<phi>s. \<phi> # \<phi>s)) ?A) \<leftrightarrow> ((\<phi> \<sqinter> ?B) \<sqinter> ?C)"
  proof -
    let ?\<phi> = "\<^bold>\<langle>\<Squnion> (map \<Sqinter> ?A)\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>?B\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>?C\<^bold>\<rangle>)
           \<rightarrow> (\<^bold>\<langle>\<Squnion> (map (\<Sqinter> \<circ> (\<lambda> \<phi>s. \<phi> # \<phi>s)) ?A)\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> (map \<Sqinter> ?A)\<^bold>\<rangle>))
           \<rightarrow> \<^bold>\<langle>\<Squnion> (map (\<Sqinter> \<circ> (\<lambda> \<phi>s. \<phi> # \<phi>s)) ?A)\<^bold>\<rangle> \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>?B\<^bold>\<rangle>) \<sqinter> \<^bold>\<langle>?C\<^bold>\<rangle>)"
    have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by simp
    hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis
      by simp
  qed
  ultimately have "\<turnstile> \<Squnion> (map (\<Sqinter> \<circ> (\<lambda> \<phi>s. \<phi> # \<phi>s)) ?A) \<leftrightarrow> ((\<phi> \<sqinter> ?B) \<sqinter> ?C)"
    using Modus_Ponens conj_dnf_distribute
    by blast
  moreover
  have "\<Sqinter> \<circ> (@) (\<phi> # \<Phi>) = \<Sqinter> \<circ> (#) \<phi> \<circ> (@) \<Phi>" by auto
  hence
    "\<turnstile> \<Squnion> (map (\<Sqinter> \<circ> (@) (\<phi> # \<Phi>)) \<Lambda>) \<leftrightarrow> (\<Sqinter> (\<phi> # \<Phi>) \<sqinter> ?C)
   = \<turnstile> \<Squnion> (map (\<Sqinter> \<circ> (#) \<phi>) ?A) \<leftrightarrow> ((\<phi> \<sqinter> ?B) \<sqinter> ?C)"
    by simp
  ultimately show ?case by meson
qed

(***************************************)

primrec (in Classical_Propositional_Logic)
  segmented_deduction :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" ("_ $\<turnstile> _" [60,100] 60)
  where
    "\<Gamma> $\<turnstile> [] = True"
  | "\<Gamma> $\<turnstile> (\<phi> # \<Phi>) = (\<exists> \<Psi>. mset (map snd \<Psi>) \<subseteq># mset \<Gamma> \<and>
                           map (uncurry (\<squnion>)) \<Psi> :\<turnstile> \<phi> \<and>
                           map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>) $\<turnstile> \<Phi>)"

definition (in Minimal_Logic)
  stronger_theory_relation :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infix "\<preceq>" 100)
  where
    "\<Sigma> \<preceq> \<Gamma> = (\<exists> \<Phi>. map snd \<Phi> = \<Sigma> \<and>
                    mset (map fst \<Phi>) \<subseteq># mset \<Gamma> \<and>
                    (\<forall> (\<gamma>,\<sigma>) \<in> set \<Phi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>))"

abbreviation (in Minimal_Logic)
  stronger_theory_relation_op :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infix "\<succeq>" 100)
  where
    "\<Gamma> \<succeq> \<Sigma> \<equiv> \<Sigma> \<preceq> \<Gamma>"

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
  assumes "\<Gamma> <~~> \<Delta>"
      and "\<Sigma> \<preceq> \<Gamma>"
    shows "\<Sigma> \<preceq> \<Delta>"
proof -
  from assms(1) have "mset \<Gamma> = mset \<Delta>"
    by (simp add: mset_eq_perm)
  thus ?thesis
    using assms(2) stronger_theory_relation_def
    by fastforce
qed

lemma (in Minimal_Logic) stronger_theory_left_permutation:
  assumes "\<Sigma> <~~> \<Delta>"
      and "\<Sigma> \<preceq> \<Gamma>"
    shows "\<Delta> \<preceq> \<Gamma>"
proof -
  have "\<forall> \<Sigma> \<Gamma>. \<Sigma> <~~> \<Delta> \<longrightarrow> \<Sigma> \<preceq> \<Gamma> \<longrightarrow> \<Delta> \<preceq> \<Gamma>"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Sigma> \<Gamma>
      assume "\<Sigma> <~~> (\<delta> # \<Delta>)" "\<Sigma> \<preceq> \<Gamma>"
      from this obtain \<Phi> where \<Phi>:
        "map snd \<Phi> = \<Sigma>"
        "mset (map fst \<Phi>) \<subseteq># mset \<Gamma>"
        "\<forall> (\<gamma>,\<delta>) \<in> set \<Phi>. \<turnstile> \<gamma> \<rightarrow> \<delta>"
        using stronger_theory_relation_def by fastforce
      with \<open>\<Sigma> <~~> (\<delta> # \<Delta>)\<close> have "\<delta> \<in># mset (map snd \<Phi>)"
        by (simp add: perm_set_eq)
      from this obtain \<gamma> where \<gamma>: "(\<gamma>, \<delta>) \<in># mset \<Phi>"
        by (induct \<Phi>, fastforce+)
      let ?\<Phi>\<^sub>0 = "remove1 (\<gamma>, \<delta>) \<Phi>"
      let ?\<Sigma>\<^sub>0 = "map snd ?\<Phi>\<^sub>0"
      from \<gamma> \<Phi>(2) have "mset (map fst ?\<Phi>\<^sub>0) \<subseteq># mset (remove1 \<gamma> \<Gamma>)"
        by (metis ex_mset
                  listSubtract_monotonic
                  listSubtract_mset_homomorphism
                  mset_remove1
                  remove1_pairs_list_projections_fst)
      moreover have "mset ?\<Phi>\<^sub>0 \<subseteq># mset \<Phi>" by simp
      with \<Phi>(3) have "\<forall> (\<gamma>,\<delta>) \<in> set ?\<Phi>\<^sub>0. \<turnstile> \<gamma> \<rightarrow> \<delta>" by fastforce
      ultimately have "?\<Sigma>\<^sub>0 \<preceq> remove1 \<gamma> \<Gamma>"
        unfolding stronger_theory_relation_def by blast
      moreover have "\<Delta> <~~> (remove1 \<delta> \<Sigma>)" using \<open>\<Sigma> <~~> (\<delta> # \<Delta>)\<close>
        by (metis perm_remove_perm perm_sym remove_hd)
      moreover from \<gamma> \<Phi>(1) have "mset ?\<Sigma>\<^sub>0 = mset (remove1 \<delta> \<Sigma>)"
        using remove1_pairs_list_projections_snd
        by fastforce
      hence "?\<Sigma>\<^sub>0 <~~> remove1 \<delta> \<Sigma>"
        using mset_eq_perm by blast
      ultimately have "\<Delta> \<preceq> remove1 \<gamma> \<Gamma>" using Cons
        by (meson perm.trans perm_sym)
      from this obtain \<Psi>\<^sub>0 where \<Psi>\<^sub>0:
        "map snd \<Psi>\<^sub>0 = \<Delta>"
        "mset (map fst \<Psi>\<^sub>0) \<subseteq># mset (remove1 \<gamma> \<Gamma>)"
        "\<forall> (\<gamma>,\<delta>) \<in> set \<Psi>\<^sub>0. \<turnstile> \<gamma> \<rightarrow> \<delta>"
        using stronger_theory_relation_def by fastforce
      let ?\<Psi> = "(\<gamma>, \<delta>) # \<Psi>\<^sub>0"
      have "map snd ?\<Psi> = (\<delta> # \<Delta>)"
        by (simp add: \<Psi>\<^sub>0(1))
      moreover have "mset (map fst ?\<Psi>) \<subseteq># mset (\<gamma> # (remove1 \<gamma> \<Gamma>))"
        using \<Psi>\<^sub>0(2) by auto
      moreover from \<gamma> \<Phi>(3) \<Psi>\<^sub>0(3) have "\<forall> (\<gamma>,\<sigma>) \<in> set ?\<Psi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>" by auto
      ultimately have "(\<delta> # \<Delta>) \<preceq> (\<gamma> # (remove1 \<gamma> \<Gamma>))"
        unfolding stronger_theory_relation_def by metis
      moreover from \<gamma> \<Phi>(2) have "\<gamma> \<in># mset \<Gamma>"
        using mset_subset_eqD by fastforce
      hence "(\<gamma> # (remove1 \<gamma> \<Gamma>)) <~~> \<Gamma>"
        by (simp add: perm_remove perm_sym)
      ultimately have "(\<delta> # \<Delta>) \<preceq> \<Gamma>"
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
        using stronger_theory_relation_def by (simp, metis)
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
        using stronger_theory_relation_def by (simp, metis)
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
        using stronger_theory_relation_def by (simp, metis)
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
        by metis
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
    unfolding stronger_theory_relation_def by metis
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
    using stronger_theory_relation_def by (simp, metis)
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
    by metis
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
          by metis
      next
        assume "\<exists>\<Phi>. mset (map snd \<Phi>) = mset \<Sigma> \<and>
                    mset (map fst \<Phi>) \<subseteq># mset (\<gamma> # \<Gamma>) \<and>
                    (\<forall>(\<gamma>, \<sigma>)\<in>set \<Phi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>)"
        from this obtain \<Phi> where \<Phi>:
          "mset (map snd \<Phi>) = mset \<Sigma>"
          "mset (map fst \<Phi>) \<subseteq># mset (\<gamma> # \<Gamma>)"
          "\<forall>(\<gamma>, \<sigma>)\<in>set \<Phi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>"
          by metis
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
            by metis
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
        by (blast, metis)
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
        "map (uncurry (\<squnion>)) \<Psi> :\<turnstile> \<phi>"
        "map (uncurry (\<rightarrow>)) \<Psi> @ \<Sigma> \<ominus> (map snd \<Psi>) $\<turnstile> \<Phi>"
        using segmented_deduction.simps(2) by blast
      let ?\<Psi> = "map snd \<Psi>"
      let ?\<Psi>' = "map (uncurry (\<rightarrow>)) \<Psi>"
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
  assumes "\<Gamma> \<succeq> \<Sigma>"
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
      moreover have "mset (remove1 \<gamma> \<Gamma>) \<subseteq># mset (map (uncurry (\<rightarrow>)) ?\<Phi> @ \<Gamma> \<ominus> (map snd ?\<Phi>))"
        by simp
      ultimately have "map (uncurry (\<rightarrow>)) ?\<Phi> @ \<Gamma> \<ominus> (map snd ?\<Phi>) $\<turnstile> \<Sigma>"
        using segmented_msub_left_monotonic by blast
      moreover have "map (uncurry (\<squnion>)) ?\<Phi> :\<turnstile> \<sigma>"
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

lemma (in Classical_Propositional_Logic) witness_weaker_theory:
  assumes "mset (map snd \<Sigma>) \<subseteq># mset \<Gamma>"
  shows "map (uncurry (\<squnion>)) \<Sigma> \<preceq> \<Gamma>"
proof -
  have "\<forall> \<Gamma>. mset (map snd \<Sigma>) \<subseteq># mset \<Gamma> \<longrightarrow> map (uncurry (\<squnion>)) \<Sigma> \<preceq> \<Gamma>"
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
      with Cons have "map (uncurry (\<squnion>)) \<Sigma> \<preceq> remove1 (snd \<sigma>) \<Gamma>" by blast
      moreover have "uncurry (\<squnion>) = (\<lambda> \<sigma>. fst \<sigma> \<squnion> snd \<sigma>)" by fastforce
      hence "uncurry (\<squnion>) \<sigma> = fst \<sigma> \<squnion> snd \<sigma>" by simp
      moreover have "\<turnstile> snd \<sigma> \<rightarrow> (fst \<sigma> \<squnion> snd \<sigma>)"
        unfolding disjunction_def
        by (simp add: Axiom_1)
      ultimately have "map (uncurry (\<squnion>)) (\<sigma> # \<Sigma>) \<preceq> (snd \<sigma> # (remove1 (snd \<sigma>) \<Gamma>))"
        by (simp add: stronger_theory_left_right_cons)
      moreover have "mset (snd \<sigma> # (remove1 (snd \<sigma>) \<Gamma>)) = mset \<Gamma>"
        using \<open>mset (map snd (\<sigma> # \<Sigma>)) \<subseteq># mset \<Gamma>\<close>
        by (simp, meson insert_DiffM mset_subset_eq_insertD)
      ultimately have "map (uncurry (\<squnion>)) (\<sigma> # \<Sigma>) \<preceq> \<Gamma>"
        unfolding stronger_theory_relation_alt_def
        by simp
    }
    then show ?case by blast
  qed
  with assms show ?thesis by simp
qed

lemma (in Classical_Propositional_Logic) segmented_deduction_one_collapse:
  "\<Gamma> $\<turnstile> [\<phi>] = \<Gamma> :\<turnstile> \<phi>"
proof (rule iffI)
  assume "\<Gamma> $\<turnstile> [\<phi>]"
  from this obtain \<Sigma> where
    \<Sigma>: "mset (map snd \<Sigma>) \<subseteq># mset \<Gamma>"
       "map (uncurry (\<squnion>)) \<Sigma> :\<turnstile> \<phi>"
    by auto
  hence "map (uncurry (\<squnion>)) \<Sigma> \<preceq> \<Gamma>"
    using witness_weaker_theory by blast
  thus "\<Gamma> :\<turnstile> \<phi>" using \<Sigma>(2)
    using stronger_theory_deduction_monotonic by blast
next
  assume "\<Gamma> :\<turnstile> \<phi>"
  let ?\<Sigma> = "map (\<lambda> \<gamma>. (\<bottom>, \<gamma>)) \<Gamma>"
  have "\<Gamma> \<preceq> map (uncurry (\<squnion>)) ?\<Sigma>"
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
  hence "map (uncurry (\<squnion>)) ?\<Sigma> :\<turnstile> \<phi>"
    using \<open>\<Gamma> :\<turnstile> \<phi>\<close> stronger_theory_deduction_monotonic by blast
  moreover have "mset (map snd ?\<Sigma>) \<subseteq># mset \<Gamma>" by (induct \<Gamma>, simp+)
  ultimately show "\<Gamma> $\<turnstile> [\<phi>]"
    using segmented_deduction.simps(1)
          segmented_deduction.simps(2)
    by blast
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
              "mset \<Delta> + add_mset \<delta> (mset []) = mset (\<delta> # \<Delta>)"
          by auto
        hence "mset (map fst \<Sigma>) \<subseteq># mset \<Delta>"
          by (metis (no_types) \<open>mset (map fst \<Sigma>) \<subseteq># mset (\<delta> # \<Delta>)\<close>
                               diff_single_trivial
                               mset.simps(1)
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

lemma (in Classical_Propositional_Logic) segmented_empty_deduction:
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
           "map (uncurry (\<squnion>)) \<Psi> :\<turnstile> \<phi>"
           "map (uncurry (\<rightarrow>)) \<Psi> @ \<Sigma> \<ominus> (map snd \<Psi>) $\<turnstile> \<Phi>"
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
        by metis
      moreover have "map (uncurry (\<squnion>)) \<Psi> \<preceq> map (uncurry (\<squnion>)) ?\<Theta>"
      proof -
        let ?\<Phi> = "map (\<lambda> (\<psi>, \<sigma>, \<gamma>). (\<psi> \<squnion> \<gamma>, \<psi> \<squnion> \<sigma>)) \<Omega>"
        have "map snd ?\<Phi> = map (uncurry (\<squnion>)) \<Psi>"
          using \<Omega>(1) by fastforce
        moreover have "map fst ?\<Phi> = map (uncurry (\<squnion>)) ?\<Theta>"
          by fastforce
        hence "mset (map fst ?\<Phi>) \<subseteq># mset (map (uncurry (\<squnion>)) ?\<Theta>)"
          by (metis subset_mset.dual_order.refl)
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
          hence "(\<lambda>(_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>)) \<omega> = (?\<gamma>, ?\<sigma>)" by metis
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
          hence "(\<lambda>(\<psi>, \<sigma>, \<gamma>). (\<psi> \<squnion> \<gamma>, \<psi> \<squnion> \<sigma>)) \<omega> = ((?\<psi> \<squnion> ?\<gamma>), (?\<psi> \<squnion> ?\<sigma>))" by metis
          ultimately show ?case by simp
        qed
        ultimately show ?thesis
          unfolding stronger_theory_relation_def
          by blast
      qed
      with \<Psi>(2) have "map (uncurry (\<squnion>)) ?\<Theta> :\<turnstile> \<phi>"
        by (metis stronger_theory_deduction_monotonic)
      moreover have
        "(map (uncurry (\<rightarrow>)) \<Psi> @ \<Sigma> \<ominus> (map snd \<Psi>)) \<preceq>
         (map (uncurry (\<rightarrow>)) ?\<Theta> @ \<Gamma> \<ominus> (map snd ?\<Theta>))"
      proof -
        have "map (uncurry (\<rightarrow>)) \<Psi> \<preceq> map (uncurry (\<rightarrow>)) ?\<Theta>"
        proof -
          let ?\<Phi> = "map (\<lambda> (\<psi>, \<sigma>, \<gamma>). (\<psi> \<rightarrow> \<gamma>, \<psi> \<rightarrow> \<sigma>)) \<Omega>"
          have "map snd ?\<Phi> = map (uncurry (\<rightarrow>)) \<Psi>"
            using \<Omega>(1) by fastforce
          moreover have "map fst ?\<Phi> = map (uncurry (\<rightarrow>)) ?\<Theta>"
            by fastforce
          hence "mset (map fst ?\<Phi>) \<subseteq># mset (map (uncurry (\<rightarrow>)) ?\<Theta>)"
            by (metis subset_mset.dual_order.refl)
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
            hence "(\<lambda>(_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>)) \<omega> = (?\<gamma>, ?\<sigma>)" by metis
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
            hence "(\<lambda>(\<psi>, \<sigma>, \<gamma>). (\<psi> \<rightarrow> \<gamma>, \<psi> \<rightarrow> \<sigma>)) \<omega> = ((?\<psi> \<rightarrow> ?\<gamma>), (?\<psi> \<rightarrow> ?\<sigma>))" by metis
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
            by (metis \<Omega>(2)
                      \<open>map snd (map (\<lambda>(\<psi>, _, \<gamma>). (\<psi>, \<gamma>)) \<Omega>) =
                      map fst (map (\<lambda>(_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>)) \<Omega>)\<close>
                      listSubtract_monotonic
                      map_listSubtract_mset_equivalence)
          moreover
          from \<Omega>(2) have "mset ?\<Delta> \<subseteq># mset \<Delta>" by simp
          hence "\<forall> (\<gamma>,\<sigma>) \<in> set ?\<Delta>. \<turnstile> \<gamma> \<rightarrow> \<sigma>"
            using \<Delta>(3)
            by (metis mset_subset_eqD set_mset_mset)
          moreover
          have "map snd (map (\<lambda>(_, \<sigma>, \<gamma>). (\<gamma>, \<sigma>)) \<Omega>) = map snd \<Psi>"
            using \<Omega>(1)
            by (induct \<Omega>, simp, fastforce)
          hence "mset (map snd ?\<Delta>) = mset (\<Sigma> \<ominus> (map snd \<Psi>))"
            by (metis \<Delta>(1) \<Omega>(2) map_listSubtract_mset_equivalence)
          ultimately show ?thesis
            by (metis stronger_theory_relation_alt_def)
        qed
        ultimately show ?thesis using stronger_theory_combine by blast
      qed
      hence "map (uncurry (\<rightarrow>)) ?\<Theta> @ \<Gamma> \<ominus> (map snd ?\<Theta>) $\<turnstile> \<Phi>"
        using \<Psi>(3) Cons by blast
      ultimately have "\<Gamma> $\<turnstile> (\<phi> # \<Phi>)"
        by (metis segmented_deduction.simps(2))
    }
    then show ?case by blast
  qed
  with assms show ?thesis by blast
qed

lemma (in Classical_Propositional_Logic) negated_segmented_deduction:
  "\<^bold>\<sim> \<Gamma> $\<turnstile> (\<phi> # \<Phi>) = (\<exists> \<Psi>. mset (map fst \<Psi>) \<subseteq># mset \<Gamma> \<and>
                        \<^bold>\<sim> (map (uncurry (\<setminus>)) \<Psi>) :\<turnstile> \<phi> \<and>
                        \<^bold>\<sim> (map (uncurry (\<sqinter>)) \<Psi> @ \<Gamma> \<ominus> (map fst \<Psi>)) $\<turnstile> \<Phi>)"
proof (rule iffI)
  assume "\<^bold>\<sim> \<Gamma> $\<turnstile> (\<phi> # \<Phi>)"
  from this obtain \<Psi> where \<Psi>:
    "mset (map snd \<Psi>) \<subseteq># mset (\<^bold>\<sim> \<Gamma>)"
    "map (uncurry (\<squnion>)) \<Psi> :\<turnstile> \<phi>"
    "map (uncurry (\<rightarrow>)) \<Psi> @ \<^bold>\<sim> \<Gamma> \<ominus> map snd \<Psi> $\<turnstile> \<Phi>"
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
                      map (uncurry (\<squnion>)) \<Psi> \<preceq> \<^bold>\<sim> (map (uncurry (\<setminus>)) (zip \<Delta> (map fst \<Psi>)))"
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
        "map (uncurry (\<squnion>)) \<Psi> \<preceq> \<^bold>\<sim> (map (uncurry (\<setminus>)) (zip (tl \<Delta>) (map fst \<Psi>)))"
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
      have "uncurry (\<squnion>) = (\<lambda> \<psi>. (fst \<psi>) \<squnion> (snd \<psi>))"
        by fastforce
      with \<gamma> have "uncurry (\<squnion>) \<psi> = ?\<psi> \<squnion> \<sim> \<gamma>"
        by simp
      with tautology have "\<turnstile> \<sim>(\<gamma> \<setminus> ?\<psi>) \<rightarrow> uncurry (\<squnion>) \<psi>"
        by simp
      ultimately have "map (uncurry (\<squnion>)) (\<psi> # \<Psi>) \<preceq>
                       \<^bold>\<sim> (map (uncurry (\<setminus>)) ((zip ((hd \<Delta>) # (tl \<Delta>)) (map fst (\<psi> # \<Psi>)))))"
        using stronger_theory_left_right_cons \<gamma>(2)
        by simp
      hence "map (uncurry (\<squnion>)) (\<psi> # \<Psi>) \<preceq>
            \<^bold>\<sim> (map (uncurry (\<setminus>)) (zip \<Delta> (map fst (\<psi> # \<Psi>))))"
        using \<open>map snd (\<psi> # \<Psi>) = \<^bold>\<sim> \<Delta>\<close> by force
    }
    thus ?case by blast
  qed
  with \<Psi>(2) \<Delta>(2) have "\<^bold>\<sim> (map (uncurry (\<setminus>)) ?\<Psi>) :\<turnstile> \<phi>"
    using stronger_theory_deduction_monotonic by blast
  moreover
  have "(map (uncurry (\<rightarrow>)) \<Psi> @ \<^bold>\<sim> \<Gamma> \<ominus> map snd \<Psi>) \<preceq>
        \<^bold>\<sim> (map (uncurry (\<sqinter>)) ?\<Psi> @ \<Gamma> \<ominus> (map fst ?\<Psi>))"
  proof -
    from \<Delta>(1) have "mset (\<^bold>\<sim> \<Gamma> \<ominus> \<^bold>\<sim> \<Delta>) = mset (\<^bold>\<sim> (\<Gamma> \<ominus> \<Delta>))"
      by (simp add: image_mset_Diff)
    hence "mset (\<^bold>\<sim> \<Gamma> \<ominus> map snd \<Psi>) = mset (\<^bold>\<sim> (\<Gamma> \<ominus> map fst ?\<Psi>))"
      using \<Psi>(1) \<Delta>(2) \<open>map fst ?\<Psi> = \<Delta>\<close> by simp
    hence "(\<^bold>\<sim> \<Gamma> \<ominus> map snd \<Psi>) \<preceq> \<^bold>\<sim> (\<Gamma> \<ominus> map fst ?\<Psi>)"
      by (simp add: msub_stronger_theory_intro)
    moreover have "\<forall> \<Delta>. map snd \<Psi> = \<^bold>\<sim> \<Delta> \<longrightarrow>
                         map (uncurry (\<rightarrow>)) \<Psi> \<preceq> \<^bold>\<sim> (map (uncurry (\<sqinter>)) (zip \<Delta> (map fst \<Psi>)))"
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
          "map (uncurry (\<rightarrow>)) \<Psi> \<preceq> \<^bold>\<sim> (map (uncurry (\<sqinter>)) (zip (tl \<Delta>) (map fst \<Psi>)))"
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
        have "(uncurry (\<rightarrow>)) = (\<lambda> \<psi>. (fst \<psi>) \<rightarrow> (snd \<psi>))"
          by fastforce
        with \<gamma> have "uncurry (\<rightarrow>) \<psi> = ?\<psi> \<rightarrow> \<sim> \<gamma>"
          by simp
        with tautology have "\<turnstile> \<sim>(\<gamma> \<sqinter> ?\<psi>) \<rightarrow> (uncurry (\<rightarrow>)) \<psi>"
          by simp
        ultimately have "map (uncurry (\<rightarrow>)) (\<psi> # \<Psi>) \<preceq>
                         \<^bold>\<sim> (map (uncurry (\<sqinter>)) ((zip ((hd \<Delta>) # (tl \<Delta>)) (map fst (\<psi> # \<Psi>)))))"
          using stronger_theory_left_right_cons \<gamma>(2)
          by simp
        hence "map (uncurry (\<rightarrow>)) (\<psi> # \<Psi>) \<preceq>
              \<^bold>\<sim> (map (uncurry (\<sqinter>)) (zip \<Delta> (map fst (\<psi> # \<Psi>))))"
          using \<open>map snd (\<psi> # \<Psi>) = \<^bold>\<sim> \<Delta>\<close> by force
      }
      then show ?case by blast
    qed
    ultimately have "(map (uncurry (\<rightarrow>)) \<Psi> @ \<^bold>\<sim> \<Gamma> \<ominus> map snd \<Psi>) \<preceq>
                     (\<^bold>\<sim> (map (uncurry (\<sqinter>)) ?\<Psi>) @ \<^bold>\<sim> (\<Gamma> \<ominus> (map fst ?\<Psi>)))"
      using stronger_theory_combine \<Delta>(2)
      by metis
    thus ?thesis by simp
  qed
  hence "\<^bold>\<sim> (map (uncurry (\<sqinter>)) ?\<Psi> @ \<Gamma> \<ominus> (map fst ?\<Psi>)) $\<turnstile> \<Phi>"
    using \<Psi>(3) segmented_stronger_theory_left_monotonic
    by blast
  ultimately show "\<exists>\<Psi>. mset (map fst \<Psi>) \<subseteq># mset \<Gamma> \<and>
                        \<^bold>\<sim> (map (uncurry (\<setminus>)) \<Psi>) :\<turnstile> \<phi> \<and>
                        \<^bold>\<sim> (map (uncurry (\<sqinter>)) \<Psi> @ \<Gamma> \<ominus> (map fst \<Psi>)) $\<turnstile> \<Phi>"
    by metis
next
  assume "\<exists>\<Psi>. mset (map fst \<Psi>) \<subseteq># mset \<Gamma> \<and>
               \<^bold>\<sim> (map (uncurry (\<setminus>)) \<Psi>) :\<turnstile> \<phi> \<and>
               \<^bold>\<sim> (map (uncurry (\<sqinter>)) \<Psi> @ \<Gamma> \<ominus> map fst \<Psi>) $\<turnstile> \<Phi>"
  from this obtain \<Psi> where \<Psi>:
    "mset (map fst \<Psi>) \<subseteq># mset \<Gamma>"
    "\<^bold>\<sim> (map (uncurry (\<setminus>)) \<Psi>) :\<turnstile> \<phi>"
    "\<^bold>\<sim> (map (uncurry (\<sqinter>)) \<Psi> @ \<Gamma> \<ominus> map fst \<Psi>) $\<turnstile> \<Phi>"
    by auto
  let ?\<Psi> = "zip (map snd \<Psi>) (\<^bold>\<sim> (map fst \<Psi>))"
  from \<Psi>(1) have "mset (map snd ?\<Psi>) \<subseteq># mset (\<^bold>\<sim> \<Gamma>)"
    by (simp, metis image_mset_subseteq_mono multiset.map_comp)
  moreover have "\<^bold>\<sim> (map (uncurry (\<setminus>)) \<Psi>) \<preceq> map (uncurry (\<squnion>)) ?\<Psi>"
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
    have "\<sim> \<circ> uncurry (\<setminus>) = (\<lambda> \<psi>. \<sim> ((fst \<psi>) \<setminus> (snd \<psi>)))"
         "uncurry (\<squnion>) = (\<lambda> (\<psi>,\<gamma>). \<psi> \<squnion> \<gamma>)"
      by fastforce+
    with tautology have "\<turnstile> uncurry (\<squnion>) (?\<psi>, \<sim> ?\<gamma>) \<rightarrow> (\<sim> \<circ> uncurry (\<setminus>)) \<psi>"
      by fastforce
    with Cons.hyps have
      "((\<sim> \<circ> uncurry (\<setminus>)) \<psi> # \<^bold>\<sim> (map (uncurry (\<setminus>)) \<Psi>)) \<preceq>
       (uncurry (\<squnion>) (?\<psi>, \<sim> ?\<gamma>) # map (uncurry (\<squnion>)) (zip (map snd \<Psi>) (\<^bold>\<sim> (map fst \<Psi>))))"
      using stronger_theory_left_right_cons by blast
    thus ?case by simp
  qed
  with \<Psi>(2) have "map (uncurry (\<squnion>)) ?\<Psi> :\<turnstile> \<phi>"
    using stronger_theory_deduction_monotonic by blast
  moreover have "\<^bold>\<sim> (map (uncurry (\<sqinter>)) \<Psi> @ \<Gamma> \<ominus> map fst \<Psi>) \<preceq>
                 (map (uncurry (\<rightarrow>)) ?\<Psi> @ \<^bold>\<sim> \<Gamma> \<ominus> map snd ?\<Psi>)"
  proof -
    have "\<^bold>\<sim> (map (uncurry (\<sqinter>)) \<Psi>) \<preceq> map (uncurry (\<rightarrow>)) ?\<Psi>"
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
      have "\<sim> \<circ> uncurry (\<sqinter>) = (\<lambda> \<psi>. \<sim> ((fst \<psi>) \<sqinter> (snd \<psi>)))"
           "uncurry (\<rightarrow>) = (\<lambda> (\<psi>,\<gamma>). \<psi> \<rightarrow> \<gamma>)"
        by fastforce+
      with tautology have "\<turnstile> uncurry (\<rightarrow>) (?\<psi>, \<sim> ?\<gamma>) \<rightarrow> (\<sim> \<circ> uncurry (\<sqinter>)) \<psi>"
        by fastforce
      with Cons.hyps have
        "((\<sim> \<circ> uncurry (\<sqinter>)) \<psi> # \<^bold>\<sim> (map (uncurry (\<sqinter>)) \<Psi>)) \<preceq>
         (uncurry (\<rightarrow>) (?\<psi>, \<sim> ?\<gamma>) # map (uncurry (\<rightarrow>)) (zip (map snd \<Psi>) (\<^bold>\<sim> (map fst \<Psi>))))"
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
  hence "map (uncurry (\<rightarrow>)) ?\<Psi> @ \<^bold>\<sim> \<Gamma> \<ominus> map snd ?\<Psi> $\<turnstile> \<Phi>"
    using \<Psi>(3) segmented_stronger_theory_left_monotonic by blast
  ultimately show "\<^bold>\<sim> \<Gamma> $\<turnstile> (\<phi> # \<Phi>)"
    using segmented_deduction.simps(2) by blast
qed

lemma (in Logical_Probability) segmented_deduction_summation_introduction:
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
        "\<^bold>\<sim> (map (uncurry (\<setminus>)) \<Psi>) :\<turnstile> \<sim> \<phi>"
        "\<^bold>\<sim> (map (uncurry (\<sqinter>)) \<Psi> @ \<Gamma> \<ominus> (map fst \<Psi>)) $\<turnstile> \<^bold>\<sim> \<Phi>"
        using negated_segmented_deduction by blast
      let ?\<Gamma> = "\<Gamma> \<ominus> (map fst \<Psi>)"
      let ?\<Psi>\<^sub>1 = "map (uncurry (\<setminus>)) \<Psi>"
      let ?\<Psi>\<^sub>2 = "map (uncurry (\<sqinter>)) \<Psi>"
      have "(\<Sum>\<phi>'\<leftarrow>\<Phi>. Pr \<phi>') \<le> (\<Sum>\<phi>\<leftarrow>(?\<Psi>\<^sub>2 @ ?\<Gamma>). Pr \<phi>)"
        using Cons \<Psi>(3) by blast
      moreover
      have "Pr \<phi> \<le> (\<Sum>\<phi>\<leftarrow>?\<Psi>\<^sub>1. Pr \<phi>)"
        using \<Psi>(2)
              biconditional_weaken
              list_deduction_def
              map_negation_list_implication
              set_deduction_base_theory
              implication_list_summation_inequality
        by blast
      ultimately have "(\<Sum>\<phi>'\<leftarrow>(\<phi> # \<Phi>). Pr \<phi>') \<le> (\<Sum>\<gamma> \<leftarrow>(?\<Psi>\<^sub>1 @ ?\<Psi>\<^sub>2 @ ?\<Gamma>). Pr \<gamma>)"
        by simp
      moreover have "(\<Sum>\<phi>'\<leftarrow>(?\<Psi>\<^sub>1 @ ?\<Psi>\<^sub>2). Pr \<phi>') = (\<Sum>\<gamma>\<leftarrow>(map fst \<Psi>). Pr \<gamma>)"
      proof (induct \<Psi>)
        case Nil
        then show ?case by simp
      next
        case (Cons \<psi> \<Psi>)
        let ?\<Psi>\<^sub>1 = "map (uncurry (\<setminus>)) \<Psi>"
        let ?\<Psi>\<^sub>2 = "map (uncurry (\<sqinter>)) \<Psi>"
        let ?\<psi>\<^sub>1 = "uncurry (\<setminus>) \<psi>"
        let ?\<psi>\<^sub>2 = "uncurry (\<sqinter>) \<psi>"
        assume "(\<Sum>\<phi>'\<leftarrow>(?\<Psi>\<^sub>1 @ ?\<Psi>\<^sub>2). Pr \<phi>') = (\<Sum>\<gamma>\<leftarrow>(map fst \<Psi>). Pr \<gamma>)"
        moreover
        {
          let ?\<gamma> = "fst \<psi>"
          let ?\<psi> = "snd \<psi>"
          have "uncurry (\<setminus>) = (\<lambda> \<psi>. (fst \<psi>) \<setminus> (snd \<psi>))"
               "uncurry (\<sqinter>) = (\<lambda> \<psi>. (fst \<psi>) \<sqinter> (snd \<psi>))"
            by fastforce+
          moreover have "Pr ?\<gamma> = Pr (?\<gamma> \<setminus> ?\<psi>) + Pr (?\<gamma> \<sqinter> ?\<psi>)"
            by (simp add: subtraction_identity)
          ultimately have "Pr ?\<gamma> = Pr ?\<psi>\<^sub>1 + Pr ?\<psi>\<^sub>2"
            by simp
        }
        moreover have "mset (?\<psi>\<^sub>1 # ?\<psi>\<^sub>2 # (?\<Psi>\<^sub>1 @ ?\<Psi>\<^sub>2)) =
                       mset (map (uncurry (\<setminus>)) (\<psi> # \<Psi>) @ map (uncurry (\<sqinter>)) (\<psi> # \<Psi>))"
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
  firstComponent :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" ("\<AA>")
  where
    "\<AA> \<Psi> [] = []"
  | "\<AA> \<Psi> (\<delta> # \<Delta>) =
       (case find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> of
             None \<Rightarrow> \<AA> \<Psi> \<Delta>
           | Some \<psi> \<Rightarrow> \<psi> # (\<AA> (remove1 \<psi> \<Psi>) \<Delta>))"

primrec (in Minimal_Logic)
  secondComponent :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" ("\<BB>")
  where
    "\<BB> \<Psi> [] = []"
  | "\<BB> \<Psi> (\<delta> # \<Delta>) =
       (case find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> of
             None \<Rightarrow> \<BB> \<Psi> \<Delta>
           | Some \<psi> \<Rightarrow> \<delta> # (\<BB> (remove1 \<psi> \<Psi>) \<Delta>))"

lemma (in Minimal_Logic) firstComponent_secondComponent_mset_connection:
  "mset (map (uncurry (\<rightarrow>)) (\<AA> \<Psi> \<Delta>)) = mset (map snd (\<BB> \<Psi> \<Delta>))"
proof -
  have "\<forall> \<Psi>. mset (map (uncurry (\<rightarrow>)) (\<AA> \<Psi> \<Delta>)) = mset (map snd (\<BB> \<Psi> \<Delta>))"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "mset (map (uncurry (\<rightarrow>)) (\<AA> \<Psi> (\<delta> # \<Delta>))) =
            mset (map snd (\<BB> \<Psi> (\<delta> # \<Delta>)))"
      proof (cases "find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        then show ?thesis using Cons by simp
      next
        case False
        from this obtain \<psi> where
          "find (\<lambda>\<psi>. uncurry (\<rightarrow>) \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
          "uncurry (\<rightarrow>) \<psi> = snd \<delta>"
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
  "\<BB> [] \<Delta> = []"
  by (induct \<Delta>, simp+)

lemma (in Minimal_Logic) firstComponent_msub:
  "mset (\<AA> \<Psi> \<Delta>) \<subseteq># mset \<Psi>"
proof -
  have "\<forall> \<Psi>. mset (\<AA> \<Psi> \<Delta>) \<subseteq># mset \<Psi>"
  proof(induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "mset (\<AA> \<Psi> (\<delta> # \<Delta>)) \<subseteq># mset \<Psi>"
      proof (cases "find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        then show ?thesis using Cons by simp
      next
        case False
        from this obtain \<psi> where
          \<psi>: "find (\<lambda>\<psi>. uncurry (\<rightarrow>) \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
             "\<psi> \<in> set \<Psi>"
          using find_Some_set_membership
          by fastforce
        have "mset (\<AA> (remove1 \<psi> \<Psi>) \<Delta>) \<subseteq># mset (remove1 \<psi> \<Psi>)"
          using Cons by metis
        thus ?thesis using \<psi> by (simp add: insert_subset_eq_iff)
      qed
    }
    then show ?case by blast
  qed
  thus ?thesis by blast
qed

lemma (in Minimal_Logic) secondComponent_msub:
  "mset (\<BB> \<Psi> \<Delta>) \<subseteq># mset \<Delta>"
proof -
  have "\<forall>\<Psi>. mset (\<BB> \<Psi> \<Delta>) \<subseteq># mset \<Delta>"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "mset (\<BB> \<Psi> (\<delta> # \<Delta>)) \<subseteq># mset (\<delta> # \<Delta>)"
      using Cons
      by (cases "find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> = None",
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
  "mset (map snd (\<BB> \<Psi> \<Delta>)) \<subseteq># mset (map (uncurry (\<rightarrow>)) \<Psi>)"
proof -
  have "\<forall>\<Psi>. mset (map snd (\<BB> \<Psi> \<Delta>)) \<subseteq># mset (map (uncurry (\<rightarrow>)) \<Psi>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "mset (map snd (\<BB> \<Psi> (\<delta> # \<Delta>))) \<subseteq># mset (map (uncurry (\<rightarrow>)) \<Psi>)"
      proof (cases "find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        then show ?thesis
          using Cons by simp
      next
        case False
        from this obtain \<psi> where \<psi>:
          "find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
          by auto
        hence "\<BB> \<Psi> (\<delta> # \<Delta>) = \<delta> # (\<BB> (remove1 \<psi> \<Psi>) \<Delta>)"
          using \<psi> by fastforce
        with Cons have "mset (map snd (\<BB> \<Psi> (\<delta> # \<Delta>))) \<subseteq>#
                        mset ((snd \<delta>) # map (uncurry (\<rightarrow>)) (remove1 \<psi> \<Psi>))"
          by (simp, metis mset_map mset_remove1)
        moreover from \<psi> have "snd \<delta> = (uncurry (\<rightarrow>)) \<psi>"
          using find_Some_predicate by fastforce
        ultimately have "mset (map snd (\<BB> \<Psi> (\<delta> # \<Delta>))) \<subseteq>#
                         mset (map (uncurry (\<rightarrow>)) (\<psi> # (remove1 \<psi> \<Psi>)))"
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
  assumes "mset (map snd \<Delta>) \<subseteq># mset (map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>))"
  shows "mset (map snd (\<Delta> \<ominus> (\<BB> \<Psi> \<Delta>))) \<subseteq># mset (\<Gamma> \<ominus> (map snd \<Psi>))"
proof -
  have "\<forall> \<Psi> \<Gamma>. mset (map snd \<Delta>) \<subseteq># mset (map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>)) \<longrightarrow>
               mset (map snd (\<Delta> \<ominus> (\<BB> \<Psi> \<Delta>))) \<subseteq># mset (\<Gamma> \<ominus> (map snd \<Psi>))"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi> \<Gamma>
      assume \<diamondsuit>: "mset (map snd (\<delta> # \<Delta>)) \<subseteq># mset (map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> map snd \<Psi>)"
      have "mset (map snd ((\<delta> # \<Delta>) \<ominus> \<BB> \<Psi> (\<delta> # \<Delta>))) \<subseteq># mset (\<Gamma> \<ominus> map snd \<Psi>)"
      proof (cases "find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        hence A: "snd \<delta> \<notin> set (map (uncurry (\<rightarrow>)) \<Psi>)"
        proof (induct \<Psi>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<psi> \<Psi>)
          then show ?case
            by (cases "uncurry (\<rightarrow>) \<psi> = snd \<delta>", simp+)
        qed
        moreover have "mset (map snd \<Delta>)
                   \<subseteq># mset (map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> map snd \<Psi>) - {#snd \<delta>#}"
          using \<diamondsuit> insert_subset_eq_iff by fastforce
        ultimately have "mset (map snd \<Delta>)
                      \<subseteq># mset (map (uncurry (\<rightarrow>)) \<Psi> @ (remove1 (snd \<delta>) \<Gamma>) \<ominus> map snd \<Psi>)"
          by (metis (no_types) mset_remove1
                               mset_eq_perm union_code
                               listSubtract.simps(2)
                               listSubtract_remove1_cons_perm
                               remove1_append)
        hence B: "mset (map snd (\<Delta> \<ominus> (\<BB> \<Psi> \<Delta>))) \<subseteq># mset (remove1 (snd \<delta>) \<Gamma> \<ominus> (map snd \<Psi>))"
          using Cons by blast
        have C: "snd \<delta> \<in># mset (snd \<delta> # map snd \<Delta> @
                                  (map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> map snd \<Psi>) \<ominus> (snd \<delta> # map snd \<Delta>))"
          by (meson in_multiset_in_set list.set_intros(1))
        have "mset (map snd (\<delta> # \<Delta>))
           + (mset (map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> map snd \<Psi>)
              - mset (map snd (\<delta> # \<Delta>)))
         = mset (map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> map snd \<Psi>)"
          using \<diamondsuit> subset_mset.add_diff_inverse by blast
        then have "snd \<delta> \<in># mset (map (uncurry (\<rightarrow>)) \<Psi>) + (mset \<Gamma> - mset (map snd \<Psi>))"
          using C by simp
        with A have "snd \<delta> \<in> set \<Gamma>"
          by (metis (no_types) diff_subset_eq_self
                               in_multiset_in_set
                               subset_mset.add_diff_inverse
                               union_iff)
        have D: "\<BB> \<Psi> \<Delta> = \<BB> \<Psi> (\<delta> # \<Delta>)"
          using \<open>find (\<lambda>\<psi>. uncurry (\<rightarrow>) \<psi> = snd \<delta>) \<Psi> = None\<close>
          by simp
        obtain diff :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
          "\<forall>x0 x1. (\<exists>v2. x1 @ v2 <~~> x0) = (x1 @ diff x0 x1 <~~> x0)"
          by moura
        then have E: "mset (map snd (\<BB> \<Psi> (\<delta> # \<Delta>))
                    @ diff (map (uncurry (\<rightarrow>)) \<Psi>) (map snd (\<BB> \<Psi> (\<delta> # \<Delta>))))
                    = mset (map (uncurry (\<rightarrow>)) \<Psi>)"
          by (meson secondComponent_snd_projection_msub mset_eq_perm mset_le_perm_append)
        have F: "\<forall>a m ma. (add_mset (a::'a) m \<subseteq># ma) = (a \<in># ma \<and> m \<subseteq># ma - {#a#})"
          using insert_subset_eq_iff by blast
        then have "snd \<delta> \<in># mset (map snd (\<BB> \<Psi> (\<delta> # \<Delta>))
                                  @ diff (map (uncurry (\<rightarrow>)) \<Psi>) (map snd (\<BB> \<Psi> (\<delta> # \<Delta>))))
                          + mset (\<Gamma> \<ominus> map snd \<Psi>)"
          using E \<diamondsuit> by force
        then have "snd \<delta> \<in># mset (\<Gamma> \<ominus> map snd \<Psi>)"
          using A E by (metis (no_types) in_multiset_in_set union_iff)
        then have G: "add_mset (snd \<delta>) (mset (map snd (\<Delta> \<ominus> \<BB> \<Psi> \<Delta>))) \<subseteq># mset (\<Gamma> \<ominus> map snd \<Psi>)"
          using B F by force
        have H: "\<forall>ps psa f. \<not> mset (ps::('a \<times> 'a) list) \<subseteq># mset psa \<or>
                              mset ((map f psa::'a list) \<ominus> map f ps) = mset (map f (psa \<ominus> ps))"
          using map_listSubtract_mset_equivalence by blast
        have "snd \<delta> \<notin># mset (map snd (\<BB> \<Psi> (\<delta> # \<Delta>)))
                     + mset (diff (map (uncurry (\<rightarrow>)) \<Psi>) (map snd (\<BB> \<Psi> (\<delta> # \<Delta>))))"
          using A E by auto
        then have "add_mset (snd \<delta>) (mset (map snd (\<Delta> \<ominus> \<BB> \<Psi> \<Delta>)))
                 = mset (map snd (\<delta> # \<Delta>) \<ominus> map snd (\<BB> \<Psi> (\<delta> # \<Delta>)))"
          using D H secondComponent_msub by auto
        then show ?thesis
          using G H by (metis (no_types) secondComponent_msub)
      next
        case False
        from this obtain \<psi> where \<psi>: "find (\<lambda>\<psi>. uncurry (\<rightarrow>) \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
          by auto
        let ?\<Psi>' = "remove1 \<psi> \<Psi>"
        let ?\<Gamma>' = "remove1 (snd \<psi>) \<Gamma>"
        have "snd \<delta> = uncurry (\<rightarrow>) \<psi>"
             "\<psi> \<in> set \<Psi>"
             "mset ((\<delta> # \<Delta>) \<ominus> \<BB> \<Psi> (\<delta> # \<Delta>)) =
              mset (\<Delta> \<ominus> \<BB> ?\<Psi>' \<Delta>)"
          using \<psi> find_Some_predicate find_Some_set_membership
          by fastforce+
        moreover
        have "mset (\<Gamma> \<ominus> map snd \<Psi>) = mset (?\<Gamma>' \<ominus> map snd ?\<Psi>')"
          by (simp, metis \<open>\<psi> \<in> set \<Psi>\<close> image_mset_add_mset in_multiset_in_set insert_DiffM)
        moreover
        obtain search :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'a" where
          "\<forall>xs P. (\<exists>x. x \<in> set xs \<and> P x) = (search xs P \<in> set xs \<and> P (search xs P))"
          by moura
        then have "\<forall>p ps. (find p ps \<noteq> None \<or> (\<forall>pa. pa \<notin> set ps \<or> \<not> p pa))
                        \<and> (find p ps = None \<or> search ps p \<in> set ps \<and> p (search ps p))"
          by (metis (full_types) find_None_iff)
        then have "(find (\<lambda>p. uncurry (\<rightarrow>) p = snd \<delta>) \<Psi> \<noteq> None
                    \<or> (\<forall>p. p \<notin> set \<Psi> \<or> uncurry (\<rightarrow>) p \<noteq> snd \<delta>))
                 \<and> (find (\<lambda>p. uncurry (\<rightarrow>) p = snd \<delta>) \<Psi> = None
                    \<or> search \<Psi> (\<lambda>p. uncurry (\<rightarrow>) p = snd \<delta>) \<in> set \<Psi>
                    \<and> uncurry (\<rightarrow>) (search \<Psi> (\<lambda>p. uncurry (\<rightarrow>) p = snd \<delta>)) = snd \<delta>)"
          by blast
        hence "snd \<delta> \<in> set (map (uncurry (\<rightarrow>)) \<Psi>)"
          by (metis (no_types) False image_eqI image_set)
        moreover
        have A: "add_mset (uncurry (\<rightarrow>) \<psi>) (image_mset snd (mset \<Delta>))
              = image_mset snd (add_mset \<delta> (mset \<Delta>))"
          by (simp add: \<open>snd \<delta> = uncurry (\<rightarrow>) \<psi>\<close>)
        have B: "{#snd \<delta>#} \<subseteq># image_mset (uncurry (\<rightarrow>)) (mset \<Psi>)"
          using \<open>snd \<delta> \<in> set (map (uncurry (\<rightarrow>)) \<Psi>)\<close> by force
        have "image_mset (uncurry (\<rightarrow>)) (mset \<Psi>) - {#snd \<delta>#}
            = image_mset (uncurry (\<rightarrow>)) (mset (remove1 \<psi> \<Psi>))"
          by (simp add: \<open>\<psi> \<in> set \<Psi>\<close> \<open>snd \<delta> = uncurry (\<rightarrow>) \<psi>\<close> image_mset_Diff)
        then have "mset (map snd (\<Delta> \<ominus> \<BB> (remove1 \<psi> \<Psi>) \<Delta>))
                \<subseteq># mset (remove1 (snd \<psi>) \<Gamma> \<ominus> map snd (remove1 \<psi> \<Psi>))"
          by (metis (no_types)
                    A B \<diamondsuit> Cons.hyps
                    calculation(1)
                    calculation(4)
                    insert_subset_eq_iff
                    mset.simps(2)
                    mset_map
                    subset_mset.diff_add_assoc2
                    union_code)
        ultimately show ?thesis by fastforce
      qed
    }
    then show ?case by blast
  qed
  thus ?thesis using assms by auto
qed

primrec (in Classical_Propositional_Logic)
  mergeWitness :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" ("\<JJ>")
  where
    "\<JJ> \<Psi> [] = \<Psi>"
  | "\<JJ> \<Psi> (\<delta> # \<Delta>) =
       (case find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> of
             None \<Rightarrow> \<delta> # \<JJ> \<Psi> \<Delta>
           | Some \<psi> \<Rightarrow> (fst \<delta> \<sqinter> fst \<psi>, snd \<psi>) # (\<JJ> (remove1 \<psi> \<Psi>) \<Delta>))"

lemma (in Classical_Propositional_Logic) mergeWitness_right_empty [simp]:
  "\<JJ> [] \<Delta> = \<Delta>"
  by (induct \<Delta>, simp+)

lemma (in Classical_Propositional_Logic) secondComponent_mergeWitness_snd_projection:
  "mset (map snd \<Psi> @ map snd (\<Delta> \<ominus> (\<BB> \<Psi> \<Delta>))) = mset (map snd (\<JJ> \<Psi> \<Delta>))"
proof -
  have "\<forall> \<Psi>. mset (map snd \<Psi> @ map snd (\<Delta> \<ominus> (\<BB> \<Psi> \<Delta>))) = mset (map snd (\<JJ> \<Psi> \<Delta>))"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "mset (map snd \<Psi> @ map snd ((\<delta> # \<Delta>) \<ominus> \<BB> \<Psi> (\<delta> # \<Delta>))) =
            mset (map snd (\<JJ> \<Psi> (\<delta> # \<Delta>)))"
      proof (cases "find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> = None")
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
        from this obtain \<psi> where \<psi>: "find (\<lambda>\<psi>. uncurry (\<rightarrow>) \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
          by auto
        moreover have "\<psi> \<in> set \<Psi>"
          by (meson \<psi> find_Some_set_membership)
        moreover
        let ?\<Psi>' = "remove1 \<psi> \<Psi>"
        from Cons have
          "mset (map snd ?\<Psi>' @ map snd (\<Delta> \<ominus> \<BB> ?\<Psi>' \<Delta>)) =
            mset (map snd (\<JJ> ?\<Psi>' \<Delta>))"
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
  "(map (uncurry (\<rightarrow>)) \<Delta> @ map (uncurry (\<rightarrow>)) \<Psi> \<ominus> map snd (\<BB> \<Psi> \<Delta>)) \<preceq>
    map (uncurry (\<rightarrow>)) (\<JJ> \<Psi> \<Delta>)"
proof -
  have "\<forall> \<Psi>. (map (uncurry (\<rightarrow>)) \<Delta> @
              map (uncurry (\<rightarrow>)) \<Psi> \<ominus> map snd (\<BB> \<Psi> \<Delta>)) \<preceq>
              map (uncurry (\<rightarrow>)) (\<JJ> \<Psi> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case
      by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "\<turnstile> (uncurry (\<rightarrow>)) \<delta> \<rightarrow> (uncurry (\<rightarrow>)) \<delta>"
        using Axiom_1 Modus_Ponens implication_absorption by blast
      have
        "(map (uncurry (\<rightarrow>)) (\<delta> # \<Delta>) @
          map (uncurry (\<rightarrow>)) \<Psi> \<ominus> map snd (\<BB> \<Psi> (\<delta> # \<Delta>))) \<preceq>
          map (uncurry (\<rightarrow>)) (\<JJ> \<Psi> (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        thus ?thesis
          using Cons
                \<open>\<turnstile> (uncurry (\<rightarrow>)) \<delta> \<rightarrow> (uncurry (\<rightarrow>)) \<delta>\<close>
          by (simp, metis stronger_theory_left_right_cons)
      next
        case False
        from this obtain \<psi> where \<psi>: "find (\<lambda>\<psi>. uncurry (\<rightarrow>) \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
          by auto
        from \<psi> have "snd \<delta> = uncurry (\<rightarrow>) \<psi>"
          using find_Some_predicate by fastforce
        from \<psi> \<open>snd \<delta> = uncurry (\<rightarrow>) \<psi>\<close> have
          "mset (map (uncurry (\<rightarrow>)) (\<delta> # \<Delta>) @
                   map (uncurry (\<rightarrow>)) \<Psi> \<ominus> map snd (\<BB> \<Psi> (\<delta> # \<Delta>))) =
           mset (map (uncurry (\<rightarrow>)) (\<delta> # \<Delta>) @
                   map (uncurry (\<rightarrow>)) (remove1 \<psi> \<Psi>) \<ominus>
                   map snd (\<BB> (remove1 \<psi> \<Psi>) \<Delta>))"
          by (simp add: find_Some_set_membership image_mset_Diff)
        hence
          "(map (uncurry (\<rightarrow>)) (\<delta> # \<Delta>) @
              map (uncurry (\<rightarrow>)) \<Psi> \<ominus> map snd (\<BB> \<Psi> (\<delta> # \<Delta>))) \<preceq>
           (map (uncurry (\<rightarrow>)) (\<delta> # \<Delta>) @
              map (uncurry (\<rightarrow>)) (remove1 \<psi> \<Psi>) \<ominus> map snd (\<BB> (remove1 \<psi> \<Psi>) \<Delta>))"
          by (simp add: msub_stronger_theory_intro)
        with Cons \<open>\<turnstile> (uncurry (\<rightarrow>)) \<delta> \<rightarrow> (uncurry (\<rightarrow>)) \<delta>\<close> have
          "(map (uncurry (\<rightarrow>)) (\<delta> # \<Delta>) @
            map (uncurry (\<rightarrow>)) \<Psi> \<ominus> map snd (\<BB> \<Psi> (\<delta> # \<Delta>)))
            \<preceq> ((uncurry (\<rightarrow>)) \<delta> # map (uncurry (\<rightarrow>)) (\<JJ> (remove1 \<psi> \<Psi>) \<Delta>))"
          apply simp
          using stronger_theory_left_right_cons
                stronger_theory_transitive
          by blast
        moreover
        let ?\<alpha> = "fst \<delta>"
        let ?\<beta> = "fst \<psi>"
        let ?\<gamma> = "snd \<psi>"
        have "uncurry (\<rightarrow>) = (\<lambda> \<delta>. fst \<delta> \<rightarrow> snd \<delta>)" by fastforce
        with \<psi> have "(uncurry (\<rightarrow>)) \<delta> = ?\<alpha> \<rightarrow> ?\<beta> \<rightarrow> ?\<gamma>"
          using find_Some_predicate by fastforce
        hence "\<turnstile> ((?\<alpha> \<sqinter> ?\<beta>) \<rightarrow> ?\<gamma>) \<rightarrow> (uncurry (\<rightarrow>)) \<delta>"
          using biconditional_def curry_uncurry by auto
        with \<psi> have
          "((uncurry (\<rightarrow>)) \<delta> # map (uncurry (\<rightarrow>)) (\<JJ> (remove1 \<psi> \<Psi>) \<Delta>)) \<preceq>
           map (uncurry (\<rightarrow>)) (\<JJ> \<Psi> (\<delta> # \<Delta>))"
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
      and "mset (map snd \<Delta>) \<subseteq># mset (map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>))"
    shows "mset (map snd (\<JJ> \<Psi> \<Delta>)) \<subseteq># mset \<Gamma>"
proof -
  have "\<forall>\<Psi> \<Gamma>. mset (map snd \<Psi>) \<subseteq># mset \<Gamma> \<longrightarrow>
               mset (map snd \<Delta>) \<subseteq># mset (map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>)) \<longrightarrow>
               mset (map snd (\<JJ> \<Psi> \<Delta>)) \<subseteq># mset \<Gamma>"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi> :: "('a \<times> 'a) list"
      fix \<Gamma> :: "'a list"
      assume \<diamondsuit>: "mset (map snd \<Psi>) \<subseteq># mset \<Gamma>"
                "mset (map snd (\<delta> # \<Delta>)) \<subseteq># mset (map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>))"
      have "mset (map snd (\<JJ> \<Psi> (\<delta> # \<Delta>))) \<subseteq># mset \<Gamma>"
      proof (cases "find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        hence "snd \<delta> \<notin> set (map (uncurry (\<rightarrow>)) \<Psi>)"
        proof (induct \<Psi>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<psi> \<Psi>)
          hence "uncurry (\<rightarrow>) \<psi> \<noteq> snd \<delta>" by fastforce
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
        moreover
        have "add_mset (snd \<delta>) (mset (\<Gamma> \<ominus> map snd \<Psi>) - {#snd \<delta>#}) = mset (\<Gamma> \<ominus> map snd \<Psi>)"
          by (meson \<open>snd \<delta> \<in># mset (\<Gamma> \<ominus> map snd \<Psi>)\<close> insert_DiffM)
        then have "image_mset snd (mset \<Delta>) - (mset \<Gamma> - add_mset (snd \<delta>) (image_mset snd (mset \<Psi>)))
               \<subseteq># {#x \<rightarrow> y. (x, y) \<in># mset \<Psi>#}"
          using \<diamondsuit>(2) by (simp, metis add_mset_diff_bothsides
                                     listSubtract_mset_homomorphism
                                     mset_map subset_eq_diff_conv)
        hence "mset (map snd \<Delta>)
           \<subseteq># mset (map (uncurry (\<rightarrow>)) \<Psi> @ (remove1 (snd \<delta>) \<Gamma>) \<ominus> (map snd \<Psi>))"
          using subset_eq_diff_conv by (simp, blast)
        ultimately have "mset (map snd (\<JJ> \<Psi> \<Delta>)) \<subseteq># mset (remove1 (snd \<delta>) \<Gamma>)"
          using Cons by blast
        hence "mset (map snd (\<delta> # (\<JJ> \<Psi> \<Delta>))) \<subseteq># mset \<Gamma>"
          by (simp, metis \<open>snd \<delta> \<in># mset (\<Gamma> \<ominus> map snd \<Psi>)\<close>
                          cancel_ab_semigroup_add_class.diff_right_commute
                          diff_single_trivial
                          insert_subset_eq_iff
                          listSubtract_mset_homomorphism
                          multi_drop_mem_not_eq)
        with \<open>find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> = None\<close>
        show ?thesis
          by simp
      next
        case False
        from this obtain \<psi> where \<psi>:
          "find (\<lambda>\<psi>. uncurry (\<rightarrow>) \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
          by fastforce
        let ?\<chi> = "fst \<psi>"
        let ?\<gamma> = "snd \<psi>"
        have "uncurry (\<rightarrow>) = (\<lambda> \<psi>. fst \<psi> \<rightarrow> snd \<psi>)"
          by fastforce
        moreover
        from this have "uncurry (\<rightarrow>) \<psi> = ?\<chi> \<rightarrow> ?\<gamma>" by fastforce
        with \<psi> have A: "(?\<chi>, ?\<gamma>) \<in> set \<Psi>"
                and B: "snd \<delta> = ?\<chi> \<rightarrow> ?\<gamma>"
          using find_Some_predicate
          by (simp add: find_Some_set_membership, fastforce)
        let ?\<Psi>' = "remove1 (?\<chi>, ?\<gamma>) \<Psi>"
        from B \<diamondsuit>(2) have
          "mset (map snd \<Delta>) \<subseteq># mset (map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> map snd \<Psi>) - {# ?\<chi> \<rightarrow> ?\<gamma> #}"
          by (simp add: insert_subset_eq_iff)
        moreover
        have "mset (map (uncurry (\<rightarrow>)) \<Psi>)
            = add_mset (case (fst \<psi>, snd \<psi>) of (x, xa) \<Rightarrow> x \<rightarrow> xa)
                       (image_mset (uncurry (\<rightarrow>)) (mset (remove1 (fst \<psi>, snd \<psi>) \<Psi>)))"
          by (metis (no_types) A
                    image_mset_add_mset
                    in_multiset_in_set
                    insert_DiffM
                    mset_map
                    mset_remove1
                    uncurry_def)
        ultimately have
          "mset (map snd \<Delta>) \<subseteq># mset (map (uncurry (\<rightarrow>)) ?\<Psi>' @ \<Gamma> \<ominus> map snd \<Psi>)"
          using add_diff_cancel_left'
                add_diff_cancel_right
                diff_diff_add_mset
                diff_subset_eq_self
                mset_append
                subset_eq_diff_conv
                subset_mset.diff_add
          by auto
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
                         mset (map (uncurry (\<rightarrow>)) ?\<Psi>' @ (remove1 ?\<gamma> \<Gamma>) \<ominus> map snd ?\<Psi>')"
          by simp
        hence "mset (map snd (\<JJ> ?\<Psi>' \<Delta>)) \<subseteq># mset (remove1 ?\<gamma> \<Gamma>)"
          using Cons \<diamondsuit>(1) A
          by (metis (no_types, lifting)
                    image_mset_add_mset
                    in_multiset_in_set
                    insert_DiffM
                    insert_subset_eq_iff
                    mset_map mset_remove1
                    prod.collapse)
        with \<diamondsuit>(1) A have "mset (map snd (\<JJ> ?\<Psi>' \<Delta>)) + {# ?\<gamma> #} \<subseteq># mset \<Gamma>"
          by (metis add_mset_add_single
                    image_eqI
                    insert_subset_eq_iff
                    mset_remove1
                    mset_subset_eqD
                    set_map
                    set_mset_mset
                    snd_conv)
        hence "mset (map snd ((fst \<delta> \<sqinter> ?\<chi>, ?\<gamma>) # (\<JJ> ?\<Psi>' \<Delta>))) \<subseteq># mset \<Gamma>"
          by simp
        moreover from \<psi> have
          "\<JJ> \<Psi> (\<delta> # \<Delta>) = (fst \<delta> \<sqinter> ?\<chi>, ?\<gamma>) # (\<JJ> ?\<Psi>' \<Delta>)"
          by simp
        ultimately show ?thesis by simp
      qed
    }
    thus ?case by blast
  qed
  with assms show ?thesis by blast
qed

lemma (in Classical_Propositional_Logic) right_mergeWitness_stronger_theory:
  "map (uncurry (\<squnion>)) \<Delta> \<preceq> map (uncurry (\<squnion>)) (\<JJ> \<Psi> \<Delta>)"
proof -
  have "\<forall> \<Psi>. map (uncurry (\<squnion>)) \<Delta> \<preceq> map (uncurry (\<squnion>)) (\<JJ> \<Psi> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "map (uncurry (\<squnion>)) (\<delta> # \<Delta>) \<preceq> map (uncurry (\<squnion>)) (\<JJ> \<Psi> (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        hence "\<JJ> \<Psi> (\<delta> # \<Delta>) = \<delta> # \<JJ> \<Psi> \<Delta>"
          by simp
        moreover have "\<turnstile> (uncurry (\<squnion>)) \<delta> \<rightarrow> (uncurry (\<squnion>)) \<delta>"
          by (metis Axiom_1 Axiom_2 Modus_Ponens)
        ultimately show ?thesis using Cons
          by (simp add: stronger_theory_left_right_cons)
      next
        case False
        from this obtain \<psi> where \<psi>:
          "find (\<lambda>\<psi>. uncurry (\<rightarrow>) \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
          by fastforce
        let ?\<chi> = "fst \<psi>"
        let ?\<gamma> = "snd \<psi>"
        let ?\<mu> = "fst \<delta>"
        have "uncurry (\<rightarrow>) = (\<lambda> \<psi>. fst \<psi> \<rightarrow> snd \<psi>)"
             "uncurry (\<squnion>) = (\<lambda> \<delta>. fst \<delta> \<squnion> snd \<delta>)"
          by fastforce+
        hence "uncurry (\<squnion>) \<delta> = ?\<mu> \<squnion> (?\<chi> \<rightarrow> ?\<gamma>)"
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
  "map (uncurry (\<squnion>)) \<Psi> \<preceq> map (uncurry (\<squnion>)) (\<JJ> \<Psi> \<Delta>)"
proof -
  have "\<forall> \<Psi>. map (uncurry (\<squnion>)) \<Psi> \<preceq> map (uncurry (\<squnion>)) (\<JJ> \<Psi> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case
      by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "map (uncurry (\<squnion>)) \<Psi> \<preceq> map (uncurry (\<squnion>)) (\<JJ> \<Psi> (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        then show ?thesis
          using Cons stronger_theory_right_cons
          by auto
      next
        case False
        from this obtain \<psi> where \<psi>:
          "find (\<lambda>\<psi>. uncurry (\<rightarrow>) \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
          by fastforce
        let ?\<chi> = "fst \<psi>"
        let ?\<gamma> = "snd \<psi>"
        let ?\<mu> = "fst \<delta>"
        have "uncurry (\<rightarrow>) = (\<lambda> \<psi>. fst \<psi> \<rightarrow> snd \<psi>)"
             "uncurry (\<squnion>) = (\<lambda> \<delta>. fst \<delta> \<squnion> snd \<delta>)"
          by fastforce+
        hence
          "uncurry (\<squnion>) \<delta> = ?\<mu> \<squnion> (?\<chi> \<rightarrow> ?\<gamma>)"
          "uncurry (\<squnion>) \<psi> = ?\<chi> \<squnion> ?\<gamma>"
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
         "map (uncurry (\<squnion>)) (\<psi> # (remove1 \<psi> \<Psi>)) \<preceq>
          map (uncurry (\<squnion>)) (\<JJ> \<Psi> (\<delta> # \<Delta>))"
         using Cons \<psi> stronger_theory_left_right_cons
         by simp
       moreover from \<psi> have "\<psi> \<in> set \<Psi>"
         by (simp add: find_Some_set_membership)
       hence "mset (map (uncurry (\<squnion>)) (\<psi> # (remove1 \<psi> \<Psi>))) =
              mset (map (uncurry (\<squnion>)) \<Psi>)"
         by (metis insert_DiffM
                   mset.simps(2)
                   mset_map
                   mset_remove1
                   set_mset_mset)
       hence "map (uncurry (\<squnion>)) \<Psi> \<preceq> map (uncurry (\<squnion>)) (\<psi> # (remove1 \<psi> \<Psi>))"
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
  assumes "mset (map snd \<Delta>) \<subseteq># mset (map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>))"
      and "map (uncurry (\<rightarrow>)) \<Delta> @ (map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> map snd \<Psi>) \<ominus> map snd \<Delta> $\<turnstile> \<Phi>"
          (is "?\<Gamma>\<^sub>0 $\<turnstile> \<Phi>")
    shows "map (uncurry (\<rightarrow>)) (\<JJ> \<Psi> \<Delta>) @ \<Gamma> \<ominus> map snd (\<JJ> \<Psi> \<Delta>) $\<turnstile> \<Phi>"
          (is "?\<Gamma> $\<turnstile> \<Phi>")
proof -
  let ?\<Sigma> = "\<BB> \<Psi> \<Delta>"
  let ?A = "map (uncurry (\<rightarrow>)) \<Delta>"
  let ?B = "map (uncurry (\<rightarrow>)) \<Psi>"
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
  moreover
  from calculation have "image_mset snd (mset \<Delta> - mset (\<BB> \<Psi> \<Delta>))
                      \<subseteq># mset \<Gamma> - image_mset snd (mset \<Psi>)"
    by simp
  hence "mset \<Gamma> - image_mset snd (mset \<Psi>)
                - image_mset snd (mset \<Delta> - mset (\<BB> \<Psi> \<Delta>))
         + image_mset snd (mset \<Delta> - mset (\<BB> \<Psi> \<Delta>))
       = mset \<Gamma> - image_mset snd (mset \<Psi>)"
    using subset_mset.diff_add by blast
  then have "image_mset snd (mset \<Delta> - mset (\<BB> \<Psi> \<Delta>))
              + ({#x \<rightarrow> y. (x, y) \<in># mset \<Psi>#}
                  + (mset \<Gamma> - (image_mset snd (mset \<Psi>)
                                + image_mset snd (mset \<Delta> - mset (\<BB> \<Psi> \<Delta>)))))
          = {#x \<rightarrow> y. (x, y) \<in># mset \<Psi>#} + (mset \<Gamma> - image_mset snd (mset \<Psi>))"
    by (simp add: union_commute)
  with calculation have "mset ?\<Gamma>\<^sub>0 = mset (?A @ (?B \<ominus> ?C) @ (?D \<ominus> ?E))"
    by (simp, metis (no_types) add_diff_cancel_left image_mset_union subset_mset.diff_add)
  moreover have "(?A @ (?B \<ominus> ?C)) \<preceq> map (uncurry (\<rightarrow>)) (\<JJ> \<Psi> \<Delta>)"
    using secondComponent_mergeWitness_stronger_theory by simp
  moreover have "mset (?D \<ominus> ?E) = mset (\<Gamma> \<ominus> map snd (\<JJ> \<Psi> \<Delta>))"
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
    "map (uncurry (\<squnion>)) \<Psi> :\<turnstile> \<phi>"
    "(map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>)) $\<turnstile> \<Phi>"
    by auto
  let ?\<Psi>\<^sub>1 = "zip (map (\<lambda> (\<chi>,\<gamma>). \<psi> \<squnion> \<chi>) \<Psi>) (map snd \<Psi>)"
  let ?\<Gamma>\<^sub>1 = "map (uncurry (\<rightarrow>)) ?\<Psi>\<^sub>1 @ \<Gamma> \<ominus> (map snd ?\<Psi>\<^sub>1)"
  let ?\<Psi>\<^sub>2 = "zip (map (\<lambda> (\<chi>,\<gamma>). \<psi> \<rightarrow> \<chi>) \<Psi>) (map (uncurry (\<rightarrow>)) ?\<Psi>\<^sub>1)"
  let ?\<Gamma>\<^sub>2 = "map (uncurry (\<rightarrow>)) ?\<Psi>\<^sub>2 @ ?\<Gamma>\<^sub>1 \<ominus> (map snd ?\<Psi>\<^sub>2)"
  have "map (uncurry (\<rightarrow>)) \<Psi> \<preceq> map (uncurry (\<rightarrow>)) ?\<Psi>\<^sub>2"
  proof (induct \<Psi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Psi>)
    let ?\<chi> = "fst \<delta>"
    let ?\<gamma> = "snd \<delta>"
    let ?\<Psi>\<^sub>1 = "zip (map (\<lambda> (\<chi>,\<gamma>). \<psi> \<squnion> \<chi>) \<Psi>) (map snd \<Psi>)"
    let ?\<Psi>\<^sub>2 = "zip (map (\<lambda> (\<chi>,\<gamma>). \<psi> \<rightarrow> \<chi>) \<Psi>) (map (uncurry (\<rightarrow>)) ?\<Psi>\<^sub>1)"
    let ?T\<^sub>1 = "\<lambda> \<Psi>. map (uncurry (\<rightarrow>)) (zip (map (\<lambda> (\<chi>,\<gamma>). \<psi> \<squnion> \<chi>) \<Psi>) (map snd \<Psi>))"
    let ?T\<^sub>2 = "\<lambda> \<Psi>. map (uncurry (\<rightarrow>)) (zip (map (\<lambda> (\<chi>,\<gamma>). \<psi> \<rightarrow> \<chi>) \<Psi>) (?T\<^sub>1 \<Psi>))"
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
    hence "?T\<^sub>2 (\<delta> # \<Psi>) = ((\<psi> \<rightarrow> ?\<chi>) \<rightarrow> (\<psi> \<squnion> ?\<chi>) \<rightarrow> ?\<gamma>) # (map (uncurry (\<rightarrow>)) ?\<Psi>\<^sub>2)"
      by simp
    moreover have "map (uncurry (\<rightarrow>)) (\<delta> # \<Psi>) = (?\<chi> \<rightarrow> ?\<gamma>) # map (uncurry (\<rightarrow>)) \<Psi>"
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
    assume "map (uncurry (\<rightarrow>)) \<Psi> \<preceq> map (uncurry (\<rightarrow>)) ?\<Psi>\<^sub>2"
    with identity have "((?\<chi> \<rightarrow> ?\<gamma>) # map (uncurry (\<rightarrow>)) \<Psi>) \<preceq>
                        (((\<psi> \<rightarrow> ?\<chi>) \<rightarrow> (\<psi> \<squnion> ?\<chi>) \<rightarrow> ?\<gamma>) # (map (uncurry (\<rightarrow>)) ?\<Psi>\<^sub>2))"
      using stronger_theory_left_right_cons by blast
    ultimately show ?case by simp
  qed
  hence "(map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>)) \<preceq>
         ((map (uncurry (\<rightarrow>)) ?\<Psi>\<^sub>2) @ \<Gamma> \<ominus> (map snd \<Psi>))"
    using stronger_theory_combine stronger_theory_reflexive by blast
  moreover have "mset ?\<Gamma>\<^sub>2 = mset ((map (uncurry (\<rightarrow>)) ?\<Psi>\<^sub>2) @ \<Gamma> \<ominus> (map snd ?\<Psi>\<^sub>1))"
    by simp
  ultimately have "(map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>)) \<preceq> ?\<Gamma>\<^sub>2"
    by (simp add: stronger_theory_relation_def)
  hence "?\<Gamma>\<^sub>2 $\<turnstile> \<Phi>"
    using \<Psi>(3) segmented_stronger_theory_left_monotonic by blast
  moreover
  have "(map (uncurry (\<squnion>)) ?\<Psi>\<^sub>2) :\<turnstile> \<psi> \<rightarrow> \<phi>"
  proof -
    let ?\<Gamma> = "map (\<lambda> (\<chi>, \<gamma>). (\<psi> \<rightarrow> \<chi>) \<squnion> (\<psi> \<squnion> \<chi>) \<rightarrow> \<gamma>) \<Psi>"
    let ?\<Sigma> = "map (\<lambda> (\<chi>, \<gamma>). (\<psi> \<rightarrow> (\<chi> \<squnion> \<gamma>))) \<Psi>"
    have "map (uncurry (\<squnion>)) ?\<Psi>\<^sub>2 = ?\<Gamma>"
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
        by metis
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
        by metis+
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
    moreover have "\<forall> \<phi>. (map (uncurry (\<squnion>)) \<Psi>) :\<turnstile> \<phi> \<longrightarrow> ?\<Sigma> :\<turnstile> \<psi> \<rightarrow> \<phi>"
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
        assume "map (uncurry (\<squnion>)) (\<delta> # \<Psi>) :\<turnstile> \<phi>"
        hence "map (uncurry (\<squnion>)) \<Psi> :\<turnstile> (uncurry (\<squnion>)) \<delta> \<rightarrow> \<phi>"
          using list_deduction_theorem
          by simp
        hence "?\<Sigma> :\<turnstile> \<psi> \<rightarrow> (uncurry (\<squnion>)) \<delta> \<rightarrow> \<phi>"
          using Cons
          by blast
        moreover
        {
          fix \<alpha> \<beta> \<gamma>
          have "\<turnstile> (\<alpha> \<rightarrow> \<beta> \<rightarrow> \<gamma>) \<rightarrow> ((\<alpha> \<rightarrow> \<beta>) \<rightarrow> \<alpha> \<rightarrow> \<gamma>)"
            using Axiom_2 by auto
        }
        ultimately have "?\<Sigma> :\<turnstile> (\<psi> \<rightarrow> (uncurry (\<squnion>)) \<delta>) \<rightarrow> \<psi> \<rightarrow> \<phi>"
          using list_deduction_weaken [where ?\<Gamma>="?\<Sigma>"]
                list_deduction_modus_ponens [where ?\<Gamma>="?\<Sigma>"]
          by metis
        moreover
        have "(\<lambda> \<delta>. \<psi> \<rightarrow> (uncurry (\<squnion>)) \<delta>) = (\<lambda> \<delta>. (\<lambda> (\<chi>, \<gamma>). (\<psi> \<rightarrow> (\<chi> \<squnion> \<gamma>))) \<delta>)"
          by fastforce
        ultimately have "?\<Sigma> :\<turnstile> (\<lambda> (\<chi>, \<gamma>). (\<psi> \<rightarrow> (\<chi> \<squnion> \<gamma>))) \<delta> \<rightarrow> \<psi> \<rightarrow> \<phi>"
          by metis
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
  moreover have "\<turnstile> (map (uncurry (\<squnion>)) \<Psi> :\<rightarrow> \<phi>) \<rightarrow> (map (uncurry (\<squnion>)) ?\<Psi>\<^sub>1) :\<rightarrow> (\<psi> \<squnion> \<phi>)"
  proof (induct \<Psi>)
    case Nil
    then show ?case
      unfolding disjunction_def
      apply simp
      using Axiom_1 Modus_Ponens
      by blast
  next
    case (Cons \<nu> \<Psi>)
    let ?\<Delta> = "map (uncurry (\<squnion>)) \<Psi>"
    let ?\<Delta>' = "map (uncurry (\<squnion>)) (\<nu> # \<Psi>)"
    let ?\<Sigma> = "map (uncurry (\<squnion>)) (zip (map (\<lambda> (\<chi>,\<gamma>). \<psi> \<squnion> \<chi>) \<Psi>) (map snd \<Psi>))"
    let ?\<Sigma>' = "map (uncurry (\<squnion>)) (zip (map (\<lambda> (\<chi>,\<gamma>). \<psi> \<squnion> \<chi>) (\<nu> # \<Psi>)) (map snd (\<nu> # \<Psi>)))"
    have "\<turnstile> (?\<Delta>' :\<rightarrow>  \<phi>) \<rightarrow> (uncurry (\<squnion>)) \<nu> \<rightarrow> ?\<Delta> :\<rightarrow> \<phi>"
      by (simp, metis Axiom_1 Axiom_2 Modus_Ponens)
    with Cons have "\<turnstile> (?\<Delta>' :\<rightarrow>  \<phi>) \<rightarrow> (uncurry (\<squnion>)) \<nu> \<rightarrow> ?\<Sigma> :\<rightarrow> (\<psi> \<squnion> \<phi>)"
      using hypothetical_syllogism Modus_Ponens
      by blast
    hence "(?\<Delta>' :\<rightarrow>  \<phi>) # ((uncurry (\<squnion>)) \<nu>) # ?\<Sigma> :\<turnstile> \<psi> \<squnion> \<phi>"
      by (simp add: list_deduction_def)
    moreover have "set ((?\<Delta>' :\<rightarrow>  \<phi>) # ((uncurry (\<squnion>)) \<nu>) # ?\<Sigma>) =
                   set (((uncurry (\<squnion>)) \<nu>) # (?\<Delta>' :\<rightarrow>  \<phi>) # ?\<Sigma>)"
      by fastforce
    ultimately have "((uncurry (\<squnion>)) \<nu>) # (?\<Delta>' :\<rightarrow>  \<phi>) # ?\<Sigma> :\<turnstile> \<psi> \<squnion> \<phi>"
      using list_deduction_monotonic by blast
    hence "(?\<Delta>' :\<rightarrow>  \<phi>) # ?\<Sigma> :\<turnstile> ((uncurry (\<squnion>)) \<nu>) \<rightarrow> (\<psi> \<squnion> \<phi>)"
      using list_deduction_theorem
      by simp
    moreover
    let ?\<chi> = "fst \<nu>"
    let ?\<gamma> = "snd \<nu>"
    have "(\<lambda> \<nu> . (uncurry (\<squnion>)) \<nu>) = (\<lambda> \<nu>. fst \<nu> \<squnion> snd \<nu>)"
      by fastforce
    hence "(uncurry (\<squnion>)) \<nu> = ?\<chi> \<squnion> ?\<gamma>" by simp
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
    moreover have
      "map (uncurry (\<squnion>)) (\<nu> # \<Psi>) :\<rightarrow> \<phi>
       # (\<psi> \<squnion> fst \<nu>) \<squnion> snd \<nu>
       # map (uncurry (\<squnion>)) (zip (map (\<lambda>(_, a). \<psi> \<squnion> a) \<Psi>) (map snd \<Psi>)) :\<turnstile> (\<psi> \<squnion> fst \<nu>) \<squnion> snd \<nu>"
      by (meson list.set_intros(1)
                list_deduction_monotonic
                list_deduction_reflection
                set_subset_Cons)
    ultimately have "(?\<Delta>' :\<rightarrow>  \<phi>) # ((\<psi> \<squnion> ?\<chi>) \<squnion> ?\<gamma>) # ?\<Sigma> :\<turnstile> \<psi> \<squnion> \<phi>"
      using  list_deduction_modus_ponens list_deduction_monotonic by blast
    moreover
    have "(\<lambda> \<nu>. \<psi> \<squnion> fst \<nu>) = (\<lambda> (\<chi>, \<gamma>). \<psi> \<squnion> \<chi>)"
      by fastforce
    hence "\<psi> \<squnion> fst \<nu> = (\<lambda> (\<chi>, \<gamma>). \<psi> \<squnion> \<chi>) \<nu>"
      by metis
    hence "((\<psi> \<squnion> ?\<chi>) \<squnion> ?\<gamma>) # ?\<Sigma> = ?\<Sigma>'"
      by simp
    ultimately have "(?\<Delta>' :\<rightarrow>  \<phi>) # ?\<Sigma>' :\<turnstile> \<psi> \<squnion> \<phi>" by simp
    then show ?case by (simp add: list_deduction_def)
  qed
  with \<Psi>(2) have "map (uncurry (\<squnion>)) ?\<Psi>\<^sub>1 :\<turnstile> (\<psi> \<squnion> \<phi>)"
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
    "map (uncurry (\<squnion>)) \<Psi> :\<turnstile> \<psi> \<squnion> \<phi>"
    "map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>) $\<turnstile> (\<psi> \<rightarrow> \<phi> # \<Phi>)"
    using segmented_deduction.simps(2) by blast
  let ?\<Gamma>' = "map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>)"
  from \<Psi> obtain \<Delta> where \<Delta>:
    "mset (map snd \<Delta>) \<subseteq># mset ?\<Gamma>'"
    "map (uncurry (\<squnion>)) \<Delta> :\<turnstile> \<psi> \<rightarrow> \<phi>"
    "(map (uncurry (\<rightarrow>)) \<Delta> @ ?\<Gamma>' \<ominus> (map snd \<Delta>)) $\<turnstile> \<Phi>"
    using segmented_deduction.simps(2) by blast
  let ?\<Omega> = "\<JJ> \<Psi> \<Delta>"
  have "mset (map snd ?\<Omega>) \<subseteq># mset \<Gamma>"
    using \<Delta>(1) \<Psi>(1) mergeWitness_msub_intro
    by blast
  moreover have "map (uncurry (\<squnion>)) ?\<Omega> :\<turnstile> \<phi>"
  proof -
    have "map (uncurry (\<squnion>)) ?\<Omega> :\<turnstile> \<psi> \<squnion> \<phi>"
         "map (uncurry (\<squnion>)) ?\<Omega> :\<turnstile> \<psi> \<rightarrow> \<phi>"
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
  moreover have "map (uncurry (\<rightarrow>)) ?\<Omega> @ \<Gamma> \<ominus> (map snd ?\<Omega>) $\<turnstile> \<Phi>"
    using \<Delta>(1) \<Delta>(3) \<Psi>(1) mergeWitness_segmented_deduction_intro by blast
  ultimately show "\<Gamma> $\<turnstile> (\<phi> # \<Phi>)"
    using segmented_deduction.simps(2) by blast
qed

primrec (in Minimal_Logic)
  XWitness :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" ("\<XX>")
  where
    "\<XX> \<Psi> [] = []"
  | "\<XX> \<Psi> (\<delta> # \<Delta>) =
       (case find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> of
             None \<Rightarrow> \<delta> # \<XX> \<Psi> \<Delta>
           | Some \<psi> \<Rightarrow> (fst \<psi> \<rightarrow> fst \<delta>, snd \<psi>) # (\<XX> (remove1 \<psi> \<Psi>) \<Delta>))"

primrec (in Minimal_Logic)
  XComponent :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" ("\<XX>\<^sub>\<bullet>")
  where
    "\<XX>\<^sub>\<bullet> \<Psi> [] = []"
  | "\<XX>\<^sub>\<bullet> \<Psi> (\<delta> # \<Delta>) =
       (case find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> of
             None \<Rightarrow> \<XX>\<^sub>\<bullet> \<Psi> \<Delta>
           | Some \<psi> \<Rightarrow> (fst \<psi> \<rightarrow> fst \<delta>, snd \<psi>) # (\<XX>\<^sub>\<bullet> (remove1 \<psi> \<Psi>) \<Delta>))"

primrec (in Minimal_Logic)
  YWitness :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" ("\<YY>")
  where
    "\<YY> \<Psi> [] = \<Psi>"
  | "\<YY> \<Psi> (\<delta> # \<Delta>) =
       (case find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> of
             None \<Rightarrow> \<YY> \<Psi> \<Delta>
           | Some \<psi> \<Rightarrow> (fst \<psi>, (fst \<psi> \<rightarrow> fst \<delta>) \<rightarrow> snd \<psi>) #
                       (\<YY> (remove1 \<psi> \<Psi>) \<Delta>))"

primrec (in Minimal_Logic)
  YComponent :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" ("\<YY>\<^sub>\<bullet>")
  where
    "\<YY>\<^sub>\<bullet> \<Psi> [] = []"
  | "\<YY>\<^sub>\<bullet> \<Psi> (\<delta> # \<Delta>) =
       (case find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> of
             None \<Rightarrow> \<YY>\<^sub>\<bullet> \<Psi> \<Delta>
           | Some \<psi> \<Rightarrow> (fst \<psi>, (fst \<psi> \<rightarrow> fst \<delta>) \<rightarrow> snd \<psi>) #
                       (\<YY>\<^sub>\<bullet> (remove1 \<psi> \<Psi>) \<Delta>))"

lemma (in Minimal_Logic) XWitness_right_empty [simp]:
  "\<XX> [] \<Delta> = \<Delta>"
  by (induct \<Delta>, simp+)

lemma (in Minimal_Logic) YWitness_right_empty [simp]:
  "\<YY> [] \<Delta> = []"
  by (induct \<Delta>, simp+)

lemma (in Minimal_Logic) XWitness_map_snd_decomposition:
   "mset (map snd (\<XX> \<Psi> \<Delta>)) = mset (map snd ((\<AA> \<Psi> \<Delta>) @ (\<Delta> \<ominus> (\<BB> \<Psi> \<Delta>))))"
proof -
  have "\<forall>\<Psi>. mset (map snd (\<XX> \<Psi> \<Delta>)) = mset (map snd ((\<AA> \<Psi> \<Delta>) @ (\<Delta> \<ominus> (\<BB> \<Psi> \<Delta>))))"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "mset (map snd (\<XX> \<Psi> (\<delta> # \<Delta>)))
          = mset (map snd (\<AA> \<Psi> (\<delta> # \<Delta>) @ (\<delta> # \<Delta>) \<ominus> \<BB> \<Psi> (\<delta> # \<Delta>)))"
      using Cons
      by (cases "find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> = None",
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

lemma (in Minimal_Logic) YWitness_map_snd_decomposition:
   "mset (map snd (\<YY> \<Psi> \<Delta>)) = mset (map snd ((\<Psi> \<ominus> (\<AA> \<Psi> \<Delta>)) @ (\<YY>\<^sub>\<bullet> \<Psi> \<Delta>)))"
proof -
  have "\<forall> \<Psi>. mset (map snd (\<YY> \<Psi> \<Delta>)) = mset (map snd ((\<Psi> \<ominus> (\<AA> \<Psi> \<Delta>)) @ (\<YY>\<^sub>\<bullet> \<Psi> \<Delta>)))"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "mset (map snd (\<YY> \<Psi> (\<delta> # \<Delta>))) = mset (map snd (\<Psi> \<ominus> \<AA> \<Psi> (\<delta> # \<Delta>) @ \<YY>\<^sub>\<bullet> \<Psi> (\<delta> # \<Delta>)))"
        using Cons
        by (cases "find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> = None", fastforce+)
    }
    then show ?case by blast
  qed
  thus ?thesis by blast
qed

lemma (in Minimal_Logic) XWitness_msub:
  assumes "mset (map snd \<Psi>) \<subseteq># mset \<Gamma>"
      and "mset (map snd \<Delta>) \<subseteq># mset (map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>))"
    shows "mset (map snd (\<XX> \<Psi> \<Delta>)) \<subseteq># mset \<Gamma>"
proof -
  have "mset (map snd (\<Delta> \<ominus> (\<BB> \<Psi> \<Delta>))) \<subseteq># mset (\<Gamma> \<ominus> (map snd \<Psi>))"
    using assms secondComponent_diff_msub by blast
  moreover have "mset (map snd (\<AA> \<Psi> \<Delta>)) \<subseteq># mset (map snd \<Psi>)"
    using firstComponent_msub
    by (simp add: image_mset_subseteq_mono)
  moreover have "mset ((map snd \<Psi>) @ (\<Gamma> \<ominus> map snd \<Psi>)) = mset \<Gamma>"
    using assms(1)
    by simp
  moreover have "image_mset snd (mset (\<AA> \<Psi> \<Delta>)) + image_mset snd (mset (\<Delta> \<ominus> \<BB> \<Psi> \<Delta>))
               = mset (map snd (\<XX> \<Psi> \<Delta>))"
      using XWitness_map_snd_decomposition by force
  ultimately
  show ?thesis
    by (metis (no_types) mset_append mset_map subset_mset.add_mono)
qed

lemma (in Minimal_Logic) YComponent_msub:
  "mset (map snd (\<YY>\<^sub>\<bullet> \<Psi> \<Delta>)) \<subseteq># mset (map (uncurry (\<rightarrow>)) (\<XX> \<Psi> \<Delta>))"
proof -
  have "\<forall> \<Psi>. mset (map snd (\<YY>\<^sub>\<bullet> \<Psi> \<Delta>)) \<subseteq># mset (map (uncurry (\<rightarrow>)) (\<XX> \<Psi> \<Delta>))"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "mset (map snd (\<YY>\<^sub>\<bullet> \<Psi> (\<delta> # \<Delta>))) \<subseteq># mset (map (uncurry (\<rightarrow>)) (\<XX> \<Psi> (\<delta> # \<Delta>)))"
        using Cons
        by (cases "find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> = None",
            simp, metis add_mset_add_single
                        mset_subset_eq_add_left
                        subset_mset.order_trans,
            fastforce)
    }
    then show ?case by blast
  qed
  thus ?thesis by blast
qed

lemma (in Minimal_Logic) YWitness_msub:
  assumes "mset (map snd \<Psi>) \<subseteq># mset \<Gamma>"
      and "mset (map snd \<Delta>) \<subseteq># mset (map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>))"
    shows "mset (map snd (\<YY> \<Psi> \<Delta>)) \<subseteq>#
           mset (map (uncurry (\<rightarrow>)) (\<XX> \<Psi> \<Delta>) @ \<Gamma> \<ominus> map snd (\<XX> \<Psi> \<Delta>))"
proof -
  have A: "image_mset snd (mset \<Psi>) \<subseteq># mset \<Gamma>" using assms by simp
  have B: "image_mset snd (mset (\<AA> \<Psi> \<Delta>)) + image_mset snd (mset \<Delta> - mset (\<BB> \<Psi> \<Delta>)) \<subseteq># mset \<Gamma>"
    using A XWitness_map_snd_decomposition assms(2) XWitness_msub by auto
  have "mset \<Gamma> - image_mset snd (mset \<Psi>) = mset (\<Gamma> \<ominus> map snd \<Psi>)"
    by simp
  then have C: "mset (map snd (\<Delta> \<ominus> \<BB> \<Psi> \<Delta>)) + image_mset snd (mset \<Psi>) \<subseteq># mset \<Gamma>"
    using A by (metis (full_types) assms(2) secondComponent_diff_msub subset_mset.le_diff_conv2)
  have "image_mset snd (mset (\<Psi> \<ominus> \<AA> \<Psi> \<Delta>)) + image_mset snd (mset (\<AA> \<Psi> \<Delta>)) = image_mset snd (mset \<Psi>)"
    by (metis (no_types) image_mset_union
                         listSubtract_mset_homomorphism
                         firstComponent_msub
                         subset_mset.diff_add)
  then have "image_mset snd (mset \<Psi> - mset (\<AA> \<Psi> \<Delta>))
              + (image_mset snd (mset (\<AA> \<Psi> \<Delta>)) + image_mset snd (mset \<Delta> - mset (\<BB> \<Psi> \<Delta>)))
           = mset (map snd (\<Delta> \<ominus> \<BB> \<Psi> \<Delta>)) + image_mset snd (mset \<Psi>)"
    by (simp add: union_commute)
  then have "image_mset snd (mset \<Psi> - mset (\<AA> \<Psi> \<Delta>))
          \<subseteq># mset \<Gamma> - (image_mset snd (mset (\<AA> \<Psi> \<Delta>)) + image_mset snd (mset \<Delta> - mset (\<BB> \<Psi> \<Delta>)))"
      by (metis (no_types) B C subset_mset.le_diff_conv2)
  hence "mset (map snd (\<Psi> \<ominus> \<AA> \<Psi> \<Delta>)) \<subseteq># mset (\<Gamma> \<ominus> map snd (\<XX> \<Psi> \<Delta>))"
    using assms XWitness_map_snd_decomposition
    by simp
  thus ?thesis
    using YComponent_msub
          YWitness_map_snd_decomposition
    by (simp add: mset_subset_eq_mono_add union_commute)
qed

lemma (in Classical_Propositional_Logic) XWitness_right_stronger_theory:
  "map (uncurry (\<squnion>)) \<Delta> \<preceq> map (uncurry (\<squnion>)) (\<XX> \<Psi> \<Delta>)"
proof -
  have "\<forall> \<Psi>. map (uncurry (\<squnion>)) \<Delta> \<preceq> map (uncurry (\<squnion>)) (\<XX> \<Psi> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "map (uncurry (\<squnion>)) (\<delta> # \<Delta>) \<preceq> map (uncurry (\<squnion>)) (\<XX> \<Psi> (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        then show ?thesis
          using Cons
          by (simp add: stronger_theory_left_right_cons
                        trivial_implication)
      next
        case False
        from this obtain \<psi> where
          \<psi>: "find (\<lambda>\<psi>. uncurry (\<rightarrow>) \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
             "\<psi> \<in> set \<Psi>"
             "(fst \<psi> \<rightarrow> snd \<psi>) = snd \<delta>"
          using find_Some_set_membership
                find_Some_predicate
          by fastforce
        let ?\<Psi>' = "remove1 \<psi> \<Psi>"
        let ?\<alpha> = "fst \<psi>"
        let ?\<beta> = "snd \<psi>"
        let ?\<gamma> = "fst \<delta>"
        have "map (uncurry (\<squnion>)) \<Delta> \<preceq> map (uncurry (\<squnion>)) (\<XX> ?\<Psi>' \<Delta>)"
          using Cons by simp
        moreover
        have "(uncurry (\<squnion>)) = (\<lambda> \<delta>. fst \<delta> \<squnion> snd \<delta>)" by fastforce
        hence "(uncurry (\<squnion>)) \<delta> = ?\<gamma> \<squnion> (?\<alpha> \<rightarrow> ?\<beta>)" using \<psi>(3) by fastforce
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

lemma (in Classical_Propositional_Logic) YWitness_left_stronger_theory:
  "map (uncurry (\<squnion>)) \<Psi> \<preceq> map (uncurry (\<squnion>)) (\<YY> \<Psi> \<Delta>)"
proof -
  have "\<forall> \<Psi>. map (uncurry (\<squnion>)) \<Psi> \<preceq> map (uncurry (\<squnion>)) (\<YY> \<Psi> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "map (uncurry (\<squnion>)) \<Psi> \<preceq> map (uncurry (\<squnion>)) (\<YY> \<Psi> (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        then show ?thesis using Cons by simp
      next
        case False
        from this obtain \<psi> where
          \<psi>: "find (\<lambda>\<psi>. uncurry (\<rightarrow>) \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
             "\<psi> \<in> set \<Psi>"
             "(uncurry (\<squnion>)) \<psi> = fst \<psi> \<squnion> snd \<psi>"
          using find_Some_set_membership
          by fastforce
        let ?\<phi> = "fst \<psi> \<squnion> (fst \<psi> \<rightarrow> fst \<delta>) \<rightarrow> snd \<psi>"
        let ?\<Psi>' = "remove1 \<psi> \<Psi>"
        have "map (uncurry (\<squnion>)) ?\<Psi>' \<preceq> map (uncurry (\<squnion>)) (\<YY> ?\<Psi>' \<Delta>)"
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
        hence "\<turnstile> ?\<phi> \<rightarrow> (uncurry (\<squnion>)) \<psi>" using \<psi>(3) by auto
        ultimately
        have "map (uncurry (\<squnion>)) (\<psi> # ?\<Psi>') \<preceq> (?\<phi> # map (uncurry (\<squnion>)) (\<YY> ?\<Psi>' \<Delta>))"
          by (simp add: stronger_theory_left_right_cons)
        moreover
        from \<psi> have "mset (map (uncurry (\<squnion>)) (\<psi> # ?\<Psi>')) = mset (map (uncurry (\<squnion>)) \<Psi>)"
          by (metis mset_eq_perm mset_map perm_remove)
        ultimately show ?thesis
          using stronger_theory_relation_alt_def \<psi>(1) by auto
      qed
    }
    then show ?case by blast
  qed
  thus ?thesis by blast
qed

lemma (in Minimal_Logic) XWitness_secondComponent_diff_decomposition:
  "mset (\<XX> \<Psi> \<Delta>) = mset (\<XX>\<^sub>\<bullet> \<Psi> \<Delta> @ \<Delta> \<ominus> \<BB> \<Psi> \<Delta>)"
proof -
  have "\<forall> \<Psi>. mset (\<XX> \<Psi> \<Delta>) = mset (\<XX>\<^sub>\<bullet> \<Psi> \<Delta> @ \<Delta> \<ominus> \<BB> \<Psi> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "mset (\<XX> \<Psi> (\<delta> # \<Delta>)) =
            mset (\<XX>\<^sub>\<bullet> \<Psi> (\<delta> # \<Delta>) @ (\<delta> # \<Delta>) \<ominus> \<BB> \<Psi> (\<delta> # \<Delta>))"
        using Cons
        by (cases "find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> = None",
            simp, metis add_mset_add_single secondComponent_msub subset_mset.diff_add_assoc2,
            fastforce)
    }
    then show ?case by blast
  qed
  thus ?thesis by blast
qed

lemma (in Minimal_Logic) YWitness_firstComponent_diff_decomposition:
  "mset (\<YY> \<Psi> \<Delta>) = mset (\<Psi> \<ominus> \<AA> \<Psi> \<Delta> @ \<YY>\<^sub>\<bullet> \<Psi> \<Delta>)"
proof -
  have "\<forall> \<Psi>. mset (\<YY> \<Psi> \<Delta>) = mset (\<Psi> \<ominus> \<AA> \<Psi> \<Delta> @ \<YY>\<^sub>\<bullet> \<Psi> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "mset (\<YY> \<Psi> (\<delta> # \<Delta>)) =
            mset (\<Psi> \<ominus> \<AA> \<Psi> (\<delta> # \<Delta>) @ \<YY>\<^sub>\<bullet> \<Psi> (\<delta> # \<Delta>))"
      using Cons
        by (cases "find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> = None", simp, fastforce)
    }
    then show ?case by blast
  qed
  thus ?thesis by blast
qed

lemma (in Minimal_Logic) YWitness_right_stronger_theory:
    "map (uncurry (\<rightarrow>)) \<Delta> \<preceq> map (uncurry (\<rightarrow>)) (\<YY> \<Psi> \<Delta> \<ominus> (\<Psi> \<ominus> \<AA> \<Psi> \<Delta>) @ (\<Delta> \<ominus> \<BB> \<Psi> \<Delta>))"
proof -
  let ?\<ff> = "\<lambda>\<Psi> \<Delta>. (\<Psi> \<ominus> \<AA> \<Psi> \<Delta>)"
  let ?\<gg> = "\<lambda> \<Psi> \<Delta>. (\<Delta> \<ominus> \<BB> \<Psi> \<Delta>)"
  have "\<forall> \<Psi>. map (uncurry (\<rightarrow>)) \<Delta> \<preceq>  map (uncurry (\<rightarrow>)) (\<YY> \<Psi> \<Delta> \<ominus> ?\<ff> \<Psi> \<Delta> @ ?\<gg> \<Psi> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    let ?\<delta> = "(uncurry (\<rightarrow>)) \<delta>"
    {
      fix \<Psi>
      have "map (uncurry (\<rightarrow>)) (\<delta> # \<Delta>)
          \<preceq> map (uncurry (\<rightarrow>)) (\<YY> \<Psi> (\<delta> # \<Delta>) \<ominus> ?\<ff> \<Psi> (\<delta> # \<Delta>) @ ?\<gg> \<Psi> (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> = None")
        case True
        moreover
        from Cons have
          "map (uncurry (\<rightarrow>)) (\<delta> # \<Delta>) \<preceq> map (uncurry (\<rightarrow>)) (\<delta> # \<YY> \<Psi> \<Delta> \<ominus> ?\<ff> \<Psi> \<Delta> @ ?\<gg> \<Psi> \<Delta>)"
          by (simp add: stronger_theory_left_right_cons trivial_implication)
        moreover
        have "mset (map (uncurry (\<rightarrow>)) (\<delta> # \<YY> \<Psi> \<Delta> \<ominus> ?\<ff> \<Psi> \<Delta> @ ?\<gg> \<Psi> \<Delta>))
            = mset (map (uncurry (\<rightarrow>)) (\<YY> \<Psi> \<Delta> \<ominus> ?\<ff> \<Psi> \<Delta> @ ((\<delta> # \<Delta>) \<ominus> \<BB> \<Psi> \<Delta>)))"
          by (simp,
              metis (no_types, lifting)
                    add_mset_add_single
                    image_mset_single
                    image_mset_union
                    secondComponent_msub
                    mset_subset_eq_multiset_union_diff_commute)
        moreover have
          "\<forall>\<Psi> \<Phi>. \<Psi> \<preceq> \<Phi>
              = (\<exists>\<Sigma>. map snd \<Sigma> = \<Psi>
                    \<and> mset (map fst \<Sigma>) \<subseteq># mset \<Phi>
                    \<and> (\<forall>\<xi>. \<xi> \<notin> set \<Sigma> \<or> \<turnstile> (uncurry (\<rightarrow>) \<xi>)))"
            by (simp add: Ball_def_raw stronger_theory_relation_def)
        moreover have
          "((uncurry (\<rightarrow>) \<delta>) # map (uncurry (\<rightarrow>)) \<Delta>)
           \<preceq> ((uncurry (\<rightarrow>) \<delta>) # map (uncurry (\<rightarrow>)) (\<YY> \<Psi> \<Delta> \<ominus> (?\<ff> \<Psi> \<Delta>))
              @ map (uncurry (\<rightarrow>)) (?\<gg> \<Psi> \<Delta>))"
          using calculation by auto
        ultimately show ?thesis
          by (simp, metis union_mset_add_mset_right)
      next
        case False
        from this obtain \<psi> where
          \<psi>: "find (\<lambda>\<psi>. uncurry (\<rightarrow>) \<psi> = snd \<delta>) \<Psi> = Some \<psi>"
             "uncurry (\<rightarrow>) \<psi> = snd \<delta>"
          using find_Some_predicate
          by fastforce
        let ?\<alpha> = "fst \<psi>"
        let ?\<beta> = "fst \<delta>"
        let ?\<gamma> = "snd \<psi>"
        have "(\<lambda> \<delta>. fst \<delta> \<rightarrow> snd \<delta>) = uncurry (\<rightarrow>)" by fastforce
        hence "?\<beta> \<rightarrow> ?\<alpha> \<rightarrow> ?\<gamma> = uncurry (\<rightarrow>) \<delta>" using \<psi>(2) by metis
        moreover
        let ?A = "\<YY> (remove1 \<psi> \<Psi>) \<Delta>"
        let ?B = "\<AA> (remove1 \<psi> \<Psi>) \<Delta>"
        let ?C = "\<BB> (remove1 \<psi> \<Psi>) \<Delta>"
        let ?D = "?A \<ominus> ((remove1 \<psi> \<Psi>) \<ominus> ?B)"
        have "mset ((remove1 \<psi> \<Psi>) \<ominus> ?B) \<subseteq># mset ?A"
          using YWitness_firstComponent_diff_decomposition by simp
        hence "mset (map (uncurry (\<rightarrow>))
                    (((?\<alpha>, (?\<alpha> \<rightarrow> ?\<beta>) \<rightarrow> ?\<gamma>) # ?A) \<ominus> remove1 \<psi> (\<Psi> \<ominus> ?B)
                     @ (remove1 \<delta> ((\<delta> # \<Delta>) \<ominus> ?C))))
            = mset ((?\<alpha> \<rightarrow> (?\<alpha> \<rightarrow> ?\<beta>) \<rightarrow> ?\<gamma>) # map (uncurry (\<rightarrow>)) (?D @ (\<Delta> \<ominus> ?C)))"
          by (simp, metis (no_types, hide_lams)
                          add_mset_add_single
                          image_mset_add_mset
                          prod.simps(2)
                          subset_mset.diff_add_assoc2)
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
        hence "(?\<beta> \<rightarrow> ?\<alpha> \<rightarrow> ?\<gamma> # map (uncurry (\<rightarrow>)) \<Delta>) \<preceq>
                (?\<alpha> \<rightarrow> (?\<alpha> \<rightarrow> ?\<beta>) \<rightarrow> ?\<gamma> # map (uncurry (\<rightarrow>)) (?D @ (\<Delta> \<ominus> ?C)))"
          using Cons stronger_theory_left_right_cons by blast
        ultimately show ?thesis
          using \<psi> by (simp add: stronger_theory_relation_alt_def)
      qed
    }
    then show ?case by blast
  qed
  thus ?thesis by blast
qed

lemma (in Minimal_Logic) XComponent_YComponent_connection:
  "map (uncurry (\<rightarrow>)) (\<XX>\<^sub>\<bullet> \<Psi> \<Delta>) = map snd (\<YY>\<^sub>\<bullet> \<Psi> \<Delta>)"
proof -
  have "\<forall> \<Psi>. map (uncurry (\<rightarrow>)) (\<XX>\<^sub>\<bullet> \<Psi> \<Delta>) = map snd (\<YY>\<^sub>\<bullet> \<Psi> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have "map (uncurry (\<rightarrow>)) (\<XX>\<^sub>\<bullet> \<Psi> (\<delta> # \<Delta>)) = map snd (\<YY>\<^sub>\<bullet> \<Psi> (\<delta> # \<Delta>))"
        using Cons
        by (cases "find (\<lambda> \<psi>. (uncurry (\<rightarrow>)) \<psi> = snd \<delta>) \<Psi> = None", simp, fastforce)
    }
    then show ?case by blast
  qed
  thus ?thesis by blast
qed

lemma (in Classical_Propositional_Logic) XWitness_YWitness_segmented_deduction_intro:
  assumes "mset (map snd \<Psi>) \<subseteq># mset \<Gamma>"
      and "mset (map snd \<Delta>) \<subseteq># mset (map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>))"
      and "map (uncurry (\<rightarrow>)) \<Delta> @ (map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> map snd \<Psi>) \<ominus> map snd \<Delta> $\<turnstile> \<Phi>"
          (is "?\<Gamma>\<^sub>0 $\<turnstile> \<Phi>")
        shows "map (uncurry (\<rightarrow>)) (\<YY> \<Psi> \<Delta>) @
                (map (uncurry (\<rightarrow>)) (\<XX> \<Psi> \<Delta>) @ \<Gamma> \<ominus> map snd (\<XX> \<Psi> \<Delta>)) \<ominus>
                 map snd (\<YY> \<Psi> \<Delta>) $\<turnstile> \<Phi>"
          (is "?\<Gamma> $\<turnstile> \<Phi>")
proof -
  let ?A = "map (uncurry (\<rightarrow>)) (\<YY> \<Psi> \<Delta>)"
  let ?B = "map (uncurry (\<rightarrow>)) (\<XX> \<Psi> \<Delta>)"
  let ?C = "\<Psi> \<ominus> \<AA> \<Psi> \<Delta>"
  let ?D = "map (uncurry (\<rightarrow>)) ?C"
  let ?E = "\<Delta> \<ominus> \<BB> \<Psi> \<Delta>"
  let ?F = "map (uncurry (\<rightarrow>)) ?E"
  let ?G = "map snd (\<BB> \<Psi> \<Delta>)"
  let ?H = "map (uncurry (\<rightarrow>)) (\<XX>\<^sub>\<bullet> \<Psi> \<Delta>)"
  let ?I = "\<AA> \<Psi> \<Delta>"
  let ?J = "map snd (\<XX> \<Psi> \<Delta>)"
  let ?K = "map snd (\<YY> \<Psi> \<Delta>)"
  have "mset (map (uncurry (\<rightarrow>)) (\<YY> \<Psi> \<Delta> \<ominus> ?C @ ?E)) = mset (?A \<ominus> ?D @ ?F)"
    by (simp add: YWitness_firstComponent_diff_decomposition)
  hence "(map (uncurry (\<rightarrow>)) \<Delta>) \<preceq> (?A \<ominus> ?D @ ?F)"
    using YWitness_right_stronger_theory
          stronger_theory_relation_alt_def
    by (simp, metis (no_types, lifting))
  hence "?\<Gamma>\<^sub>0 \<preceq> ((?A \<ominus> ?D @ ?F) @ (map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> map snd \<Psi>) \<ominus> map snd \<Delta>)"
    using stronger_theory_combine stronger_theory_reflexive by blast
  moreover
  have \<spadesuit>: "mset ?G \<subseteq># mset (map (uncurry (\<rightarrow>)) \<Psi>)"
          "mset (\<BB> \<Psi> \<Delta>) \<subseteq># mset \<Delta>"
          "mset (map snd ?E) \<subseteq># mset (\<Gamma> \<ominus> map snd \<Psi>)"
          "mset (map (uncurry (\<rightarrow>)) \<Psi> \<ominus> ?G) = mset ?D"
          "mset ?D \<subseteq># mset ?A"
          "mset (map snd ?I) \<subseteq># mset (map snd \<Psi>)"
          "mset (map snd ?I) \<subseteq># mset \<Gamma>"
          "mset (map snd (?I @ ?E)) = mset ?J"
    using secondComponent_msub
          secondComponent_diff_msub
          secondComponent_snd_projection_msub
          firstComponent_secondComponent_mset_connection
          XWitness_map_snd_decomposition
    by (simp,
        simp,
        metis assms(2),
        simp add: image_mset_Diff firstComponent_msub,
        simp add: YWitness_firstComponent_diff_decomposition,
        simp add: image_mset_subseteq_mono firstComponent_msub,
        metis assms(1) firstComponent_msub map_monotonic subset_mset.dual_order.trans,
        simp)
  hence "mset \<Delta> - mset (\<BB> \<Psi> \<Delta>) + mset (\<BB> \<Psi> \<Delta>) = mset \<Delta>"
    by simp
  hence \<heartsuit>: "{#x \<rightarrow> y. (x, y) \<in># mset \<Psi>#} + (mset \<Gamma> - image_mset snd (mset \<Psi>))
                                          - image_mset snd (mset \<Delta>)
           = {#x \<rightarrow> y. (x, y) \<in># mset \<Psi>#} + (mset \<Gamma> - image_mset snd (mset \<Psi>))
                                          - image_mset snd (mset \<Delta> - mset (\<BB> \<Psi> \<Delta>))
                                          - image_mset snd (mset (\<BB> \<Psi> \<Delta>))"
           "image_mset snd (mset \<Psi> - mset (\<AA> \<Psi> \<Delta>)) + image_mset snd (mset (\<AA> \<Psi> \<Delta>))
          = image_mset snd (mset \<Psi>)"
    using \<spadesuit>
    by (metis (no_types) diff_diff_add_mset image_mset_union,
        metis (no_types) image_mset_union firstComponent_msub subset_mset.diff_add)
  then have "mset \<Gamma> - image_mset snd (mset \<Psi>)
                    - image_mset snd (mset \<Delta> - mset (\<BB> \<Psi> \<Delta>))
           = mset \<Gamma> - (image_mset snd (mset \<Psi> - mset (\<AA> \<Psi> \<Delta>))
                    + image_mset snd (mset (\<XX> \<Psi> \<Delta>)))"
    using \<spadesuit> by (simp, metis (full_types) diff_diff_add_mset)
  hence "mset ((map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> map snd \<Psi>) \<ominus> map snd \<Delta>)
       = mset (?D @ (\<Gamma> \<ominus> ?J) \<ominus> map snd ?C)"
    using \<heartsuit> \<spadesuit> by (simp, metis (no_types) add.commute subset_mset.add_diff_assoc)
  ultimately have "?\<Gamma>\<^sub>0 \<preceq> ((?A \<ominus> ?D @ ?F) @ ?D @ (\<Gamma> \<ominus> ?J) \<ominus> map snd ?C)"
    unfolding stronger_theory_relation_alt_def
    by simp
  moreover
  have "mset ?F = mset (?B \<ominus> ?H)"
       "mset ?D \<subseteq># mset ?A"
       "mset (map snd (\<Psi> \<ominus> ?I)) \<subseteq># mset (\<Gamma> \<ominus> ?J)"
    by (simp add: XWitness_secondComponent_diff_decomposition,
        simp add: YWitness_firstComponent_diff_decomposition,
        simp, metis (no_types, lifting)
                    \<heartsuit>(2) \<spadesuit>(8) add.assoc assms(1) assms(2) image_mset_union
                    XWitness_msub mergeWitness_msub_intro
                    secondComponent_mergeWitness_snd_projection
                    mset_map
                    subset_mset.le_diff_conv2
                    union_code)
  hence "mset ((?A \<ominus> ?D @ ?F) @ ?D @ (\<Gamma> \<ominus> ?J) \<ominus> map snd ?C)
       = mset (?A @ (?B \<ominus> ?H @ \<Gamma> \<ominus> ?J) \<ominus> map snd ?C)"
        "mset ?H \<subseteq># mset ?B"
        "{#x \<rightarrow> y. (x, y) \<in># mset (\<XX>\<^sub>\<bullet> \<Psi> \<Delta>)#} = mset (map snd (\<YY>\<^sub>\<bullet> \<Psi> \<Delta>))"
    by (simp add: subset_mset.diff_add_assoc,
        simp add: XWitness_secondComponent_diff_decomposition,
        metis XComponent_YComponent_connection mset_map uncurry_def)
  hence "mset ((?A \<ominus> ?D @ ?F) @ ?D @ (\<Gamma> \<ominus> ?J) \<ominus> map snd ?C)
       = mset (?A @ (?B @ \<Gamma> \<ominus> ?J) \<ominus> (?H @ map snd ?C))"
        "{#x \<rightarrow> y. (x, y) \<in># mset (\<XX>\<^sub>\<bullet> \<Psi> \<Delta>)#} + image_mset snd (mset \<Psi> - mset (\<AA> \<Psi> \<Delta>))
       = mset (map snd (\<YY> \<Psi> \<Delta>))"
    using YWitness_map_snd_decomposition
    by (simp add: subset_mset.diff_add_assoc, force)
  hence "mset ((?A \<ominus> ?D @ ?F) @ ?D @ (\<Gamma> \<ominus> ?J) \<ominus> map snd ?C)
       = mset (?A @ (?B @ \<Gamma> \<ominus> ?J) \<ominus> ?K)"
    by (simp)
  ultimately have "?\<Gamma>\<^sub>0 \<preceq> (?A @ (?B @ \<Gamma> \<ominus> ?J) \<ominus> ?K)"
    unfolding stronger_theory_relation_alt_def
    by metis
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
    "map (uncurry (\<squnion>)) \<Psi> :\<turnstile> \<phi>"
    "map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>) $\<turnstile> (\<psi> # \<Phi>)"
    by fastforce
  let ?\<Gamma>\<^sub>0 = "map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>)"
  from \<Psi>(3) obtain \<Delta> where \<Delta>:
    "mset (map snd \<Delta>) \<subseteq># mset ?\<Gamma>\<^sub>0"
    "map (uncurry (\<squnion>)) \<Delta> :\<turnstile> \<psi>"
    "(map (uncurry (\<rightarrow>)) \<Delta> @ ?\<Gamma>\<^sub>0 \<ominus> (map snd \<Delta>)) $\<turnstile> \<Phi>"
    using segmented_deduction.simps(2) by blast
  let ?\<Psi>' = "\<XX> \<Psi> \<Delta>"
  let ?\<Gamma>\<^sub>1 = "map (uncurry (\<rightarrow>)) ?\<Psi>' @ \<Gamma> \<ominus> (map snd ?\<Psi>')"
  let ?\<Delta>' = "\<YY> \<Psi> \<Delta>"
  have "(map (uncurry (\<rightarrow>)) ?\<Delta>' @ ?\<Gamma>\<^sub>1 \<ominus> (map snd ?\<Delta>')) $\<turnstile> \<Phi>"
       "map (uncurry (\<squnion>)) \<Psi> \<preceq> map (uncurry (\<squnion>)) ?\<Delta>'"
    using \<Psi>(1) \<Delta>(1) \<Delta>(3)
          XWitness_YWitness_segmented_deduction_intro
          YWitness_left_stronger_theory
    by auto
  hence "?\<Gamma>\<^sub>1 $\<turnstile> (\<phi> # \<Phi>)"
    using \<Psi>(1) \<Psi>(2) \<Delta>(1)
          YWitness_msub segmented_deduction.simps(2)
          stronger_theory_deduction_monotonic
    by blast
  thus ?thesis
    using \<Psi>(1) \<Delta>(1) \<Delta>(2)
          XWitness_msub
          XWitness_right_stronger_theory
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
  shows "(map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>)) \<preceq> \<Gamma>"
proof -
  have "\<forall> \<Gamma>. mset (map snd \<Psi>) \<subseteq># mset \<Gamma> \<longrightarrow> (map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>)) \<preceq> \<Gamma>"
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
        "(map (uncurry (\<rightarrow>)) \<Psi> @ (remove1 (snd \<psi>) \<Gamma>) \<ominus> (map snd \<Psi>)) \<preceq> (remove1 ?\<gamma> \<Gamma>)"
        by blast
      hence "(map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd (\<psi> # \<Psi>))) \<preceq> (remove1 ?\<gamma> \<Gamma>)"
        by (simp add: stronger_theory_relation_alt_def)
      moreover
      have "(uncurry (\<rightarrow>)) = (\<lambda> \<psi>. fst \<psi> \<rightarrow> snd \<psi>)"
        by fastforce
      hence "\<turnstile> ?\<gamma> \<rightarrow> uncurry (\<rightarrow>) \<psi>"
        using Axiom_1 by simp
      ultimately have
        "(map (uncurry (\<rightarrow>)) (\<psi> # \<Psi>) @ \<Gamma> \<ominus> (map snd (\<psi> # \<Psi>))) \<preceq> (?\<gamma> # (remove1 ?\<gamma> \<Gamma>))"
        using stronger_theory_left_right_cons by auto
      hence "(map (uncurry (\<rightarrow>)) (\<psi> # \<Psi>) @ \<Gamma> \<ominus> (map snd (\<psi> # \<Psi>))) \<preceq> \<Gamma>"
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
        have "mset \<Psi> \<subseteq># mset \<Phi> + add_mset \<phi> (mset [])"
          using \<open>mset \<Psi> \<subseteq># mset (\<phi> # \<Phi>)\<close> by auto
        hence "mset \<Psi> \<subseteq># mset \<Phi>"
          by (metis (no_types) False
                               diff_single_trivial
                               in_multiset_in_set mset.simps(1)
                               subset_eq_diff_conv)
        then show ?thesis
          using \<open>\<Gamma> $\<turnstile> \<Phi>\<close> Cons
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
              "map (uncurry (\<squnion>)) \<Delta> :\<turnstile> \<phi>"
              "(map (uncurry (\<rightarrow>)) \<Delta> @ \<Gamma> \<ominus> (map snd \<Delta>)) $\<turnstile> \<Phi>"
          by auto
        ultimately have "(map (uncurry (\<rightarrow>)) \<Delta> @ \<Gamma> \<ominus> (map snd \<Delta>)) $\<turnstile> remove1 \<psi> \<Psi>"
          using Cons by blast
        moreover have "map (uncurry (\<squnion>)) \<Delta> :\<turnstile> \<psi>"
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
  shows "\<Gamma> $\<turnstile> (map (uncurry (\<squnion>)) \<Psi> @ map (uncurry (\<rightarrow>)) \<Psi> @ \<Phi> \<ominus> (map snd \<Psi>)) = \<Gamma> $\<turnstile> \<Phi>"
proof -
  have "\<forall> \<Gamma> \<Phi>. mset (map snd \<Psi>) \<subseteq># mset \<Phi> \<longrightarrow>
      \<Gamma> $\<turnstile> \<Phi> = \<Gamma> $\<turnstile> (map (uncurry (\<squnion>)) \<Psi> @ map (uncurry (\<rightarrow>)) \<Psi> @ \<Phi> \<ominus> (map snd \<Psi>))"
  proof (induct \<Psi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<psi> \<Psi>)
    {
      fix \<Gamma> \<Phi>
      let ?\<chi> = "fst \<psi>"
      let ?\<phi> = "snd \<psi>"
      let ?\<Phi>' = "map (uncurry (\<squnion>)) (\<psi> # \<Psi>) @
                 map (uncurry (\<rightarrow>)) (\<psi> # \<Psi>) @
                 \<Phi> \<ominus> map snd (\<psi> # \<Psi>)"
      let ?\<Phi>\<^sub>0 = "map (uncurry (\<squnion>)) \<Psi> @
                 map (uncurry (\<rightarrow>)) \<Psi> @
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
      have "(uncurry (\<squnion>)) = (\<lambda> \<psi>. fst \<psi> \<squnion> snd \<psi>)"
           "(uncurry (\<rightarrow>)) = (\<lambda> \<psi>. fst \<psi> \<rightarrow> snd \<psi>)"
        by fastforce+
      hence "mset ?\<Phi>' \<subseteq># mset (?\<chi> \<squnion> ?\<phi> # ?\<chi> \<rightarrow> ?\<phi> # ?\<Phi>\<^sub>0)"
            "mset (?\<chi> \<squnion> ?\<phi> # ?\<chi> \<rightarrow> ?\<phi> # ?\<Phi>\<^sub>0) \<subseteq># mset ?\<Phi>'"
            (is "mset ?X \<subseteq># mset ?Y")
        by fastforce+
      hence "\<Gamma> $\<turnstile> ?\<Phi>' = \<Gamma> $\<turnstile> (?\<phi> # ?\<Phi>\<^sub>0)"
        using segmented_formula_right_split
              segmented_msub_weaken
        by blast
      ultimately have "\<Gamma> $\<turnstile> \<Phi> = \<Gamma> $\<turnstile> ?\<Phi>'"
        by fastforce
    }
    then show ?case by blast
  qed
  with assms show ?thesis by blast
qed

primrec (in Classical_Propositional_Logic)
  submergeWitness :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" ("\<EE>")
  where
    "\<EE> \<Sigma> [] = map (\<lambda> \<sigma>. (\<bottom>, (uncurry (\<squnion>)) \<sigma>)) \<Sigma>"
  | "\<EE> \<Sigma> (\<delta> # \<Delta>) =
       (case find (\<lambda> \<sigma>. (uncurry (\<rightarrow>)) \<sigma> = snd \<delta>) \<Sigma> of
             None \<Rightarrow> \<EE> \<Sigma> \<Delta>
           | Some \<sigma> \<Rightarrow> (fst \<sigma>, (fst \<delta> \<sqinter> fst \<sigma>) \<squnion> snd \<sigma>) # (\<EE> (remove1 \<sigma> \<Sigma>) \<Delta>))"

lemma (in Classical_Propositional_Logic) submergeWitness_stronger_theory_left:
   "map (uncurry (\<squnion>)) \<Sigma> \<preceq> map (uncurry (\<squnion>)) (\<EE> \<Sigma> \<Delta>)"
proof -
  have "\<forall> \<Sigma>. map (uncurry (\<squnion>)) \<Sigma> \<preceq> map (uncurry (\<squnion>)) (\<EE> \<Sigma> \<Delta>)"
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
      have "map (uncurry (\<squnion>)) \<Sigma> \<preceq> map (uncurry (\<squnion>)) (\<EE> \<Sigma> [])"
        by (induct \<Sigma>,
            simp,
            simp add: stronger_theory_left_right_cons tautology)
    }
    then show ?case by auto
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Sigma>
      have "map (uncurry (\<squnion>)) \<Sigma> \<preceq> map (uncurry (\<squnion>)) (\<EE> \<Sigma> (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<sigma>. (uncurry (\<rightarrow>)) \<sigma> = snd \<delta>) \<Sigma> = None")
        case True
        then show ?thesis using Cons by simp
      next
        case False
        from this obtain \<sigma> where
          \<sigma>: "find (\<lambda>\<sigma>. uncurry (\<rightarrow>) \<sigma> = snd \<delta>) \<Sigma> = Some \<sigma>"
             "uncurry (\<rightarrow>) \<sigma> = snd \<delta>"
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
        have "(uncurry (\<squnion>)) = (\<lambda> \<sigma>. fst \<sigma> \<squnion> snd \<sigma>)" by fastforce
        hence "(uncurry (\<squnion>)) \<sigma> = ?\<alpha> \<squnion> ?\<beta>" by simp
        hence "\<turnstile> (?\<alpha> \<squnion> (?\<gamma> \<sqinter> ?\<alpha>) \<squnion> ?\<beta>) \<rightarrow> (uncurry (\<squnion>)) \<sigma>" using tautology by simp
        moreover
        have "map (uncurry (\<squnion>)) (remove1 \<sigma> \<Sigma>)
             \<preceq> map (uncurry (\<squnion>)) (\<EE> (remove1 \<sigma> \<Sigma>) \<Delta>)"
          using Cons by simp
        ultimately have
          "map (uncurry (\<squnion>)) (\<sigma> # (remove1 \<sigma> \<Sigma>))
           \<preceq> (?\<alpha> \<squnion> (?\<gamma> \<sqinter> ?\<alpha>) \<squnion> ?\<beta> # map (uncurry (\<squnion>)) (\<EE> (remove1 \<sigma> \<Sigma>) \<Delta>))"
          apply simp
          using stronger_theory_left_right_cons by blast
        moreover from \<sigma>(3) have "mset \<Sigma> = mset (\<sigma> # (remove1 \<sigma> \<Sigma>))"
          by simp
        hence "mset (map (uncurry (\<squnion>)) \<Sigma>) = mset (map (uncurry (\<squnion>)) (\<sigma> # (remove1 \<sigma> \<Sigma>)))"
          by (metis mset_map)
        hence "map (uncurry (\<squnion>)) \<Sigma> \<preceq> map (uncurry (\<squnion>)) (\<sigma> # (remove1 \<sigma> \<Sigma>))"
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
  "mset (map snd (\<EE> \<Sigma> \<Delta>)) \<subseteq># mset (map (uncurry (\<squnion>)) (\<JJ> \<Sigma> \<Delta>))"
proof -
  have "\<forall> \<Sigma>. mset (map snd (\<EE> \<Sigma> \<Delta>)) \<subseteq># mset (map (uncurry (\<squnion>)) (\<JJ> \<Sigma> \<Delta>))"
  proof (induct \<Delta>)
    case Nil
    {
      fix \<Sigma>
      have "mset (map snd (\<EE> \<Sigma> [])) \<subseteq>#
            mset (map (uncurry (\<squnion>)) (\<JJ> \<Sigma> []))"
        by (induct \<Sigma>, simp+)
    }
    then show ?case by blast
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Sigma>
      have "mset (map snd (\<EE> \<Sigma> (\<delta> # \<Delta>))) \<subseteq>#
            mset (map (uncurry (\<squnion>)) (\<JJ> \<Sigma> (\<delta> # \<Delta>)))"
        using Cons
        by (cases "find (\<lambda> \<sigma>. (uncurry (\<rightarrow>)) \<sigma> = snd \<delta>) \<Sigma> = None",
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
   "map (uncurry (\<squnion>)) \<Delta>
 \<preceq> (map (uncurry (\<rightarrow>)) (\<EE> \<Sigma> \<Delta>) @ map (uncurry (\<squnion>)) (\<JJ> \<Sigma> \<Delta>) \<ominus> map snd (\<EE> \<Sigma> \<Delta>))"
proof -
  have "\<forall> \<Sigma>. map (uncurry (\<squnion>)) \<Delta>
          \<preceq> (map (uncurry (\<rightarrow>)) (\<EE> \<Sigma> \<Delta>) @ map (uncurry (\<squnion>)) (\<JJ> \<Sigma> \<Delta>)  \<ominus> map snd (\<EE> \<Sigma> \<Delta>))"
  proof(induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Sigma>
      have "map (uncurry (\<squnion>)) (\<delta> # \<Delta>) \<preceq>
           (  map (uncurry (\<rightarrow>)) (\<EE> \<Sigma> (\<delta> # \<Delta>))
            @ map (uncurry (\<squnion>)) (\<JJ> \<Sigma> (\<delta> # \<Delta>))
               \<ominus> map snd (\<EE> \<Sigma> (\<delta> # \<Delta>)))"
      proof (cases "find (\<lambda> \<sigma>. (uncurry (\<rightarrow>)) \<sigma> = snd \<delta>) \<Sigma> = None")
        case True
        from Cons obtain \<Phi> where \<Phi>:
          "map snd \<Phi> = map (uncurry (\<squnion>)) \<Delta>"
          "mset (map fst \<Phi>) \<subseteq>#
             mset (map (uncurry (\<rightarrow>)) (\<EE> \<Sigma> \<Delta>)
                   @ map (uncurry (\<squnion>)) (\<JJ> \<Sigma> \<Delta>) \<ominus> map snd (\<EE> \<Sigma> \<Delta>))"
          "\<forall>(\<gamma>, \<sigma>)\<in>set \<Phi>. \<turnstile> \<gamma> \<rightarrow> \<sigma>"
          unfolding stronger_theory_relation_def
          by fastforce
        let ?\<Phi>' = "(uncurry (\<squnion>) \<delta>, (uncurry (\<squnion>)) \<delta>) # \<Phi>"
        have "map snd ?\<Phi>' = map (uncurry (\<squnion>)) (\<delta> # \<Delta>)" using \<Phi>(1) by simp
        moreover
        from \<Phi>(2) have A:
          "image_mset fst (mset \<Phi>)
        \<subseteq># {#x \<rightarrow> y. (x, y) \<in># mset (\<EE> \<Sigma> \<Delta>)#}
           + ({#x \<squnion> y. (x, y) \<in># mset (\<JJ> \<Sigma> \<Delta>)#} - image_mset snd (mset (\<EE> \<Sigma> \<Delta>)))"
          by simp
        have "image_mset snd (mset (\<EE> \<Sigma> \<Delta>)) \<subseteq># {#x \<squnion> y. (x, y) \<in># mset (\<JJ> \<Sigma> \<Delta>)#}"
          using submergeWitness_msub by force
        then have B: "{#case \<delta> of (x, xa) \<Rightarrow> x \<squnion> xa#}
                   \<subseteq># add_mset (case \<delta> of (x, xa) \<Rightarrow> x \<squnion> xa)
                               {#x \<squnion> y. (x, y) \<in># mset (\<JJ> \<Sigma> \<Delta>)#} - image_mset snd (mset (\<EE> \<Sigma> \<Delta>))"
          by (metis add_mset_add_single subset_mset.le_add_diff)
        have "add_mset (case \<delta> of (x, xa) \<Rightarrow> x \<squnion> xa) {#x \<squnion> y. (x, y) \<in># mset (\<JJ> \<Sigma> \<Delta>)#}
              - image_mset snd (mset (\<EE> \<Sigma> \<Delta>)) - {#case \<delta> of (x, xa) \<Rightarrow> x \<squnion> xa#}
            = {#x \<squnion> y. (x, y) \<in># mset (\<JJ> \<Sigma> \<Delta>)#} - image_mset snd (mset (\<EE> \<Sigma> \<Delta>))"
          by force
        then have "add_mset (case \<delta> of (x, xa) \<Rightarrow> x \<squnion> xa) (image_mset fst (mset \<Phi>))
                  - (add_mset (case \<delta> of (x, xa) \<Rightarrow> x \<squnion> xa) {#x \<squnion> y. (x, y) \<in># mset (\<JJ> \<Sigma> \<Delta>)#}
                  - image_mset snd (mset (\<EE> \<Sigma> \<Delta>)))
               \<subseteq># {#x \<rightarrow> y. (x, y) \<in># mset (\<EE> \<Sigma> \<Delta>)#}"
          using A B by (metis (no_types) add_mset_add_single
                                         subset_eq_diff_conv
                                         subset_mset.diff_diff_right)
        hence "add_mset (case \<delta> of (x, xa) \<Rightarrow> x \<squnion> xa) (image_mset fst (mset \<Phi>))
           \<subseteq># {#x \<rightarrow> y. (x, y) \<in># mset (\<EE> \<Sigma> \<Delta>)#}
              + (add_mset (case \<delta> of (x, xa) \<Rightarrow> x \<squnion> xa) {#x \<squnion> y. (x, y) \<in># mset (\<JJ> \<Sigma> \<Delta>)#}
              - image_mset snd (mset (\<EE> \<Sigma> \<Delta>)))"
          using subset_eq_diff_conv by blast
        hence
          "mset (map fst ?\<Phi>') \<subseteq>#
             mset (map (uncurry (\<rightarrow>)) (\<EE> \<Sigma> (\<delta> # \<Delta>))
                   @ map (uncurry (\<squnion>)) (\<JJ> \<Sigma> (\<delta> # \<Delta>))
                      \<ominus> map snd (\<EE> \<Sigma> (\<delta> # \<Delta>)))"
          using True \<Phi>(2)
          by simp
        moreover have "\<forall>(\<gamma>, \<sigma>)\<in>set ?\<Phi>'. \<turnstile> \<gamma> \<rightarrow> \<sigma>"
          using \<Phi>(3) trivial_implication by auto
        ultimately show ?thesis
          unfolding stronger_theory_relation_def
          by blast
      next
        case False
        from this obtain \<sigma> where
          \<sigma>: "find (\<lambda>\<sigma>. uncurry (\<rightarrow>) \<sigma> = snd \<delta>) \<Sigma> = Some \<sigma>"
             "uncurry (\<rightarrow>) \<sigma> = snd \<delta>"
          using find_Some_predicate
          by fastforce
        moreover from Cons have
          "map (uncurry (\<squnion>)) \<Delta> \<preceq>
          (map (uncurry (\<rightarrow>)) (\<EE> (remove1 \<sigma> \<Sigma>) \<Delta>) @
            remove1 ((fst \<delta> \<sqinter> fst \<sigma>) \<squnion> snd \<sigma>)
             (((fst \<delta> \<sqinter> fst \<sigma>) \<squnion> snd \<sigma> # map (uncurry (\<squnion>)) (\<JJ> (remove1 \<sigma> \<Sigma>) \<Delta>))
                \<ominus> map snd (\<EE> (remove1 \<sigma> \<Sigma>) \<Delta>)))"
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
        have "(\<lambda> \<delta>. uncurry (\<squnion>) \<delta>) = (\<lambda> \<delta>. fst \<delta> \<squnion> snd \<delta>)"
             "(\<lambda> \<sigma>. uncurry (\<rightarrow>) \<sigma>) = (\<lambda> \<sigma>. fst \<sigma> \<rightarrow> snd \<sigma>)" by fastforce+
        hence "(uncurry (\<squnion>) \<delta>) = (?\<gamma> \<squnion> (?\<alpha> \<rightarrow> ?\<beta>))" using \<sigma>(2) by simp
        hence "\<turnstile> (?\<alpha> \<rightarrow> ((?\<gamma> \<sqinter> ?\<alpha>) \<squnion> ?\<beta>)) \<rightarrow> (uncurry (\<squnion>) \<delta>)" using tautology by auto
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
  assumes "map (uncurry (\<squnion>)) \<Sigma> :\<turnstile> \<phi>"
      and "mset (map snd \<Delta>) \<subseteq># mset (map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma>)"
      and "map (uncurry (\<squnion>)) \<Delta> $\<turnstile> \<Phi>"
    shows "map (uncurry (\<squnion>)) (\<JJ> \<Sigma> \<Delta>) $\<turnstile> (\<phi> # \<Phi>)"
proof -
  let ?\<Sigma>' = "\<EE> \<Sigma> \<Delta>"
  let ?\<Gamma> = "map (uncurry (\<rightarrow>)) ?\<Sigma>' @ map (uncurry (\<squnion>)) (\<JJ> \<Sigma> \<Delta>) \<ominus> map snd ?\<Sigma>'"
  have "?\<Gamma> $\<turnstile> \<Phi>"
    using assms(3)
          submergeWitness_stronger_theory_right
          segmented_stronger_theory_left_monotonic
    by blast
  moreover have "map (uncurry (\<squnion>)) ?\<Sigma>' :\<turnstile> \<phi>"
    using assms(1)
          stronger_theory_deduction_monotonic
          submergeWitness_stronger_theory_left
    by blast
  ultimately show ?thesis
    using submergeWitness_msub
    by fastforce
qed

primrec (in Classical_Propositional_Logic)
  recoverWitnessA :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" ("\<PP>")
  where
    "\<PP> \<Sigma> [] = \<Sigma>"
  | "\<PP> \<Sigma> (\<delta> # \<Delta>) =
       (case find (\<lambda> \<sigma>. snd \<sigma> = (uncurry (\<squnion>)) \<delta>) \<Sigma> of
             None \<Rightarrow> \<PP> \<Sigma> \<Delta>
           | Some \<sigma> \<Rightarrow> (fst \<sigma> \<squnion> fst \<delta>, snd \<delta>) # (\<PP> (remove1 \<sigma> \<Sigma>) \<Delta>))"

primrec (in Classical_Propositional_Logic)
  recoverComplementA :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" ("\<PP>\<^sup>C")
  where
    "\<PP>\<^sup>C \<Sigma> [] = []"
  | "\<PP>\<^sup>C \<Sigma> (\<delta> # \<Delta>) =
       (case find (\<lambda> \<sigma>. snd \<sigma> = (uncurry (\<squnion>)) \<delta>) \<Sigma> of
             None \<Rightarrow> \<delta> # \<PP>\<^sup>C \<Sigma> \<Delta>
           | Some \<sigma> \<Rightarrow> (\<PP>\<^sup>C (remove1 \<sigma> \<Sigma>) \<Delta>))"

primrec (in Classical_Propositional_Logic)
  recoverWitnessB :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" ("\<QQ>")
  where
    "\<QQ> \<Sigma> [] = []"
  | "\<QQ> \<Sigma> (\<delta> # \<Delta>) =
       (case find (\<lambda> \<sigma>. (snd \<sigma>) = (uncurry (\<squnion>)) \<delta>) \<Sigma> of
             None \<Rightarrow> \<delta> # \<QQ> \<Sigma> \<Delta>
           | Some \<sigma> \<Rightarrow> (fst \<delta>, (fst \<sigma> \<squnion> fst \<delta>) \<rightarrow> snd \<delta>) # (\<QQ> (remove1 \<sigma> \<Sigma>) \<Delta>))"

lemma (in Classical_Propositional_Logic) recoverWitnessA_left_stronger_theory:
  "map (uncurry (\<squnion>)) \<Sigma> \<preceq> map (uncurry (\<squnion>)) (\<PP> \<Sigma> \<Delta>)"
proof -
  have "\<forall> \<Sigma>. map (uncurry (\<squnion>)) \<Sigma> \<preceq> map (uncurry (\<squnion>)) (\<PP> \<Sigma> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    {
      fix \<Sigma>
      have "map (uncurry (\<squnion>)) \<Sigma> \<preceq> map (uncurry (\<squnion>)) (\<PP> \<Sigma> [])"
        by(induct \<Sigma>, simp+)
    }
    then show ?case by auto
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Sigma>
      have "map (uncurry (\<squnion>)) \<Sigma> \<preceq> map (uncurry (\<squnion>)) (\<PP> \<Sigma> (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<sigma>. snd \<sigma> = uncurry (\<squnion>) \<delta>) \<Sigma> = None")
        case True
        then show ?thesis using Cons by simp
      next
        case False
        from this obtain \<sigma> where
          \<sigma>: "find (\<lambda>\<sigma>. snd \<sigma> = uncurry (\<squnion>) \<delta>) \<Sigma> = Some \<sigma>"
             "snd \<sigma> = uncurry (\<squnion>) \<delta>"
             "\<sigma> \<in> set \<Sigma>"
          using find_Some_predicate
                find_Some_set_membership
          by fastforce
        let ?\<alpha> = "fst \<sigma>"
        let ?\<beta> = "fst \<delta>"
        let ?\<gamma> = "snd \<delta>"
        have "uncurry (\<squnion>) = (\<lambda>\<delta>. fst \<delta> \<squnion> snd \<delta>)" by fastforce
        hence "\<turnstile> ((?\<alpha> \<squnion> ?\<beta>) \<squnion> ?\<gamma>) \<rightarrow> uncurry (\<squnion>) \<sigma>"
          using \<sigma>(2) biconditional_def disjunction_associativity
          by auto
        moreover
        have "map (uncurry (\<squnion>)) (remove1 \<sigma> \<Sigma>)
            \<preceq> map (uncurry (\<squnion>)) (\<PP> (remove1 \<sigma> \<Sigma>) \<Delta>)"
          using Cons by simp
        ultimately have "map (uncurry (\<squnion>)) (\<sigma> # (remove1 \<sigma> \<Sigma>))
                       \<preceq> map (uncurry (\<squnion>)) (\<PP> \<Sigma> (\<delta> # \<Delta>))"
          using \<sigma>(1)
          by (simp, metis stronger_theory_left_right_cons)
        moreover
        from \<sigma>(3) have "mset \<Sigma> = mset (\<sigma> # (remove1 \<sigma> \<Sigma>))"
          by simp
        hence "mset (map (uncurry (\<squnion>)) \<Sigma>) = mset (map (uncurry (\<squnion>)) (\<sigma> # (remove1 \<sigma> \<Sigma>)))"
          by (metis mset_map)
        hence "map (uncurry (\<squnion>)) \<Sigma> \<preceq> map (uncurry (\<squnion>)) (\<sigma> # (remove1 \<sigma> \<Sigma>))"
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
  assumes "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>)"
  shows "mset (map snd (\<PP> \<Sigma> \<Delta> @ \<PP>\<^sup>C \<Sigma> \<Delta>)) = mset (map snd \<Delta>)"
proof -
  have "\<forall> \<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>)
         \<longrightarrow> mset (map snd (\<PP> \<Sigma> \<Delta> @ \<PP>\<^sup>C \<Sigma> \<Delta>)) = mset (map snd \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Sigma> :: "('a \<times> 'a) list"
      assume \<star>: "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry (\<squnion>)) (\<delta> # \<Delta>))"
      have "mset (map snd (\<PP> \<Sigma> (\<delta> # \<Delta>) @ \<PP>\<^sup>C \<Sigma> (\<delta> # \<Delta>))) = mset (map snd (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<sigma>. snd \<sigma> = uncurry (\<squnion>) \<delta>) \<Sigma> = None")
        case True
        hence "uncurry (\<squnion>) \<delta> \<notin> set (map snd \<Sigma>)"
        proof (induct \<Sigma>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<sigma> \<Sigma>)
          then show ?case
            by (cases "(uncurry (\<squnion>)) \<delta> = snd \<sigma>", fastforce+)
        qed
        moreover have "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>) + {#uncurry (\<squnion>) \<delta>#}"
          using \<star> by fastforce
        ultimately have "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>)"
          by (metis diff_single_trivial
                    in_multiset_in_set
                    subset_eq_diff_conv)
        then show ?thesis using Cons True by simp
      next
        case False
        from this obtain \<sigma> where
          \<sigma>: "find (\<lambda>\<sigma>. snd \<sigma> = uncurry (\<squnion>) \<delta>) \<Sigma> = Some \<sigma>"
             "snd \<sigma> = uncurry (\<squnion>) \<delta>"
             "\<sigma> \<in> set \<Sigma>"
          using find_Some_predicate
                find_Some_set_membership
          by fastforce
        have A: "mset (map snd \<Sigma>)
              \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>) + add_mset (uncurry (\<squnion>) \<delta>) (mset [])"
          using \<star> by auto
        have "(fst \<sigma>, uncurry (\<squnion>) \<delta>) \<in># mset \<Sigma>"
          by (metis (no_types) \<sigma>(2) \<sigma>(3) prod.collapse set_mset_mset)
        then have B: "mset (map snd (remove1 (fst \<sigma>, uncurry (\<squnion>) \<delta>) \<Sigma>))
                    = mset (map snd \<Sigma>) - {#uncurry (\<squnion>) \<delta>#}"
          by (meson remove1_pairs_list_projections_snd)
        have "(fst \<sigma>, uncurry (\<squnion>) \<delta>) = \<sigma>"
          by (metis \<sigma>(2) prod.collapse)
        then have "mset (map snd \<Sigma>) - add_mset (uncurry (\<squnion>) \<delta>) (mset [])
                 = mset (map snd (remove1 \<sigma> \<Sigma>))"
          using B by simp
        hence "mset (map snd (remove1 \<sigma> \<Sigma>)) \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>)"
          using A by (metis (no_types) subset_eq_diff_conv)
        with \<sigma>(1) Cons show ?thesis by simp
      qed
    }
    then show ?case by simp
  qed
  with assms show ?thesis by blast
qed

lemma (in Classical_Propositional_Logic) recoverWitnessB_stronger_theory:
  assumes "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>)"
  shows "(map (uncurry (\<rightarrow>)) \<Sigma> @ map (uncurry (\<squnion>)) \<Delta> \<ominus> map snd \<Sigma>)
         \<preceq> map (uncurry (\<squnion>)) (\<QQ> \<Sigma> \<Delta>)"
proof -
  have "\<forall> \<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>)
        \<longrightarrow> (map (uncurry (\<rightarrow>)) \<Sigma> @ map (uncurry (\<squnion>)) \<Delta> \<ominus> map snd \<Sigma>)
            \<preceq> map (uncurry (\<squnion>)) (\<QQ> \<Sigma> \<Delta>)"
  proof(induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Sigma> :: "('a \<times> 'a) list"
      assume \<star>: "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry (\<squnion>)) (\<delta> # \<Delta>))"
      have "(map (uncurry (\<rightarrow>)) \<Sigma> @ map (uncurry (\<squnion>)) (\<delta> # \<Delta>) \<ominus> map snd \<Sigma>)
            \<preceq> map (uncurry (\<squnion>)) (\<QQ> \<Sigma> (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<sigma>. snd \<sigma> = uncurry (\<squnion>) \<delta>) \<Sigma> = None")
        case True
        hence "uncurry (\<squnion>) \<delta> \<notin> set (map snd \<Sigma>)"
        proof (induct \<Sigma>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<sigma> \<Sigma>)
          then show ?case
            by (cases "uncurry (\<squnion>) \<delta> = snd \<sigma>", fastforce+)
        qed
        hence "mset (map (uncurry (\<rightarrow>)) \<Sigma> @ (map (uncurry (\<squnion>)) (\<delta> # \<Delta>)) \<ominus> map snd \<Sigma>)
             = mset (uncurry (\<squnion>) \<delta> # map (uncurry (\<rightarrow>)) \<Sigma>
                     @ map (uncurry (\<squnion>)) \<Delta> \<ominus> map snd \<Sigma>)"
              "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>)"
          using \<star>
          by (simp, simp,
              metis add_mset_add_single
                    diff_single_trivial
                    image_set
                    mset_map
                    set_mset_mset
                    subset_eq_diff_conv)
        moreover from this have
          "(map (uncurry (\<rightarrow>)) \<Sigma> @ map (uncurry (\<squnion>)) \<Delta> \<ominus> map snd \<Sigma>)
           \<preceq> map (uncurry (\<squnion>)) (\<QQ> \<Sigma> \<Delta>)"
          using Cons
          by auto
        hence "(uncurry (\<squnion>) \<delta> # map (uncurry (\<rightarrow>)) \<Sigma> @ map (uncurry (\<squnion>)) \<Delta> \<ominus> map snd \<Sigma>)
               \<preceq> map (uncurry (\<squnion>)) (\<QQ> \<Sigma> (\<delta> # \<Delta>))"
          using True
          by (simp add: stronger_theory_left_right_cons trivial_implication)
        ultimately show ?thesis
          unfolding stronger_theory_relation_alt_def
          by simp
      next
        case False
        let ?\<Gamma> = "map (uncurry (\<rightarrow>)) \<Sigma> @ (map (uncurry (\<squnion>)) (\<delta> # \<Delta>)) \<ominus> map snd \<Sigma>"
        from False obtain \<sigma> where
          \<sigma>: "find (\<lambda>\<sigma>. snd \<sigma> = uncurry (\<squnion>) \<delta>) \<Sigma> = Some \<sigma>"
             "snd \<sigma> = uncurry (\<squnion>) \<delta>"
             "\<sigma> \<in> set \<Sigma>"
          using find_Some_predicate
                find_Some_set_membership
          by fastforce
        let ?\<Gamma>\<^sub>0 = "map (uncurry (\<rightarrow>)) (remove1 \<sigma> \<Sigma>)
                    @ (map (uncurry (\<squnion>)) \<Delta>) \<ominus> map snd (remove1 \<sigma> \<Sigma>)"
        let ?\<alpha> = "fst \<sigma>"
        let ?\<beta> = "fst \<delta>"
        let ?\<gamma> = "snd \<delta>"
        have "uncurry (\<squnion>) = (\<lambda> \<sigma>. fst \<sigma> \<squnion> snd \<sigma>)"
             "uncurry (\<rightarrow>) = (\<lambda> \<sigma>. fst \<sigma> \<rightarrow> snd \<sigma>)"
          by fastforce+
        hence "uncurry (\<rightarrow>) \<sigma> = ?\<alpha> \<rightarrow> (?\<beta> \<squnion> ?\<gamma>)"
          using \<sigma>(2)
          by simp
        from \<sigma>(3) have "mset (\<sigma> # (remove1 \<sigma> \<Sigma>)) = mset \<Sigma>" by simp
        hence \<spadesuit>: "mset (map snd (\<sigma> # (remove1 \<sigma> \<Sigma>))) = mset (map snd \<Sigma>)"
                 "mset (map (uncurry (\<rightarrow>)) (\<sigma> # (remove1 \<sigma> \<Sigma>))) = mset (map (uncurry (\<rightarrow>)) \<Sigma>)"
          by (metis mset_map)+
        hence "mset ?\<Gamma> = mset (map (uncurry (\<rightarrow>)) (\<sigma> # (remove1 \<sigma> \<Sigma>))
                                   @ (uncurry (\<squnion>) \<delta> # map (uncurry (\<squnion>)) \<Delta>)
                                        \<ominus> map snd (\<sigma> # (remove1 \<sigma> \<Sigma>)))"
          by simp
        hence "?\<Gamma> \<preceq> (?\<alpha> \<rightarrow> (?\<beta> \<squnion> ?\<gamma>) # ?\<Gamma>\<^sub>0)"
          using \<sigma>(2) \<open>uncurry (\<rightarrow>) \<sigma> = ?\<alpha> \<rightarrow> (?\<beta> \<squnion> ?\<gamma>)\<close>
          by (simp add: msub_stronger_theory_intro)
        moreover have "mset (map snd (remove1 \<sigma> \<Sigma>)) \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>)"
          using \<spadesuit>(1)
          by (simp,
              metis (no_types, lifting)
                    \<star> \<sigma>(2)
                    list.simps(9)
                    mset.simps(2)
                    mset_map
                    uncurry_def
                    mset_subset_eq_add_mset_cancel)
        with Cons have \<heartsuit>: "?\<Gamma>\<^sub>0 \<preceq> map (uncurry (\<squnion>)) (\<QQ> (remove1 \<sigma> \<Sigma>) \<Delta>)" by simp
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
        hence "(?\<alpha> \<rightarrow> (?\<beta> \<squnion> ?\<gamma>) # ?\<Gamma>\<^sub>0) \<preceq> map (uncurry (\<squnion>)) (\<QQ> \<Sigma> (\<delta> # \<Delta>))"
          using \<sigma>(1) \<heartsuit>
          by (simp, metis stronger_theory_left_right_cons)
        ultimately show ?thesis
          using stronger_theory_transitive by blast
      qed
    }
    then show ?case by simp
  qed
  thus ?thesis using assms by blast
qed

lemma (in Classical_Propositional_Logic) recoverWitnessB_mset_equiv:
  assumes "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>)"
  shows "mset (map snd (\<QQ> \<Sigma> \<Delta>))
       = mset (map (uncurry (\<rightarrow>)) (\<PP> \<Sigma> \<Delta>) @ map snd \<Delta> \<ominus> map snd (\<PP> \<Sigma> \<Delta>))"
proof -
  have "\<forall> \<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>)
       \<longrightarrow>   mset (map snd (\<QQ> \<Sigma> \<Delta>)) = mset (map (uncurry (\<rightarrow>)) (\<PP> \<Sigma> \<Delta>) @ map snd (\<PP>\<^sup>C \<Sigma> \<Delta>))"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Sigma> :: "('a \<times> 'a) list"
      assume \<star>: "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry (\<squnion>)) (\<delta> # \<Delta>))"
      have "mset (map snd (\<QQ> \<Sigma> (\<delta> # \<Delta>)))
         =  mset (map (uncurry (\<rightarrow>)) (\<PP> \<Sigma> (\<delta> # \<Delta>)) @ map snd (\<PP>\<^sup>C \<Sigma> (\<delta> # \<Delta>)))"
      proof (cases "find (\<lambda> \<sigma>. snd \<sigma> = uncurry (\<squnion>) \<delta>) \<Sigma> = None")
        case True
        hence "uncurry (\<squnion>) \<delta> \<notin> set (map snd \<Sigma>)"
        proof (induct \<Sigma>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<sigma> \<Sigma>)
          then show ?case
            by (cases "(uncurry (\<squnion>)) \<delta> = snd \<sigma>", fastforce+)
        qed
        moreover have "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>) + {#uncurry (\<squnion>) \<delta>#}"
          using \<star> by force
        ultimately have "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>)"
          by (metis diff_single_trivial in_multiset_in_set subset_eq_diff_conv)
        then show ?thesis using True Cons by simp
      next
        case False
        from this obtain \<sigma> where
          \<sigma>: "find (\<lambda>\<sigma>. snd \<sigma> = uncurry (\<squnion>) \<delta>) \<Sigma> = Some \<sigma>"
             "snd \<sigma> = uncurry (\<squnion>) \<delta>"
             "\<sigma> \<in> set \<Sigma>"
          using find_Some_predicate
                find_Some_set_membership
          by fastforce
        hence "(fst \<sigma>, uncurry (\<squnion>) \<delta>) \<in># mset \<Sigma>"
          by (metis (full_types) prod.collapse set_mset_mset)
        then have "mset (map snd (remove1 (fst \<sigma>, uncurry (\<squnion>) \<delta>) \<Sigma>))
                 = mset (map snd \<Sigma>) - {#uncurry (\<squnion>) \<delta>#}"
          by (meson remove1_pairs_list_projections_snd)
        moreover have
        "mset (map snd \<Sigma>)
     \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>) + add_mset (uncurry (\<squnion>) \<delta>) (mset [])"
          using \<star> by force
        ultimately have "mset (map snd (remove1 \<sigma> \<Sigma>))
            \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>)"
          by (metis (no_types) \<sigma>(2) mset.simps(1) prod.collapse subset_eq_diff_conv)
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
  "map (uncurry (\<rightarrow>)) \<Delta> \<preceq> map (uncurry (\<rightarrow>)) (\<QQ> \<Sigma> \<Delta>)"
proof -
  have "\<forall> \<Sigma>. map (uncurry (\<rightarrow>)) \<Delta> \<preceq> map (uncurry (\<rightarrow>)) (\<QQ> \<Sigma> \<Delta>)"
  proof (induct \<Delta>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Sigma>
      have "map (uncurry (\<rightarrow>)) (\<delta> # \<Delta>) \<preceq> map (uncurry (\<rightarrow>)) (\<QQ> \<Sigma> (\<delta> # \<Delta>))"
      proof (cases "find (\<lambda> \<sigma>. snd \<sigma> = uncurry (\<squnion>) \<delta>) \<Sigma> = None")
        case True
        then show ?thesis
          using Cons
          by (simp add: stronger_theory_left_right_cons trivial_implication)
      next
        case False
        from this obtain \<sigma> where \<sigma>:
          "find (\<lambda>\<sigma>. snd \<sigma> = uncurry (\<squnion>) \<delta>) \<Sigma> = Some \<sigma>"
          by fastforce
        let ?\<alpha> = "fst \<delta>"
        let ?\<beta> = "snd \<delta>"
        let ?\<gamma> = "fst \<sigma>"
        have "uncurry (\<rightarrow>) = (\<lambda>\<delta>. fst \<delta> \<rightarrow> snd \<delta>)" by fastforce
        hence "uncurry (\<rightarrow>) \<delta> = ?\<alpha> \<rightarrow> ?\<beta>" by auto
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
      and "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>)"
    shows "mset (\<Gamma> \<ominus> map snd \<Delta>)
         = mset ((map (uncurry (\<rightarrow>)) (\<PP> \<Sigma> \<Delta>) @ \<Gamma> \<ominus> map snd (\<PP> \<Sigma> \<Delta>)) \<ominus> map snd (\<QQ> \<Sigma> \<Delta>))"
proof -
  have "mset (\<Gamma> \<ominus> map snd \<Delta>) = mset (\<Gamma> \<ominus> map snd (\<PP>\<^sup>C \<Sigma> \<Delta>) \<ominus> map snd (\<PP> \<Sigma> \<Delta>))"
    using assms(2) recoverWitnessA_mset_equiv
    by (simp add: union_commute)
  moreover have "\<forall> \<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>)
                  \<longrightarrow> mset (\<Gamma> \<ominus> map snd (\<PP>\<^sup>C \<Sigma> \<Delta>))
                    = (mset ((map (uncurry (\<rightarrow>)) (\<PP> \<Sigma> \<Delta>) @ \<Gamma>) \<ominus> map snd (\<QQ> \<Sigma> \<Delta>)))"
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
      assume \<star>: "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry (\<squnion>)) (\<delta> # \<Delta>))"
      have "mset (\<Gamma> \<ominus> map snd (\<PP>\<^sup>C \<Sigma> (\<delta> # \<Delta>)))
          = mset ((map (uncurry (\<rightarrow>)) (\<PP> \<Sigma> (\<delta> # \<Delta>)) @ \<Gamma>) \<ominus> map snd (\<QQ> \<Sigma> (\<delta> # \<Delta>)))"
      proof (cases "find (\<lambda> \<sigma>. snd \<sigma> = uncurry (\<squnion>) \<delta>) \<Sigma> = None")
        case True
        hence "uncurry (\<squnion>) \<delta> \<notin> set (map snd \<Sigma>)"
        proof (induct \<Sigma>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<sigma> \<Sigma>)
          then show ?case
            by (cases "(uncurry (\<squnion>)) \<delta> = snd \<sigma>", fastforce+)
        qed
        moreover have "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>) + {#uncurry (\<squnion>) \<delta>#}"
          using \<star> by auto
        ultimately have "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>)"
          by (metis (full_types) diff_single_trivial in_multiset_in_set subset_eq_diff_conv)
        with Cons.hyps \<heartsuit> have "mset (\<Gamma> \<ominus> map snd (\<PP>\<^sup>C \<Sigma> \<Delta>))
                             = mset ((map (uncurry (\<rightarrow>)) (\<PP> \<Sigma> \<Delta>) @ \<Gamma>) \<ominus> map snd (\<QQ> \<Sigma> \<Delta>))"
          by simp
        thus ?thesis using True \<open>snd \<delta> \<in> set \<Gamma>\<close> by simp
      next
        case False
        from this obtain \<sigma> where \<sigma>:
          "find (\<lambda>\<sigma>. snd \<sigma> = uncurry (\<squnion>) \<delta>) \<Sigma> = Some \<sigma>"
          "snd \<sigma> = uncurry (\<squnion>) \<delta>"
          "\<sigma> \<in> set \<Sigma>"
          using find_Some_predicate
                find_Some_set_membership
          by fastforce
        with \<star> have "mset (map snd (remove1 \<sigma> \<Sigma>)) \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>)"
          by (simp, metis (no_types, lifting)
                          add_mset_remove_trivial_eq
                          image_mset_add_mset
                          in_multiset_in_set
                          mset_subset_eq_add_mset_cancel)
        with Cons.hyps have "mset (\<Gamma> \<ominus> map snd (\<PP>\<^sup>C (remove1 \<sigma> \<Sigma>) \<Delta>))
                           = mset ((map (uncurry (\<rightarrow>)) (\<PP> (remove1 \<sigma> \<Sigma>) \<Delta>) @ \<Gamma>)
                                   \<ominus> map snd (\<QQ> (remove1 \<sigma> \<Sigma>) \<Delta>))"
          using \<heartsuit> by blast
        then show ?thesis using \<sigma> by simp
      qed
    }
    then show ?case by blast
  qed
  moreover have "image_mset snd (mset (\<PP>\<^sup>C \<Sigma> \<Delta>)) = mset (map snd \<Delta> \<ominus> map snd (\<PP> \<Sigma> \<Delta>))"
    using assms(2) recoverWitnessA_mset_equiv
    by (simp, metis (no_types) diff_union_cancelL listSubtract_mset_homomorphism mset_map)
  then have "mset \<Gamma> - (image_mset snd (mset (\<PP>\<^sup>C \<Sigma> \<Delta>)) + image_mset snd (mset (\<PP> \<Sigma> \<Delta>)))
          = {#x \<rightarrow> y. (x, y) \<in># mset (\<PP> \<Sigma> \<Delta>)#}
            + (mset \<Gamma> - image_mset snd (mset (\<PP> \<Sigma> \<Delta>))) - image_mset snd (mset (\<QQ> \<Sigma> \<Delta>))"
    using calculation
          assms(2)
          recoverWitnessA_mset_equiv
          recoverWitnessB_mset_equiv
    by fastforce
  ultimately
  show ?thesis
    using assms recoverWitnessA_mset_equiv
    by simp
qed

theorem (in Classical_Propositional_Logic) segmented_deduction_generalized_witness:
  "\<Gamma> $\<turnstile> (\<Phi> @ \<Psi>) = (\<exists> \<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset \<Gamma> \<and>
                         map (uncurry (\<squnion>)) \<Sigma> $\<turnstile> \<Phi> \<and>
                         (map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> (map snd \<Sigma>)) $\<turnstile> \<Psi>)"
proof -
  have "\<forall> \<Gamma> \<Psi>. \<Gamma> $\<turnstile> (\<Phi> @ \<Psi>) = (\<exists> \<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset \<Gamma> \<and>
                                      map (uncurry (\<squnion>)) \<Sigma> $\<turnstile> \<Phi> \<and>
                                     (map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> (map snd \<Sigma>)) $\<turnstile> \<Psi>)"
  proof (induct \<Phi>)
    case Nil
    {
      fix \<Gamma> \<Psi>
      have "\<Gamma> $\<turnstile> ([] @ \<Psi>) = (\<exists>\<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset \<Gamma> \<and>
                                  map (uncurry (\<squnion>)) \<Sigma> $\<turnstile> [] \<and>
                                  map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> $\<turnstile> \<Psi>)"
      proof (rule iffI)
        assume "\<Gamma> $\<turnstile> ([] @ \<Psi>)"
        moreover
        have "\<Gamma> $\<turnstile> ([] @ \<Psi>) = (mset (map snd []) \<subseteq># mset \<Gamma> \<and>
                                map (uncurry (\<squnion>)) [] $\<turnstile> [] \<and>
                                map (uncurry (\<rightarrow>)) [] @ \<Gamma> \<ominus> (map snd []) $\<turnstile> \<Psi>)"
          by simp
        ultimately show "\<exists>\<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset \<Gamma> \<and>
                              map (uncurry (\<squnion>)) \<Sigma> $\<turnstile> [] \<and>
                              map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> $\<turnstile> \<Psi>"
          by metis
      next
        assume "\<exists>\<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset \<Gamma> \<and>
                    map (uncurry (\<squnion>)) \<Sigma> $\<turnstile> [] \<and>
                    map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> $\<turnstile> \<Psi>"
        from this obtain \<Sigma> where
          \<Sigma>: "mset (map snd \<Sigma>) \<subseteq># mset \<Gamma>"
             "map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> $\<turnstile> ([] @ \<Psi>)"
          by fastforce
        hence "(map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma>) \<preceq> \<Gamma>"
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
                                       map (uncurry (\<squnion>)) \<Sigma> $\<turnstile> (\<phi> # \<Phi>) \<and>
                                       map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> $\<turnstile> \<Psi>)"
      proof (rule iffI)
        assume "\<Gamma> $\<turnstile> ((\<phi> # \<Phi>) @ \<Psi>)"
        from this obtain \<Sigma> where
          \<Sigma>: "mset (map snd \<Sigma>) \<subseteq># mset \<Gamma>"
             "map (uncurry (\<squnion>)) \<Sigma> :\<turnstile> \<phi>"
             "map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> (map snd \<Sigma>) $\<turnstile> (\<Phi> @ \<Psi>)"
             (is "?\<Gamma>\<^sub>0 $\<turnstile> (\<Phi> @ \<Psi>)")
          by auto
        from this(3) obtain \<Delta> where
          \<Delta>: "mset (map snd \<Delta>) \<subseteq># mset ?\<Gamma>\<^sub>0"
             "map (uncurry (\<squnion>)) \<Delta> $\<turnstile> \<Phi>"
             "map (uncurry (\<rightarrow>)) \<Delta> @ ?\<Gamma>\<^sub>0 \<ominus> (map snd \<Delta>) $\<turnstile> \<Psi>"
          using Cons
          by auto
        let ?\<Sigma>' = "\<JJ> \<Sigma> \<Delta>"
        have "map (uncurry (\<squnion>)) ?\<Sigma>' $\<turnstile> (\<phi> # \<Phi>)"
          using \<Delta>(1) \<Delta>(2) \<Sigma>(2) mergeWitness_cons_segmented_deduction by blast
        moreover have "mset (map snd ?\<Sigma>') \<subseteq># mset \<Gamma>"
          using \<Delta>(1) \<Sigma>(1) mergeWitness_msub_intro by blast
        moreover have "map (uncurry (\<rightarrow>)) ?\<Sigma>' @ \<Gamma> \<ominus> map snd ?\<Sigma>' $\<turnstile> \<Psi>"
          using \<Delta>(1) \<Delta>(3) mergeWitness_segmented_deduction_intro by blast
        ultimately show
          "\<exists>\<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset \<Gamma> \<and>
               map (uncurry (\<squnion>)) \<Sigma> $\<turnstile> (\<phi> # \<Phi>) \<and>
               map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> $\<turnstile> \<Psi>"
          by fast
      next
        assume "\<exists>\<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset \<Gamma> \<and>
                    map (uncurry (\<squnion>)) \<Sigma> $\<turnstile> (\<phi> # \<Phi>) \<and>
                    map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> $\<turnstile> \<Psi>"
        from this obtain \<Delta> where \<Delta>:
          "mset (map snd \<Delta>) \<subseteq># mset \<Gamma>"
          "map (uncurry (\<squnion>)) \<Delta> $\<turnstile> (\<phi> # \<Phi>)"
          "map (uncurry (\<rightarrow>)) \<Delta> @ \<Gamma> \<ominus> map snd \<Delta> $\<turnstile> \<Psi>"
          by auto
        from this obtain \<Sigma> where \<Sigma>:
          "mset (map snd \<Sigma>) \<subseteq># mset (map (uncurry (\<squnion>)) \<Delta>)"
          "map (uncurry (\<squnion>)) \<Sigma> :\<turnstile> \<phi>"
          "map (uncurry (\<rightarrow>)) \<Sigma> @ (map (uncurry (\<squnion>)) \<Delta>) \<ominus> map snd \<Sigma> $\<turnstile> \<Phi>"
          by auto
        let ?\<Omega> = "\<PP> \<Sigma> \<Delta>"
        let ?\<Xi> = "\<QQ> \<Sigma> \<Delta>"
        let ?\<Gamma>\<^sub>0 = "map (uncurry (\<rightarrow>)) ?\<Omega> @ \<Gamma> \<ominus> map snd ?\<Omega>"
        let ?\<Gamma>\<^sub>1 = "map (uncurry (\<rightarrow>)) ?\<Xi> @ ?\<Gamma>\<^sub>0 \<ominus> map snd ?\<Xi>"
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
        have "map (uncurry (\<squnion>)) ?\<Xi> $\<turnstile> \<Phi>"
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
        have "map (uncurry (\<squnion>)) ?\<Omega> :\<turnstile> \<phi>"
          using \<Sigma>(2)
                recoverWitnessA_left_stronger_theory
                stronger_theory_deduction_monotonic
          by blast
        ultimately show "\<Gamma> $\<turnstile> ((\<phi> # \<Phi>) @ \<Psi>)"
          by (simp, blast)
      qed
    }
    then show ?case by metis
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
        "map (uncurry (\<squnion>)) \<Sigma> :\<turnstile> \<psi>"
        "map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> $\<turnstile> \<Psi>"
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

theorem (in Classical_Propositional_Logic) segmented_transitive:
  assumes "\<Gamma> $\<turnstile> \<Lambda>" and "\<Lambda> $\<turnstile> \<Delta>"
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
        "map (uncurry (\<squnion>)) \<Sigma> :\<turnstile> \<delta>"
        "map (uncurry (\<rightarrow>)) \<Sigma> @ \<Lambda> \<ominus> map snd \<Sigma> $\<turnstile> \<Delta>"
        by auto
      assume "\<Gamma> $\<turnstile> \<Lambda>"
      hence "\<Gamma> $\<turnstile> (map (uncurry (\<squnion>)) \<Sigma> @ map (uncurry (\<rightarrow>)) \<Sigma> @ \<Lambda> \<ominus> (map snd \<Sigma>))"
        using \<Sigma>(1) segmented_witness_right_split
        by simp
      from this obtain \<Psi> where \<Psi>:
        "mset (map snd \<Psi>) \<subseteq># mset \<Gamma>"
        "map (uncurry (\<squnion>)) \<Psi> $\<turnstile> map (uncurry (\<squnion>)) \<Sigma>"
        "map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> map snd \<Psi> $\<turnstile> (map (uncurry (\<rightarrow>)) \<Sigma> @ \<Lambda> \<ominus> map snd \<Sigma>)"
        using segmented_deduction_generalized_witness
        by fastforce
      have "map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> map snd \<Psi> $\<turnstile> \<Delta>"
        using \<Sigma>(3) \<Psi>(3) Cons
        by auto
      moreover
      have "map (uncurry (\<squnion>)) \<Psi> :\<turnstile> \<delta>"
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
  "\<psi> \<squnion> \<phi> # \<psi> \<rightarrow> \<phi> # \<Gamma> $\<turnstile> \<Phi> = \<phi> # \<Gamma> $\<turnstile> \<Phi>"
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

lemma (in Classical_Propositional_Logic) segmented_witness_left_split [simp]:
  assumes "mset (map snd \<Sigma>) \<subseteq># mset \<Gamma>"
  shows "(map (uncurry (\<squnion>)) \<Sigma> @ map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> (map snd \<Sigma>)) $\<turnstile> \<Phi> = \<Gamma> $\<turnstile> \<Phi>"
proof -
  have "\<forall> \<Gamma>. mset (map snd \<Sigma>) \<subseteq># mset \<Gamma> \<longrightarrow>
      (map (uncurry (\<squnion>)) \<Sigma> @ map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> (map snd \<Sigma>)) $\<turnstile> \<Phi> = \<Gamma> $\<turnstile> \<Phi>"
  proof (induct \<Sigma>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<sigma> \<Sigma>)
    {
      fix \<Gamma>
      let ?\<chi> = "fst \<sigma>"
      let ?\<gamma> = "snd \<sigma>"
      let ?\<Gamma>\<^sub>0 = "map (uncurry (\<squnion>)) \<Sigma> @ map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> map snd (\<sigma> # \<Sigma>)"
      let ?\<Gamma>' = "map (uncurry (\<squnion>)) (\<sigma> # \<Sigma>) @ map (uncurry (\<rightarrow>)) (\<sigma> # \<Sigma>) @ \<Gamma> \<ominus> map snd (\<sigma> # \<Sigma>)"
      assume "mset (map snd (\<sigma> # \<Sigma>)) \<subseteq># mset \<Gamma>"
      hence A: "add_mset (snd \<sigma>) (image_mset snd (mset \<Sigma>)) \<subseteq># mset \<Gamma>" by simp
      hence B: "image_mset snd (mset \<Sigma>) + (mset \<Gamma> - image_mset snd (mset \<Sigma>))
              = add_mset (snd \<sigma>) (image_mset snd (mset \<Sigma>))
                + (mset \<Gamma> - add_mset (snd \<sigma>) (image_mset snd (mset \<Sigma>)))"
        by (metis (no_types) mset_subset_eq_insertD subset_mset.add_diff_inverse subset_mset_def)
      have "{#x \<rightarrow> y. (x, y) \<in># mset \<Sigma>#} + mset \<Gamma> - add_mset (snd \<sigma>) (image_mset snd (mset \<Sigma>))
          = {#x \<rightarrow> y. (x, y) \<in># mset \<Sigma>#} + (mset \<Gamma> - add_mset (snd \<sigma>) (image_mset snd (mset \<Sigma>)))"
        using A subset_mset.diff_add_assoc by blast
      hence "{#x \<rightarrow> y. (x, y) \<in># mset \<Sigma>#} + (mset \<Gamma> - image_mset snd (mset \<Sigma>))
           = add_mset (snd \<sigma>) ({#x \<rightarrow> y. (x, y) \<in># mset \<Sigma>#}
             + mset \<Gamma> - add_mset (snd \<sigma>) (image_mset snd (mset \<Sigma>)))"
        using B by auto
      hence C:
        "mset (map snd \<Sigma>) \<subseteq># mset \<Gamma>"
        "mset (map (uncurry (\<squnion>)) \<Sigma> @ map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma>)
       = mset (?\<gamma> # ?\<Gamma>\<^sub>0)"
        using \<open>mset (map snd (\<sigma> # \<Sigma>)) \<subseteq># mset \<Gamma>\<close>
              subset_mset.dual_order.trans
        by (fastforce+)
      hence "\<Gamma> $\<turnstile> \<Phi> = (?\<chi> \<squnion> ?\<gamma> # ?\<chi> \<rightarrow> ?\<gamma> # ?\<Gamma>\<^sub>0) $\<turnstile> \<Phi>"
      proof -
        have "\<forall>\<Gamma> \<Delta>. \<not> mset (map snd \<Sigma>) \<subseteq># mset \<Gamma>
                  \<or> \<not> \<Gamma> $\<turnstile> \<Phi>
                  \<or> \<not> mset (map (uncurry (\<squnion>)) \<Sigma>
                            @ map (uncurry (\<rightarrow>)) \<Sigma>
                            @ \<Gamma> \<ominus> map snd \<Sigma>)
                      \<subseteq># mset \<Delta>
                  \<or> \<Delta> $\<turnstile> \<Phi>"
          using Cons.hyps segmented_msub_left_monotonic by blast
        moreover
        { assume "\<not> \<Gamma> $\<turnstile> \<Phi>"
          then have "\<exists>\<Delta>. mset (snd \<sigma> # map (uncurry (\<squnion>)) \<Sigma>
                               @ map (uncurry (\<rightarrow>)) \<Sigma>
                               @ \<Gamma> \<ominus> map snd (\<sigma> # \<Sigma>))
                          \<subseteq># mset \<Delta>
                        \<and> \<not> \<Gamma> $\<turnstile> \<Phi>
                        \<and> \<not> \<Delta> $\<turnstile> \<Phi>"
            by (metis (no_types) Cons.hyps C subset_mset.dual_order.refl)
          then have ?thesis
            using segmented_formula_left_split segmented_msub_left_monotonic by blast }
        ultimately show ?thesis
          by (metis (full_types) C segmented_formula_left_split subset_mset.dual_order.refl)
      qed
      moreover
      have "(uncurry (\<squnion>)) = (\<lambda> \<psi>. fst \<psi> \<squnion> snd \<psi>)"
           "(uncurry (\<rightarrow>)) = (\<lambda> \<psi>. fst \<psi> \<rightarrow> snd \<psi>)"
        by fastforce+
      hence "mset ?\<Gamma>' = mset (?\<chi> \<squnion> ?\<gamma> # ?\<chi> \<rightarrow> ?\<gamma> # ?\<Gamma>\<^sub>0)"
        by fastforce
      hence "(?\<chi> \<squnion> ?\<gamma> # ?\<chi> \<rightarrow> ?\<gamma> # ?\<Gamma>\<^sub>0) $\<turnstile> \<Phi> = ?\<Gamma>' $\<turnstile> \<Phi>"
        by (metis (mono_tags, lifting)
                  segmented_msub_left_monotonic
                  subset_mset.dual_order.refl)
      ultimately have "\<Gamma> $\<turnstile> \<Phi> = ?\<Gamma>' $\<turnstile> \<Phi>"
        by fastforce
    }
    then show ?case by blast
  qed
  with assms show ?thesis by blast
qed

lemma (in Classical_Propositional_Logic) segmented_tautology_right_cancel:
  assumes "\<turnstile> \<phi>"
  shows "\<Gamma> $\<turnstile> (\<phi> # \<Phi>) = \<Gamma> $\<turnstile> \<Phi>"
proof (rule iffI)
  assume "\<Gamma> $\<turnstile> (\<phi> # \<Phi>)"
  from this obtain \<Sigma> where \<Sigma>:
    "mset (map snd \<Sigma>) \<subseteq># mset \<Gamma>"
    "map (uncurry (\<squnion>)) \<Sigma> :\<turnstile> \<phi>"
    "map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> $\<turnstile> \<Phi>"
    by auto
  thus "\<Gamma> $\<turnstile> \<Phi>"
    using segmented_stronger_theory_left_monotonic
          witness_stronger_theory
    by blast
next
  assume "\<Gamma> $\<turnstile> \<Phi>"
  hence "map (uncurry (\<rightarrow>)) [] @ \<Gamma> \<ominus> map snd [] $\<turnstile> \<Phi>"
        "mset (map snd []) \<subseteq># mset \<Gamma>"
        "map (uncurry (\<squnion>)) [] :\<turnstile> \<phi>"
    using assms
    by simp+
  thus "\<Gamma> $\<turnstile> (\<phi> # \<Phi>)"
    using segmented_deduction.simps(2)
    by blast
qed

lemma (in Classical_Propositional_Logic) segmented_tautology_left_cancel [simp]:
  assumes "\<turnstile> \<gamma>"
  shows "(\<gamma> # \<Gamma>) $\<turnstile> \<Phi> = \<Gamma> $\<turnstile> \<Phi>"
proof (rule iffI)
  assume "(\<gamma> # \<Gamma>) $\<turnstile> \<Phi>"
  moreover have "\<Gamma> $\<turnstile> \<Gamma>"
    by (simp add: segmented_stronger_theory_intro)
  hence "\<Gamma> $\<turnstile> (\<gamma> # \<Gamma>)"
    using assms segmented_tautology_right_cancel
    by simp
  ultimately show "\<Gamma> $\<turnstile> \<Phi>"
    using segmented_transitive by blast
next
  assume "\<Gamma> $\<turnstile> \<Phi>"
  moreover have "mset \<Gamma> \<subseteq># mset (\<gamma> # \<Gamma>)"
    by simp
  hence "(\<gamma> # \<Gamma>) $\<turnstile> \<Gamma>"
    using msub_stronger_theory_intro
          segmented_stronger_theory_intro
    by blast
  ultimately show "(\<gamma> # \<Gamma>) $\<turnstile> \<Phi>"
    using segmented_transitive by blast
qed

lemma (in Classical_Propositional_Logic) segmented_cancel:
  "(\<Delta> @ \<Gamma>) $\<turnstile> (\<Delta> @ \<Phi>) = \<Gamma> $\<turnstile> \<Phi>"
proof -
  {
    fix \<Delta> \<Gamma> \<Phi>
    assume "\<Gamma> $\<turnstile> \<Phi>"
    hence "(\<Delta> @ \<Gamma>) $\<turnstile> (\<Delta> @ \<Phi>)"
    proof (induct \<Delta>)
      case Nil
      then show ?case by simp
    next
      case (Cons \<delta> \<Delta>)
      let ?\<Sigma> = "[(\<delta>, \<delta>)]"
      have "map (uncurry (\<squnion>)) ?\<Sigma> :\<turnstile> \<delta>"
        unfolding disjunction_def list_deduction_def
        by (simp add: Peirces_law)
      moreover have "mset (map snd ?\<Sigma>) \<subseteq># mset (\<delta> # \<Delta>)" by simp
      moreover have "map (uncurry (\<rightarrow>)) ?\<Sigma> @ ((\<delta> # \<Delta>) @ \<Gamma>) \<ominus> map snd ?\<Sigma> $\<turnstile> (\<Delta> @ \<Phi>)"
        using Cons
        by (simp add: trivial_implication)
      moreover have "map snd [(\<delta>, \<delta>)] = [\<delta>]" by force
      ultimately show ?case
        by (metis (no_types) segmented_deduction.simps(2)
                             append_Cons
                             list.set_intros(1)
                             mset.simps(1)
                             mset.simps(2)
                             mset_subset_eq_single
                             set_mset_mset)
    qed
  } note forward_direction = this
  {
    assume "(\<Delta> @ \<Gamma>) $\<turnstile> (\<Delta> @ \<Phi>)"
    hence "\<Gamma> $\<turnstile> \<Phi>"
    proof (induct \<Delta>)
      case Nil
      then show ?case by simp
    next
      case (Cons \<delta> \<Delta>)
      have "mset ((\<delta> # \<Delta>) @ \<Phi>) = mset ((\<Delta> @ \<Phi>) @ [\<delta>])" by simp
      with Cons.prems have "((\<delta> # \<Delta>) @ \<Gamma>) $\<turnstile> ((\<Delta> @ \<Phi>) @ [\<delta>])"
        by (metis segmented_msub_weaken
                  subset_mset.dual_order.refl)
      from this obtain \<Sigma> where \<Sigma>:
        "mset (map snd \<Sigma>) \<subseteq># mset ((\<delta> # \<Delta>) @ \<Gamma>)"
        "map (uncurry (\<squnion>)) \<Sigma> $\<turnstile> (\<Delta> @ \<Phi>)"
        "map (uncurry (\<rightarrow>)) \<Sigma> @ ((\<delta> # \<Delta>) @ \<Gamma>) \<ominus> map snd \<Sigma> $\<turnstile> [\<delta>]"
        by (metis append_assoc segmented_deduction_generalized_witness)
      show ?case
      proof (cases "find (\<lambda> \<sigma>. snd \<sigma> = \<delta>) \<Sigma> = None")
        case True
        hence "\<delta> \<notin> set (map snd \<Sigma>)"
        proof (induct \<Sigma>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<sigma> \<Sigma>)
          then show ?case by (cases "snd \<sigma> = \<delta>", simp+)
        qed
        with \<Sigma>(1) have "mset (map snd \<Sigma>) \<subseteq># mset (\<Delta> @ \<Gamma>)"
          by (simp, metis add_mset_add_single
                          diff_single_trivial
                          mset_map
                          set_mset_mset
                          subset_eq_diff_conv)
        thus ?thesis
          using segmented_stronger_theory_left_monotonic
                witness_weaker_theory
                Cons.hyps \<Sigma>(2)
          by blast
      next
        case False
        from this obtain \<sigma> \<chi> where
          \<sigma>: "\<sigma> = (\<chi>, \<delta>)"
             "\<sigma> \<in> set \<Sigma>"
          using find_Some_predicate
                find_Some_set_membership
          by fastforce
        let ?\<Sigma>' = "remove1 \<sigma> \<Sigma>"
        let ?\<Sigma>\<^sub>A = "map (uncurry (\<squnion>)) ?\<Sigma>'"
        let ?\<Sigma>\<^sub>B = "map (uncurry (\<rightarrow>)) ?\<Sigma>'"
        have "mset \<Sigma> = mset (?\<Sigma>' @ [(\<chi>, \<delta>)])"
             "mset \<Sigma> = mset ((\<chi>, \<delta>) # ?\<Sigma>')"
          using \<sigma> by simp+
        hence "mset (map (uncurry (\<squnion>)) \<Sigma>) = mset (map (uncurry (\<squnion>)) (?\<Sigma>' @ [(\<chi>, \<delta>)]))"
              "mset (map snd \<Sigma>) = mset (map snd ((\<chi>, \<delta>) # ?\<Sigma>'))"
              "mset (map (uncurry (\<rightarrow>)) \<Sigma>) = mset (map (uncurry (\<rightarrow>)) ((\<chi>, \<delta>) # ?\<Sigma>'))"
          by (metis mset_map)+
        hence "mset (map (uncurry (\<squnion>)) \<Sigma>) = mset (?\<Sigma>\<^sub>A @ [\<chi> \<squnion> \<delta>])"
              "mset (map (uncurry (\<rightarrow>)) \<Sigma> @ ((\<delta> # \<Delta>) @ \<Gamma>) \<ominus> map snd \<Sigma>)
             = mset (\<chi> \<rightarrow> \<delta> # ?\<Sigma>\<^sub>B @ (\<Delta> @ \<Gamma>) \<ominus> map snd ?\<Sigma>')"
          by simp+
        hence
          "?\<Sigma>\<^sub>A @ [\<chi> \<squnion> \<delta>] $\<turnstile> (\<Delta> @ \<Phi>)"
          "\<chi> \<rightarrow> \<delta> # (?\<Sigma>\<^sub>B @ (\<Delta> @ \<Gamma>) \<ominus> map snd ?\<Sigma>') $\<turnstile> [\<delta>]"
          using \<Sigma>(2) \<Sigma>(3)
          by (metis segmented_msub_left_monotonic subset_mset.dual_order.refl, simp)
        moreover
        have "\<turnstile> ((\<chi> \<rightarrow> \<delta>) \<rightarrow> \<delta>) \<rightarrow> (\<chi> \<squnion> \<delta>)"
          unfolding disjunction_def
          using Modus_Ponens
                The_Principle_of_Pseudo_Scotus
                flip_hypothetical_syllogism
          by blast
        ultimately have "(?\<Sigma>\<^sub>A @ ?\<Sigma>\<^sub>B @ (\<Delta> @ \<Gamma>) \<ominus> map snd ?\<Sigma>') $\<turnstile> (\<Delta> @ \<Phi>)"
          using segmented_deduction_one_collapse
                list_deduction_theorem
                list_deduction_modus_ponens
                list_deduction_weaken
                forward_direction
                segmented_transitive
          by meson
        moreover
        have "\<delta> = snd \<sigma>"
             "snd \<sigma> \<in> set (map snd \<Sigma>)"
          by (simp add: \<sigma>(1), simp add: \<sigma>(2))
        with \<Sigma>(1) have "mset (map snd (remove1 \<sigma> \<Sigma>)) \<subseteq># mset (remove1 \<delta> ((\<delta> # \<Delta>) @ \<Gamma>))"
          by (metis insert_DiffM
                    insert_subset_eq_iff
                    mset_remove1
                    \<sigma>(1) \<sigma>(2)
                    remove1_pairs_list_projections_snd
                    set_mset_mset)
        hence "mset (map snd (remove1 \<sigma> \<Sigma>)) \<subseteq># mset (\<Delta> @ \<Gamma>)" by simp
        ultimately show ?thesis
          using segmented_witness_left_split Cons.hyps
          by blast
      qed
    qed
  }
  with forward_direction show ?thesis by auto
qed

lemma (in Classical_Propositional_Logic) segmented_biconditional_cancel:
  assumes "\<turnstile> \<gamma> \<leftrightarrow> \<phi>"
  shows "(\<gamma> # \<Gamma>) $\<turnstile> (\<phi> # \<Phi>) = \<Gamma> $\<turnstile> \<Phi>"
proof -
  from assms have "(\<gamma> # \<Phi>) \<preceq> (\<phi> # \<Phi>)" "(\<phi> # \<Phi>) \<preceq> (\<gamma> # \<Phi>)"
    unfolding biconditional_def
    by (simp add: stronger_theory_left_right_cons)+
  hence "(\<gamma> # \<Phi>) $\<turnstile> (\<phi> # \<Phi>)"
        "(\<phi> # \<Phi>) $\<turnstile> (\<gamma> # \<Phi>)"
    using segmented_stronger_theory_intro by blast+
  moreover
  have "\<Gamma> $\<turnstile> \<Phi> = (\<gamma> # \<Gamma>) $\<turnstile> (\<gamma> # \<Phi>)"
    by (metis append_Cons append_Nil segmented_cancel)+
  ultimately
  have "\<Gamma> $\<turnstile> \<Phi> \<Longrightarrow> \<gamma> # \<Gamma> $\<turnstile> (\<phi> # \<Phi>)"
       "\<gamma> # \<Gamma> $\<turnstile> (\<phi> # \<Phi>) \<Longrightarrow> \<Gamma> $\<turnstile> \<Phi>"
    using segmented_transitive by blast+
  thus ?thesis by blast
qed

lemma (in Classical_Propositional_Logic) right_segmented_sub:
  assumes "\<turnstile> \<phi> \<leftrightarrow> \<psi>"
  shows "\<Gamma> $\<turnstile> (\<phi> # \<Phi>) = \<Gamma> $\<turnstile> (\<psi> # \<Phi>)"
proof -
  have "\<Gamma> $\<turnstile> (\<phi> # \<Phi>) = (\<psi> # \<Gamma>) $\<turnstile> (\<psi> # \<phi> # \<Phi>)"
    using segmented_cancel [where \<Delta>="[\<psi>]" and \<Gamma>="\<Gamma>" and \<Phi>="\<phi> # \<Phi>"] by simp
  also have "... = (\<psi> # \<Gamma>) $\<turnstile> (\<phi> # \<psi> # \<Phi>)"
    using segmented_cons_cons_right_permute by blast
  also have "... = \<Gamma> $\<turnstile> (\<psi> # \<Phi>)"
    using assms biconditional_symmetry_rule segmented_biconditional_cancel by blast
  finally show ?thesis .
qed

lemma (in Classical_Propositional_Logic) left_segmented_sub:
  assumes "\<turnstile> \<gamma> \<leftrightarrow> \<chi>"
  shows "(\<gamma> # \<Gamma>) $\<turnstile> \<Phi> = (\<chi> # \<Gamma>) $\<turnstile> \<Phi>"
proof -
  have "(\<gamma> # \<Gamma>) $\<turnstile> \<Phi> = (\<chi> # \<gamma> # \<Gamma>) $\<turnstile> (\<chi> # \<Phi>)"
    using segmented_cancel [where \<Delta>="[\<chi>]" and \<Gamma>="(\<gamma> # \<Gamma>)" and \<Phi>="\<Phi>"] by simp
  also have "... = (\<gamma> # \<chi> # \<Gamma>) $\<turnstile> (\<chi> # \<Phi>)"
    by (metis segmented_msub_left_monotonic mset_eq_perm perm.swap subset_mset.dual_order.refl)
  also have "... = (\<chi> # \<Gamma>) $\<turnstile> \<Phi>"
    using assms biconditional_symmetry_rule segmented_biconditional_cancel by blast
  finally show ?thesis .
qed

lemma (in Classical_Propositional_Logic) right_segmented_sum_rule:
  "\<Gamma> $\<turnstile> (\<alpha> # \<beta> # \<Phi>) = \<Gamma> $\<turnstile> (\<alpha> \<squnion> \<beta> # \<alpha> \<sqinter> \<beta> # \<Phi>)"
proof -
  have A: "mset (\<alpha> \<squnion> \<beta> # \<beta> \<rightarrow> \<alpha> # \<beta> # \<Phi>) = mset (\<beta> \<rightarrow> \<alpha> # \<beta> # \<alpha> \<squnion> \<beta> # \<Phi>)" by simp
  have B: "\<turnstile> (\<beta> \<rightarrow> \<alpha>) \<leftrightarrow> (\<beta> \<rightarrow> (\<alpha> \<sqinter> \<beta>))"
  proof -
    let ?\<phi> = "(\<^bold>\<langle>\<beta>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<alpha>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<beta>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<alpha>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<beta>\<^bold>\<rangle>))"
    have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
    hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis by simp
  qed
  have C: "\<turnstile> \<beta> \<leftrightarrow> (\<beta> \<squnion> (\<alpha> \<sqinter> \<beta>))"
  proof -
    let ?\<phi> = "\<^bold>\<langle>\<beta>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<beta>\<^bold>\<rangle> \<squnion> (\<^bold>\<langle>\<alpha>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<beta>\<^bold>\<rangle>))"
    have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
    hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis by simp
  qed
  have "\<Gamma> $\<turnstile> (\<alpha> # \<beta> # \<Phi>) = \<Gamma> $\<turnstile> (\<beta> \<squnion> \<alpha> # \<beta> \<rightarrow> \<alpha> # \<beta> # \<Phi>)"
    using segmented_formula_right_split by blast
  also have "... = \<Gamma> $\<turnstile> (\<alpha> \<squnion> \<beta> # \<beta> \<rightarrow> \<alpha> # \<beta> # \<Phi>)"
    using disjunction_commutativity right_segmented_sub by blast
  also have "... = \<Gamma> $\<turnstile> (\<beta> \<rightarrow> \<alpha> # \<beta> # \<alpha> \<squnion> \<beta> # \<Phi>)"
    by (metis A segmented_msub_weaken subset_mset.dual_order.refl)
  also have "... = \<Gamma> $\<turnstile> (\<beta> \<rightarrow> (\<alpha> \<sqinter> \<beta>) # \<beta> # \<alpha> \<squnion> \<beta> # \<Phi>)"
    using B right_segmented_sub by blast
  also have "... = \<Gamma> $\<turnstile> (\<beta> # \<beta> \<rightarrow> (\<alpha> \<sqinter> \<beta>) # \<alpha> \<squnion> \<beta> # \<Phi>)"
    using segmented_cons_cons_right_permute by blast
  also have "... = \<Gamma> $\<turnstile> (\<beta> \<squnion> (\<alpha> \<sqinter> \<beta>) # \<beta> \<rightarrow> (\<alpha> \<sqinter> \<beta>) # \<alpha> \<squnion> \<beta> # \<Phi>)"
    using C right_segmented_sub by blast
  also have "... = \<Gamma> $\<turnstile> (\<alpha> \<sqinter> \<beta> # \<alpha> \<squnion> \<beta> # \<Phi>)"
    using segmented_formula_right_split by blast
  finally show ?thesis
    using segmented_cons_cons_right_permute by blast
qed

lemma (in Classical_Propositional_Logic) left_segmented_sum_rule:
  "(\<alpha> # \<beta> # \<Gamma>) $\<turnstile> \<Phi> = (\<alpha> \<squnion> \<beta> # \<alpha> \<sqinter> \<beta> # \<Gamma>) $\<turnstile> \<Phi>"
proof -
  have \<star>: "mset (\<alpha> \<squnion> \<beta> # \<alpha> \<sqinter> \<beta> # \<alpha> # \<beta> # \<Gamma>) = mset (\<alpha> # \<beta> # \<alpha> \<squnion> \<beta> # \<alpha> \<sqinter> \<beta> # \<Gamma>)" by simp
  have "(\<alpha> # \<beta> # \<Gamma>) $\<turnstile> \<Phi> = (\<alpha> \<squnion> \<beta> # \<alpha> \<sqinter> \<beta> # \<alpha> # \<beta> # \<Gamma>) $\<turnstile> (\<alpha> \<squnion> \<beta> # \<alpha> \<sqinter> \<beta> # \<Phi>)"
    using segmented_cancel [where \<Delta>="[\<alpha> \<squnion> \<beta>, \<alpha> \<sqinter> \<beta>]" and \<Gamma>="(\<alpha> # \<beta> # \<Gamma>)" and \<Phi>="\<Phi>"] by simp
  also have "... = (\<alpha> \<squnion> \<beta> # \<alpha> \<sqinter> \<beta> # \<alpha> # \<beta> # \<Gamma>) $\<turnstile> (\<alpha> # \<beta> # \<Phi>)"
    using right_segmented_sum_rule by blast
  also have "... = (\<alpha> # \<beta> # \<alpha> \<squnion> \<beta> # \<alpha> \<sqinter> \<beta> # \<Gamma>) $\<turnstile> (\<alpha> # \<beta> # \<Phi>)"
    by (metis \<star> segmented_msub_left_monotonic subset_mset.dual_order.refl)
  also have "... = (\<alpha> \<squnion> \<beta> # \<alpha> \<sqinter> \<beta> # \<Gamma>) $\<turnstile> \<Phi>"
    using segmented_cancel [where \<Delta>="[\<alpha>, \<beta>]" and \<Gamma>="(\<alpha> \<squnion> \<beta> # \<alpha> \<sqinter> \<beta> # \<Gamma>)" and \<Phi>="\<Phi>"] by simp
  finally show ?thesis .
qed

lemma (in Classical_Propositional_Logic) segmented_exchange:
  "(\<gamma> # \<Gamma>) $\<turnstile> (\<phi> # \<Phi>) = (\<phi> \<rightarrow> \<gamma> # \<Gamma>) $\<turnstile> (\<gamma> \<rightarrow> \<phi> # \<Phi>)"
proof -
  have "(\<gamma> # \<Gamma>) $\<turnstile> (\<phi> # \<Phi>)
      = (\<phi> \<squnion> \<gamma> # \<phi> \<rightarrow> \<gamma> # \<Gamma>) $\<turnstile> (\<gamma> \<squnion> \<phi> # \<gamma> \<rightarrow> \<phi> # \<Phi>)"
    using segmented_formula_left_split
          segmented_formula_right_split
    by blast+
  thus ?thesis
    using segmented_biconditional_cancel
          disjunction_commutativity
    by blast
qed

lemma (in Classical_Propositional_Logic) segmented_negation_swap:
  "\<Gamma> $\<turnstile> (\<phi> # \<Phi>) = (\<sim> \<phi> # \<Gamma>) $\<turnstile> (\<bottom> # \<Phi>)"
proof -
  have "\<Gamma> $\<turnstile> (\<phi> # \<Phi>) = (\<bottom> # \<Gamma>) $\<turnstile> (\<bottom> # \<phi> # \<Phi>)"
    by (metis append_Cons append_Nil segmented_cancel)
  also have "... = (\<bottom> # \<Gamma>) $\<turnstile> (\<phi> # \<bottom> # \<Phi>)"
    using segmented_cons_cons_right_permute by blast
  also have "... = (\<sim> \<phi> # \<Gamma>) $\<turnstile> (\<bottom> \<rightarrow> \<phi> # \<bottom> # \<Phi>)"
    unfolding negation_def
    using segmented_exchange
    by blast
  also have "... = (\<sim> \<phi> # \<Gamma>) $\<turnstile> (\<bottom> # \<Phi>)"
    using Ex_Falso_Quodlibet
          segmented_tautology_right_cancel
    by blast
  finally show ?thesis .
qed

primrec (in Classical_Propositional_Logic)
  stratified_deduction :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool" ("_ #\<turnstile> _ _" [60,100,59] 60)
  where
    "\<Gamma> #\<turnstile> 0 \<phi> = True"
  | "\<Gamma> #\<turnstile> (Suc n) \<phi> = (\<exists> \<Psi>. mset (map snd \<Psi>) \<subseteq># mset \<Gamma> \<and>
                             map (uncurry (\<squnion>)) \<Psi> :\<turnstile> \<phi> \<and>
                             map (uncurry (\<rightarrow>)) \<Psi> @ \<Gamma> \<ominus> (map snd \<Psi>) #\<turnstile> n \<phi>)"

lemma (in Classical_Propositional_Logic) stratified_segmented_deduction_replicate:
  "\<Gamma> #\<turnstile> n \<phi> = \<Gamma> $\<turnstile> (replicate n \<phi>)"
proof -
  have "\<forall> \<Gamma>. \<Gamma> #\<turnstile> n \<phi> = \<Gamma> $\<turnstile> (replicate n \<phi>)"
    by (induct n, simp+)
  thus ?thesis by blast
qed

lemma (in Classical_Propositional_Logic) stratified_deduction_tautology_weaken:
  assumes "\<turnstile> \<phi>"
  shows "\<Gamma> #\<turnstile> n \<phi>"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  hence "\<Gamma> $\<turnstile> (\<phi> # replicate n \<phi>)"
    using assms
          stratified_segmented_deduction_replicate
          segmented_tautology_right_cancel
    by blast
  hence "\<Gamma> $\<turnstile> replicate (Suc n) \<phi>"
    by simp
  then show ?case
    using stratified_segmented_deduction_replicate
    by blast
qed

lemma (in Classical_Propositional_Logic) stratified_deduction_weaken:
  assumes "n \<le> m"
      and "\<Gamma> #\<turnstile> m \<phi>"
    shows "\<Gamma> #\<turnstile> n \<phi>"
proof -
  have "\<Gamma> $\<turnstile> replicate m \<phi>"
    using assms(2) stratified_segmented_deduction_replicate
    by blast
  hence "\<Gamma> $\<turnstile> replicate n \<phi>"
    by (metis append_Nil2
              assms(1)
              le_iff_add
              segmented_deduction.simps(1)
              segmented_deduction_generalized_witness
              replicate_add)
  thus ?thesis
    using stratified_segmented_deduction_replicate
    by blast
qed

lemma (in Classical_Propositional_Logic) stratified_deduction_implication:
  assumes "\<turnstile> \<phi> \<rightarrow> \<psi>"
     and "\<Gamma> #\<turnstile> n \<phi>"
   shows "\<Gamma> #\<turnstile> n \<psi>"
proof -
  have "replicate n \<psi> \<preceq> replicate n \<phi>"
    using stronger_theory_left_right_cons assms(1)
    by (induct n, auto)
  thus ?thesis
    using assms(2)
          segmented_stronger_theory_right_antitonic
          stratified_segmented_deduction_replicate
    by blast
qed

theorem (in Classical_Propositional_Logic) segmented_stratified_falsum_equiv:
  "\<Gamma> $\<turnstile> \<Phi> = (\<^bold>\<sim> \<Phi> @ \<Gamma>) #\<turnstile> (length \<Phi>) \<bottom>"
proof -
  have "\<forall> \<Gamma> \<Psi>. \<Gamma> $\<turnstile> (\<Phi> @ \<Psi>) = (\<^bold>\<sim> \<Phi> @ \<Gamma>) $\<turnstile> (replicate (length \<Phi>) \<bottom> @ \<Psi>)"
  proof (induct \<Phi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<phi> \<Phi>)
    {
      fix \<Gamma> \<Psi>
      have "\<Gamma> $\<turnstile> ((\<phi> # \<Phi>) @ \<Psi>) = (\<sim> \<phi> # \<Gamma>) $\<turnstile> (\<bottom> # \<Phi> @ \<Psi>)"
        using segmented_negation_swap by auto
      moreover have "mset (\<Phi> @ (\<bottom> # \<Psi>)) = mset (\<bottom> # \<Phi> @ \<Psi>)"
        by simp
      ultimately have "\<Gamma> $\<turnstile> ((\<phi> # \<Phi>) @ \<Psi>) = (\<sim> \<phi> # \<Gamma>) $\<turnstile> (\<Phi> @ (\<bottom> # \<Psi>))"
        by (metis segmented_msub_weaken subset_mset.order_refl)
      hence "\<Gamma> $\<turnstile> ((\<phi> # \<Phi>) @ \<Psi>) = (\<^bold>\<sim> \<Phi> @ (\<sim> \<phi> # \<Gamma>)) $\<turnstile> (replicate (length \<Phi>) \<bottom> @ (\<bottom> # \<Psi>))"
        using Cons
        by blast
      moreover have "mset (\<^bold>\<sim> \<Phi> @ (\<sim> \<phi> # \<Gamma>)) = mset (\<^bold>\<sim> (\<phi> # \<Phi>) @ \<Gamma>)"
                    "mset (replicate (length \<Phi>) \<bottom> @ (\<bottom> # \<Psi>))
                   = mset (replicate (length (\<phi> # \<Phi>)) \<bottom> @ \<Psi>)"
        by simp+
      ultimately have
        "\<Gamma> $\<turnstile> ((\<phi> # \<Phi>) @ \<Psi>) = \<^bold>\<sim> (\<phi> # \<Phi>) @ \<Gamma> $\<turnstile> (replicate (length (\<phi> # \<Phi>)) \<bottom> @ \<Psi>)"
        by (metis append.assoc
                  append_Cons
                  append_Nil
                  length_Cons
                  replicate_append_same
                  listSubtract.simps(1)
                  map_ident replicate_Suc
                  segmented_msub_left_monotonic
                  map_listSubtract_mset_containment)
    }
    then show ?case by blast
  qed
  thus ?thesis
    by (metis append_Nil2 stratified_segmented_deduction_replicate)
qed

(**************************************)

definition (in Minimal_Logic) unproving_core :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list set" ("\<C>")
  where
    "\<C> \<Gamma> \<phi> = {\<Phi>. mset \<Phi> \<subseteq># mset \<Gamma>
                  \<and> \<not> \<Phi> :\<turnstile> \<phi>
                  \<and> (\<forall> \<Psi>. mset \<Psi> \<subseteq># mset \<Gamma> \<longrightarrow> \<not> \<Psi> :\<turnstile> \<phi> \<longrightarrow> length \<Psi> \<le> length \<Phi>)}"

lemma (in Minimal_Logic) unproving_core_finite:
  "finite (\<C> \<Gamma> \<phi>)"
proof -
  {
    fix \<Phi>
    assume "\<Phi> \<in> \<C> \<Gamma> \<phi>"
    hence "set \<Phi> \<subseteq> set \<Gamma>"
          "length \<Phi> \<le> length \<Gamma>"
      unfolding unproving_core_def
      using mset_subset_eqD
            length_sub_mset
            mset_eq_length
      by fastforce+
  }
  hence "\<C> \<Gamma> \<phi> \<subseteq> {xs. set xs \<subseteq> set \<Gamma> \<and> length xs \<le> length \<Gamma>}"
    by auto
  moreover
  have "finite {xs. set xs \<subseteq> set \<Gamma> \<and> length xs \<le> length \<Gamma>}"
    using finite_lists_length_le by blast
  ultimately show ?thesis using rev_finite_subset by auto
qed

lemma (in Minimal_Logic) unproving_core_existence:
  "(\<not> \<turnstile> \<phi>) = (\<exists> \<Sigma>. \<Sigma> \<in> \<C> \<Gamma> \<phi>)"
proof (rule iffI)
  assume "\<not> \<turnstile> \<phi>"
  show "\<exists>\<Sigma>. \<Sigma> \<in> \<C> \<Gamma> \<phi>"
  proof (rule ccontr)
    assume "\<nexists>\<Sigma>. \<Sigma> \<in> \<C> \<Gamma> \<phi>"
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
            metis \<open>\<not> \<turnstile> \<phi>\<close>
                 list_deduction_base_theory
                 mset.simps(1)
                 neq0_conv
                 subset_mset.bot.extremum,
            fastforce)
    }
    hence "\<exists> \<Psi>. mset \<Psi> \<subseteq># mset \<Gamma> \<and> length \<Psi> > length \<Gamma>"
      by auto
    thus "False"
      using size_mset_mono by fastforce
  qed
next
  assume "\<exists>\<Sigma>. \<Sigma> \<in> \<C> \<Gamma> \<phi>"
  thus "\<not> \<turnstile> \<phi>"
    unfolding unproving_core_def
    using list_deduction_weaken
    by blast
qed

lemma (in Minimal_Logic) unproving_core_complement_deduction:
  assumes "\<Phi> \<in> \<C> \<Gamma> \<phi>"
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

lemma (in Minimal_Logic) unproving_core_set_complement [simp]:
  assumes "\<Phi> \<in> \<C> \<Gamma> \<phi>"
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
  assumes "\<Phi> \<in> \<C> \<Gamma> \<phi>"
      and "\<psi> \<in> set \<Gamma>"
    shows "\<Phi> :\<turnstile> \<psi> \<rightarrow> \<phi> = (\<psi> \<notin> set \<Phi>)"
proof (rule iffI)
  assume "\<Phi> :\<turnstile> \<psi> \<rightarrow> \<phi>"
  thus "\<psi> \<notin> set \<Phi>"
    using assms(1)
          list_deduction_modus_ponens
          list_deduction_reflection
          unproving_core_def
    by blast
next
  assume "\<psi> \<notin> set \<Phi>"
  thus "\<Phi> :\<turnstile> \<psi> \<rightarrow> \<phi>"
    using assms unproving_core_complement_deduction
    by auto
qed

lemma (in Minimal_Logic) unproving_length_equiv:
  assumes "\<Phi> \<in> \<C> \<Gamma> \<phi>"
      and "\<Psi> \<in> \<C> \<Gamma> \<phi>"
    shows "length \<Phi> = length \<Psi>"
  using assms
  by (simp add: dual_order.antisym unproving_core_def)

lemma (in Minimal_Logic) unproving_listSubtract_length_equiv:
  assumes "\<Phi> \<in> \<C> \<Gamma> \<phi>"
      and "\<Psi> \<in> \<C> \<Gamma> \<phi>"
    shows "length (\<Gamma> \<ominus> \<Phi>) = length (\<Gamma> \<ominus> \<Psi>)"
proof -
  have "length \<Phi> = length \<Psi>"
    using assms unproving_length_equiv
    by blast
  moreover
  have "mset \<Phi> \<subseteq># mset \<Gamma>"
       "mset \<Psi> \<subseteq># mset \<Gamma>"
    using assms unproving_core_def by blast+
  hence "length (\<Gamma> \<ominus> \<Phi>) = length \<Gamma> - length \<Phi>"
        "length (\<Gamma> \<ominus> \<Psi>) = length \<Gamma> - length \<Psi>"
    by (metis listSubtract_mset_homomorphism size_Diff_submset size_mset)+
  ultimately show ?thesis by metis
qed

lemma (in Minimal_Logic) unproving_core_max_list_deduction:
  "\<Gamma> :\<turnstile> \<phi> = (\<forall> \<Phi> \<in> \<C> \<Gamma> \<phi>. 1 \<le> length (\<Gamma> \<ominus> \<Phi>))"
proof cases
  assume "\<turnstile> \<phi>"
  hence "\<Gamma> :\<turnstile> \<phi>" "\<C> \<Gamma> \<phi> = {}"
    unfolding unproving_core_def
    by (simp add: list_deduction_weaken)+
  then show ?thesis by blast
next
  assume "\<not> \<turnstile> \<phi>"
  from this obtain \<Omega> where \<Omega>: "\<Omega> \<in> \<C> \<Gamma> \<phi>"
    using unproving_core_existence by blast
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

definition (in Minimal_Logic) core_size :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" ("\<bar> _ \<bar>\<^sub>_" [45])
  where
    "(\<bar> \<Gamma> \<bar>\<^sub>\<phi>) = (if \<C> \<Gamma> \<phi> = {} then 0 else Max { length \<Phi> | \<Phi>. \<Phi> \<in> \<C> \<Gamma> \<phi> })"

definition (in Minimal_Logic) complement_core_size :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" ("\<parallel> _ \<parallel>\<^sub>_" [45])
  where
    "(\<parallel> \<Gamma> \<parallel>\<^sub>\<phi>) = length \<Gamma> - \<bar> \<Gamma> \<bar>\<^sub>\<phi>"

lemma (in Minimal_Logic) core_size_intro:
  assumes "\<Phi> \<in> \<C> \<Gamma> \<phi>"
  shows "length \<Phi> = \<bar> \<Gamma> \<bar>\<^sub>\<phi>"
proof -
  have "\<forall> n \<in> { length \<Psi> | \<Psi>. \<Psi> \<in> \<C> \<Gamma> \<phi> }. n \<le> length \<Phi>"
       "length \<Phi> \<in> { length \<Psi> | \<Psi>. \<Psi> \<in> \<C> \<Gamma> \<phi> }"
    using assms unproving_core_def
    by auto
  moreover
  have "finite { length \<Psi> | \<Psi>. \<Psi> \<in> \<C> \<Gamma> \<phi> }"
    using finite_imageI unproving_core_finite
    by simp
  ultimately have "Max { length \<Psi> | \<Psi>. \<Psi> \<in> \<C> \<Gamma> \<phi> } = length \<Phi>"
    using Max_eqI
    by blast
  thus ?thesis
    using assms core_size_def
    by auto
qed

lemma (in Minimal_Logic) complement_core_size_intro:
  assumes "\<Phi> \<in> \<C> \<Gamma> \<phi>"
  shows "length (\<Gamma> \<ominus> \<Phi>) = \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>"
proof -
  have "mset \<Phi> \<subseteq># mset \<Gamma>"
    using assms
    unfolding unproving_core_def
    by auto
  moreover from this have "length (\<Gamma> \<ominus> \<Phi>) = length \<Gamma> - length \<Phi>"
    by (metis listSubtract_mset_homomorphism size_Diff_submset size_mset)
  ultimately show ?thesis
    unfolding complement_core_size_def
    by (metis assms core_size_intro)
qed

lemma (in Minimal_Logic) length_core_decomposition:
  "length \<Gamma> = (\<bar> \<Gamma> \<bar>\<^sub>\<phi>) + \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>"
proof (cases "\<C> \<Gamma> \<phi> = {}")
  case True
  then show ?thesis
    unfolding core_size_def
              complement_core_size_def
    by simp
next
  case False
  from this obtain \<Phi> where "\<Phi> \<in> \<C> \<Gamma> \<phi>"
    by fast
  moreover from this have "mset \<Phi> \<subseteq># mset \<Gamma>"
    unfolding unproving_core_def
    by auto
  moreover from this have "length (\<Gamma> \<ominus> \<Phi>) = length \<Gamma> - length \<Phi>"
    by (metis listSubtract_mset_homomorphism size_Diff_submset size_mset)
  ultimately show ?thesis
    unfolding complement_core_size_def
    using listSubtract_msub_eq core_size_intro
    by fastforce
qed

primrec core_optimal_pre_witness :: "'a list \<Rightarrow> ('a list \<times> 'a) list" ("\<VV>")
  where
    "\<VV> [] = []"
  | "\<VV> (\<psi> # \<Psi>) = (\<Psi>, \<psi>) # \<VV> \<Psi>"

lemma core_optimal_pre_witness_element_inclusion:
  "\<forall> (\<Delta>,\<delta>) \<in> set (\<VV> \<Psi>). set (\<VV> \<Delta>) \<subseteq> set (\<VV> \<Psi>)"
  by (induct \<Psi>, fastforce+)

lemma core_optimal_pre_witness_nonelement:
  assumes "length \<Delta> \<ge> length \<Psi>"
  shows "(\<Delta>,\<delta>) \<notin> set (\<VV> \<Psi>)"
  using assms
proof (induct \<Psi>)
  case Nil
  then show ?case by simp
next
  case (Cons \<psi> \<Psi>)
  hence "\<Psi> \<noteq> \<Delta>" by auto
  then show ?case using Cons by simp
qed

lemma core_optimal_pre_witness_distinct: "distinct (\<VV> \<Psi>)"
  by (induct \<Psi>, simp, simp add: core_optimal_pre_witness_nonelement)

lemma core_optimal_pre_witness_length_iff_eq:
  "\<forall> (\<Delta>,\<delta>) \<in> set (\<VV> \<Psi>). \<forall> (\<Sigma>,\<sigma>) \<in> set (\<VV> \<Psi>). (length \<Delta> = length \<Sigma>) = ((\<Delta>, \<delta>) = (\<Sigma>,\<sigma>))"
proof (induct \<Psi>)
  case Nil
  then show ?case by simp
next
  case (Cons \<psi> \<Psi>)
  {
    fix \<Delta>
    fix \<delta>
    assume "(\<Delta>,\<delta>) \<in> set (\<VV> (\<psi> # \<Psi>))"
       and "length \<Delta> = length \<Psi>"
    hence "(\<Delta>,\<delta>) = (\<Psi>, \<psi>)"
      by (simp add: core_optimal_pre_witness_nonelement)
  }
  hence "\<forall> (\<Delta>,\<delta>) \<in> set (\<VV> (\<psi> # \<Psi>)). (length \<Delta> = length \<Psi>) = ((\<Delta>,\<delta>) = (\<Psi>,\<psi>))"
    by blast
  with Cons show ?case
    by auto
qed

lemma mset_distinct_msub_down:
  assumes "mset A \<subseteq># mset B"
      and "distinct B"
    shows "distinct A"
  using assms
  by (meson distinct_append mset_le_perm_append perm_distinct_iff)

lemma mset_remdups_set_sub_iff:
  "(mset (remdups A) \<subseteq># mset (remdups B)) = (set A \<subseteq> set B)"
proof -
  have "\<forall>B. (mset (remdups A) \<subseteq># mset (remdups B)) = (set A \<subseteq> set B)"
  proof (induct A)
    case Nil
    then show ?case by simp
  next
    case (Cons a A)
    then show ?case
    proof (cases "a \<in> set A")
      case True
      then show ?thesis using Cons by auto
    next
      case False
      {
        fix B
        have "(mset (remdups (a # A)) \<subseteq># mset (remdups B)) = (set (a # A) \<subseteq> set B)"
        proof (rule iffI)
          assume assm: "mset (remdups (a # A)) \<subseteq># mset (remdups B)"
          hence "mset (remdups A) \<subseteq># mset (remdups B) - {#a#}"
            using False
            by (simp add: insert_subset_eq_iff)
          hence "mset (remdups A) \<subseteq># mset (remdups (removeAll a B))"
            by (metis diff_subset_eq_self
                      distinct_remdups
                      distinct_remove1_removeAll
                      mset_distinct_msub_down
                      mset_remove1
                      set_eq_iff_mset_eq_distinct
                      set_remdups set_removeAll)
          hence "set A \<subseteq> set (removeAll a B)"
            using Cons.hyps by blast
          moreover from assm False have "a \<in> set B"
            using mset_subset_eq_insertD by fastforce
          ultimately show "set (a # A) \<subseteq> set B"
            by auto
        next
          assume assm: "set (a # A) \<subseteq> set B"
          hence "set A \<subseteq> set (removeAll a B)" using False
            by auto
          hence "mset (remdups A) \<subseteq># mset (remdups B) - {#a#}"
            by (metis Cons.hyps
                      distinct_remdups
                      mset_remdups_subset_eq
                      mset_remove1 remove_code(1)
                      set_remdups set_remove1_eq
                      set_removeAll
                      subset_mset.dual_order.trans)
          moreover from assm False have "a \<in> set B" by auto
          ultimately show "mset (remdups (a # A)) \<subseteq># mset (remdups B)"
            by (simp add: False insert_subset_eq_iff)
        qed
      }
      then show ?thesis by simp
    qed
  qed
  thus ?thesis by blast
qed

lemma range_characterization:
  shows "(mset X = mset [0..<length X]) = (distinct X \<and> (\<forall> x \<in> set X. x < length X))"
proof (rule iffI)
  assume "mset X = mset [0..<length X]"
  thus "distinct X \<and> (\<forall>x\<in>set X. x < length X)"
    by (metis atLeastLessThan_iff count_mset_0_iff distinct_count_atmost_1 distinct_upt set_upt)
next
  assume "distinct X \<and> (\<forall>x\<in>set X. x < length X)"
  moreover
  {
    fix n
    have "\<forall> X. n = length X \<longrightarrow>
               distinct X \<and> (\<forall>x\<in>set X. x < length X) \<longrightarrow>
               mset X = mset [0..<length X]"
    proof (induct n)
      case 0
      then show ?case by simp
    next
      case (Suc n)
      {
        fix X
        assume A: "n + 1 = length X"
           and B: "distinct X"
           and C: "\<forall>x\<in>set X. x < length X"
        have "n \<in> set X"
        proof (rule ccontr)
          assume "n \<notin> set X"
          from A have A': "n = length (tl X)"
            by simp
          from B have B': "distinct (tl X)"
            by (simp add: distinct_tl)
          have C': "\<forall>x\<in>set (tl X). x < length (tl X)"
            by (metis A A' C \<open>n \<notin> set X\<close>
                      Suc_eq_plus1
                      Suc_le_eq
                      Suc_le_mono
                      le_less
                      list.set_sel(2)
                      list.size(3)
                      nat.simps(3))
          from A' B' C' Suc have "mset (tl X) = mset [0..<n]"
            by blast
          from A have "X = hd X # tl X"
            by (metis Suc_eq_plus1 list.exhaust_sel list.size(3) nat.simps(3))
          with B \<open>mset (tl X) = mset [0..<n]\<close> have "hd X \<notin> set [0..<n]"
            by (metis distinct.simps(2) mset_eq_setD)
          hence "hd X \<ge> n" by simp
          with C \<open>n \<notin> set X\<close> \<open>X = hd X # tl X\<close> show "False"
            by (metis A Suc_eq_plus1 Suc_le_eq le_neq_trans list.set_intros(1) not_less)
        qed
        let ?X' = "remove1 n X"
        have A': "n = length ?X'"
          by (metis A \<open>n \<in> set X\<close> diff_add_inverse2 length_remove1)
        have B': "distinct ?X'"
          by (simp add: B)
        have C': "\<forall>x\<in>set ?X'. x < length ?X'"
          by (metis A A' B C
                    DiffE
                    Suc_eq_plus1
                    Suc_le_eq
                    Suc_le_mono
                    le_neq_trans
                    set_remove1_eq
                    singletonI)
        hence "mset ?X' = mset [0..<n]"
          using A' B' C' Suc
          by auto
        hence "mset (n # ?X') = mset [0..<n+1]"
          by simp
        hence "mset X = mset [0..<length X]"
          by (metis A B
                    \<open>n \<in> set X\<close>
                    distinct_upt
                    perm_remove
                    perm_set_eq
                    set_eq_iff_mset_eq_distinct
                    set_mset_mset)
      }
      then show ?case by fastforce
    qed
  }
  ultimately show "mset X = mset [0..<length X]"
    by blast
qed

lemma distinct_pigeon_hole:
  assumes "distinct X"
      and "X \<noteq> []"
    shows "\<exists> n \<in> set X. n + 1 \<ge> length X"
proof (rule ccontr)
  assume \<star>: "\<not> (\<exists> n \<in> set X. length X \<le> n + 1)"
  hence "\<forall> n \<in> set X. n < length X" by fastforce
  hence "mset X = mset [0..<length X]"
    using assms(1) range_characterization
    by fastforce
  with assms(2) have "length X - 1 \<in> set X"
    by (metis diff_zero last_in_set last_upt length_greater_0_conv length_upt mset_eq_setD)
  with \<star> show False
    by (metis One_nat_def Suc_eq_plus1 Suc_pred le_refl length_pos_if_in_set)
qed

lemma core_optimal_pre_witness_pigeon_hole:
  assumes "mset \<Sigma> \<subseteq># mset (\<VV> \<Psi>)"
      and "\<Sigma> \<noteq> []"
    shows "\<exists> (\<Delta>, \<delta>) \<in> set \<Sigma>. length \<Delta> + 1 \<ge> length \<Sigma>"
proof -
  have "distinct \<Sigma>"
    using assms
          core_optimal_pre_witness_distinct
          mset_distinct_msub_down
    by blast
  with assms(1) have "distinct (map (length \<circ> fst) \<Sigma>)"
  proof (induct \<Sigma>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<sigma> \<Sigma>)
    hence "mset \<Sigma> \<subseteq># mset (\<VV> \<Psi>)"
          "distinct \<Sigma>"
      by (metis mset.simps(2) mset_subset_eq_insertD subset_mset_def, simp)
    with Cons.hyps have "distinct (map (\<lambda>a. length (fst a)) \<Sigma>)" by simp
    moreover
    obtain \<delta> \<Delta> where "\<sigma> = (\<Delta>, \<delta>)"
      by fastforce
    hence "(\<Delta>, \<delta>) \<in> set (\<VV> \<Psi>)"
      using Cons.prems mset_subset_eq_insertD
      by fastforce
    hence "\<forall> (\<Sigma>,\<sigma>) \<in> set (\<VV> \<Psi>). (length \<Delta> = length \<Sigma>) = ((\<Delta>, \<delta>) = (\<Sigma>, \<sigma>))"
      using core_optimal_pre_witness_length_iff_eq [where \<Psi>="\<Psi>"]
      by fastforce
    hence "\<forall> (\<Sigma>,\<sigma>) \<in> set \<Sigma>. (length \<Delta> = length \<Sigma>) = ((\<Delta>, \<delta>) = (\<Sigma>, \<sigma>))"
      using \<open>mset \<Sigma> \<subseteq># mset (\<VV> \<Psi>)\<close>
      by (metis (no_types, lifting) Un_iff mset_le_perm_append perm_set_eq set_append)
    hence "length (fst \<sigma>) \<notin> set (map (\<lambda>a. length (fst a)) \<Sigma>)"
      using Cons.prems(2) \<open>\<sigma> = (\<Delta>, \<delta>)\<close>
      by fastforce
    ultimately show ?case by simp
  qed
  moreover have "length (map (length \<circ> fst) \<Sigma>) = length \<Sigma>" by simp
  moreover have "map (length \<circ> fst) \<Sigma> \<noteq> []" using assms by simp
  ultimately show ?thesis
    using distinct_pigeon_hole
    by fastforce
qed

abbreviation (in Classical_Propositional_Logic)
  core_optimal_witness :: "'a \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'a) list" ("\<WW>")
  where "\<WW> \<phi> \<Xi> \<equiv> map (\<lambda>(\<Psi>,\<psi>). (\<Psi> :\<rightarrow> \<phi>, \<psi>)) (\<VV> \<Xi>)"

abbreviation (in Classical_Propositional_Logic)
  disjunction_core_optimal_witness :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" ("\<WW>\<^sub>\<squnion>")
  where "\<WW>\<^sub>\<squnion> \<phi> \<Psi> \<equiv> map (uncurry (\<squnion>)) (\<WW> \<phi> \<Psi>)"

abbreviation (in Classical_Propositional_Logic)
  implication_core_optimal_witness :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" ("\<WW>\<^sub>\<rightarrow>")
  where "\<WW>\<^sub>\<rightarrow> \<phi> \<Psi> \<equiv> map (uncurry (\<rightarrow>)) (\<WW> \<phi> \<Psi>)"

lemma (in Classical_Propositional_Logic) core_optimal_witness_conjunction_identity:
  "\<turnstile> \<Sqinter> (\<WW>\<^sub>\<squnion> \<phi> \<Psi>) \<leftrightarrow> (\<phi> \<squnion> \<Sqinter> \<Psi>)"
proof (induct \<Psi>)
  case Nil
  then show ?case
    unfolding biconditional_def
              disjunction_def
    using Axiom_1
          Modus_Ponens
          verum_tautology
    by (simp, blast)
next
  case (Cons \<psi> \<Psi>)
  have "\<turnstile> (\<Psi> :\<rightarrow> \<phi>) \<leftrightarrow> (\<Sqinter> \<Psi> \<rightarrow> \<phi>)"
    by (simp add: list_curry_uncurry)
  hence "\<turnstile> \<Sqinter> (map (uncurry (\<squnion>)) (\<WW> \<phi> (\<psi> # \<Psi>)))
        \<leftrightarrow> ((\<Sqinter> \<Psi> \<rightarrow> \<phi> \<squnion> \<psi>) \<sqinter> \<Sqinter> (map (uncurry (\<squnion>)) (\<WW> \<phi> \<Psi>)))"
    unfolding biconditional_def
    using conjunction_monotonic
          disjunction_monotonic
    by simp
  moreover have "\<turnstile> ((\<Sqinter> \<Psi> \<rightarrow> \<phi> \<squnion> \<psi>) \<sqinter> \<Sqinter> (map (uncurry (\<squnion>)) (\<WW> \<phi> \<Psi>)))
                 \<leftrightarrow> ((\<Sqinter> \<Psi> \<rightarrow> \<phi> \<squnion> \<psi>) \<sqinter> (\<phi> \<squnion> \<Sqinter> \<Psi>))"
    using Cons.hyps biconditional_conjunction_weaken_rule
    by blast
  moreover
  {
    fix \<phi> \<psi> \<chi>
    have "\<turnstile> ((\<chi> \<rightarrow> \<phi> \<squnion> \<psi>) \<sqinter> (\<phi> \<squnion> \<chi>)) \<leftrightarrow> (\<phi> \<squnion> (\<psi> \<sqinter> \<chi>))"
    proof -
      let ?\<phi> = "((\<^bold>\<langle>\<chi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>))"
      have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
      hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
      thus ?thesis by simp
    qed
  }
  ultimately have "\<turnstile> \<Sqinter> (map (uncurry (\<squnion>)) (\<WW> \<phi> (\<psi> # \<Psi>))) \<leftrightarrow> (\<phi> \<squnion> (\<psi> \<sqinter> \<Sqinter> \<Psi>))"
    using biconditional_transitivity_rule
    by blast
  then show ?case by simp
qed

lemma (in Classical_Propositional_Logic) core_optimal_witness_deduction:
  "\<turnstile> \<WW>\<^sub>\<squnion> \<phi> \<Psi> :\<rightarrow> \<phi> \<leftrightarrow> \<Psi> :\<rightarrow> \<phi>"
proof -
  have "\<turnstile> \<WW>\<^sub>\<squnion> \<phi> \<Psi> :\<rightarrow> \<phi> \<leftrightarrow> (\<Sqinter> (\<WW>\<^sub>\<squnion> \<phi> \<Psi>) \<rightarrow> \<phi>)"
    by (simp add: list_curry_uncurry)
  moreover
  {
    fix \<alpha> \<beta> \<gamma>
    have "\<turnstile> (\<alpha> \<leftrightarrow> \<beta>) \<rightarrow> ((\<alpha> \<rightarrow> \<gamma>) \<leftrightarrow> (\<beta> \<rightarrow> \<gamma>))"
    proof -
      let ?\<phi> = "(\<^bold>\<langle>\<alpha>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<beta>\<^bold>\<rangle>) \<rightarrow> ((\<^bold>\<langle>\<alpha>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<beta>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>))"
      have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
      hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
      thus ?thesis by simp
    qed
  }
  ultimately have "\<turnstile> \<WW>\<^sub>\<squnion> \<phi> \<Psi> :\<rightarrow> \<phi> \<leftrightarrow> ((\<phi> \<squnion> \<Sqinter> \<Psi>) \<rightarrow> \<phi>)"
    using Modus_Ponens
          biconditional_transitivity_rule
          core_optimal_witness_conjunction_identity
    by blast
  moreover
  {
    fix \<alpha> \<beta>
    have "\<turnstile> ((\<alpha> \<squnion> \<beta>) \<rightarrow> \<alpha>) \<leftrightarrow> (\<beta> \<rightarrow> \<alpha>)"
    proof -
      let ?\<phi> = "((\<^bold>\<langle>\<alpha>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<beta>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>\<alpha>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<beta>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<alpha>\<^bold>\<rangle>)"
      have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
      hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
      thus ?thesis by simp
    qed
  }
  ultimately have "\<turnstile> \<WW>\<^sub>\<squnion> \<phi> \<Psi> :\<rightarrow> \<phi> \<leftrightarrow> (\<Sqinter> \<Psi> \<rightarrow> \<phi>)"
    using biconditional_transitivity_rule by blast
  thus ?thesis
    using biconditional_symmetry_rule
          biconditional_transitivity_rule
          list_curry_uncurry
    by blast
qed

lemma (in Classical_Propositional_Logic) optimal_witness_split_identity:
  "\<turnstile> (\<WW>\<^sub>\<squnion> \<phi> (\<psi> # \<Xi>)) :\<rightarrow> \<phi> \<rightarrow> (\<WW>\<^sub>\<rightarrow> \<phi> (\<psi> # \<Xi>)) :\<rightarrow> \<phi> \<rightarrow> \<Xi> :\<rightarrow> \<phi>"
proof (induct \<Xi>)
  case Nil
  have "\<turnstile> ((\<phi> \<squnion> \<psi>) \<rightarrow> \<phi>) \<rightarrow> ((\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>) \<rightarrow> \<phi>"
  proof -
    let ?\<phi> = "((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>\<phi>\<^bold>\<rangle>) \<rightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>\<phi>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>\<phi>\<^bold>\<rangle>"
    have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
    hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis by simp
  qed
  then show ?case by simp
next
  case (Cons \<xi> \<Xi>)
  let ?A = "\<WW>\<^sub>\<squnion> \<phi> \<Xi> :\<rightarrow> \<phi>"
  let ?B = "\<WW>\<^sub>\<rightarrow> \<phi> \<Xi> :\<rightarrow> \<phi>"
  let ?X = "\<Xi> :\<rightarrow> \<phi>"
  from Cons.hyps have "\<turnstile> ((?X \<squnion> \<psi>) \<rightarrow> ?A) \<rightarrow> ((?X \<rightarrow> \<psi>) \<rightarrow> ?B) \<rightarrow> ?X" by simp
  moreover
  have "\<turnstile> (((?X \<squnion> \<psi>) \<rightarrow> ?A) \<rightarrow> ((?X \<rightarrow> \<psi>) \<rightarrow> ?B) \<rightarrow> ?X)
       \<rightarrow> ((\<xi> \<rightarrow> ?X \<squnion> \<psi>) \<rightarrow> (?X \<squnion> \<xi>) \<rightarrow> ?A) \<rightarrow> (((\<xi> \<rightarrow> ?X) \<rightarrow> \<psi>) \<rightarrow> (?X \<rightarrow> \<xi>) \<rightarrow> ?B) \<rightarrow> \<xi> \<rightarrow> ?X"
  proof -
    let ?\<phi> ="(((\<^bold>\<langle>?X\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>?A\<^bold>\<rangle>) \<rightarrow> ((\<^bold>\<langle>?X\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>?B\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>?X\<^bold>\<rangle>) \<rightarrow>
             ((\<^bold>\<langle>\<xi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>?X\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>?X\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<xi>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>?A\<^bold>\<rangle>) \<rightarrow>
             (((\<^bold>\<langle>\<xi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>?X\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>?X\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<xi>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>?B\<^bold>\<rangle>) \<rightarrow>
             \<^bold>\<langle>\<xi>\<^bold>\<rangle> \<rightarrow>
             \<^bold>\<langle>?X\<^bold>\<rangle>"
    have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
    hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis by simp
  qed
  ultimately
  have " \<turnstile> ((\<xi> \<rightarrow> ?X \<squnion> \<psi>) \<rightarrow> (?X \<squnion> \<xi>) \<rightarrow> ?A) \<rightarrow> (((\<xi> \<rightarrow> ?X) \<rightarrow> \<psi>) \<rightarrow> (?X \<rightarrow> \<xi>) \<rightarrow> ?B) \<rightarrow> \<xi> \<rightarrow> ?X"
    using Modus_Ponens
    by blast
  thus ?case by simp
qed

lemma (in Classical_Propositional_Logic) disj_conj_impl_duality:
  "\<turnstile> (\<phi> \<rightarrow> \<chi> \<sqinter> \<psi> \<rightarrow> \<chi>) \<leftrightarrow> ((\<phi> \<squnion> \<psi>) \<rightarrow> \<chi>)"
proof -
  let ?\<phi> = "(\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)"
  have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
  hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
  thus ?thesis by simp
qed

lemma (in Classical_Propositional_Logic) weak_disj_of_conj_equiv:
  "(\<forall>\<sigma>\<in>set \<Sigma>. \<sigma> :\<turnstile> \<phi>) = \<turnstile> \<Squnion> (map \<Sqinter> \<Sigma>) \<rightarrow> \<phi>"
proof (induct \<Sigma>)
  case Nil
  then show ?case
    by (simp add: Ex_Falso_Quodlibet)
next
  case (Cons \<sigma> \<Sigma>)
  have "(\<forall>\<sigma>'\<in>set (\<sigma> # \<Sigma>). \<sigma>' :\<turnstile> \<phi>) = (\<sigma> :\<turnstile> \<phi> \<and> (\<forall>\<sigma>'\<in>set \<Sigma>. \<sigma>' :\<turnstile> \<phi>))" by simp
  also have "... = (\<turnstile> \<sigma> :\<rightarrow> \<phi> \<and> \<turnstile> \<Squnion> (map \<Sqinter> \<Sigma>) \<rightarrow> \<phi>)" using Cons.hyps list_deduction_def by simp
  also have "... = (\<turnstile> \<Sqinter> \<sigma> \<rightarrow> \<phi> \<and> \<turnstile> \<Squnion> (map \<Sqinter> \<Sigma>) \<rightarrow> \<phi>)"
    using list_curry_uncurry weak_biconditional_weaken by blast
  also have "... = (\<turnstile> \<Sqinter> \<sigma> \<rightarrow> \<phi> \<sqinter> \<Squnion> (map \<Sqinter> \<Sigma>) \<rightarrow> \<phi>)" by simp
  also have "... = (\<turnstile> (\<Sqinter> \<sigma> \<squnion> \<Squnion> (map \<Sqinter> \<Sigma>)) \<rightarrow> \<phi>)"
    using disj_conj_impl_duality weak_biconditional_weaken by blast
  finally show ?case by simp
qed

lemma (in Classical_Propositional_Logic) arbitrary_disj_concat_equiv:
  "\<turnstile> \<Squnion> (\<Phi> @ \<Psi>) \<leftrightarrow> (\<Squnion> \<Phi> \<squnion> \<Squnion> \<Psi>)"
proof (induct \<Phi>)
  case Nil
  then show ?case
    by (simp,
        meson Ex_Falso_Quodlibet
              Modus_Ponens
              biconditional_introduction
              disjunction_elimination
              disjunction_right_introduction
              trivial_implication)
next
  case (Cons \<phi> \<Phi>)
  have "\<turnstile> \<Squnion> (\<Phi> @ \<Psi>) \<leftrightarrow> (\<Squnion> \<Phi> \<squnion> \<Squnion> \<Psi>) \<rightarrow> (\<phi> \<squnion> \<Squnion> (\<Phi> @ \<Psi>)) \<leftrightarrow> ((\<phi> \<squnion> \<Squnion> \<Phi>) \<squnion> \<Squnion> \<Psi>)"
  proof -
    let ?\<phi> =
      "(\<^bold>\<langle>\<Squnion> (\<Phi> @ \<Psi>)\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Psi>\<^bold>\<rangle>)) \<rightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (\<Phi> @ \<Psi>)\<^bold>\<rangle>) \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>\<Squnion> \<Psi>\<^bold>\<rangle>)"
    have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
    hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis by simp
  qed
  then show ?case using Cons Modus_Ponens by simp
qed

lemma (in Classical_Propositional_Logic) arbitrary_conj_concat_equiv:
  "\<turnstile> \<Sqinter> (\<Phi> @ \<Psi>) \<leftrightarrow> (\<Sqinter> \<Phi> \<sqinter> \<Sqinter> \<Psi>)"
proof (induct \<Phi>)
  case Nil
  then show ?case
    by (simp,
        meson Modus_Ponens
              biconditional_introduction
              conjunction_introduction
              conjunction_right_elimination
              verum_tautology)
next
  case (Cons \<phi> \<Phi>)
  have "\<turnstile> \<Sqinter> (\<Phi> @ \<Psi>) \<leftrightarrow> (\<Sqinter> \<Phi> \<sqinter> \<Sqinter> \<Psi>) \<rightarrow> (\<phi> \<sqinter> \<Sqinter> (\<Phi> @ \<Psi>)) \<leftrightarrow> ((\<phi> \<sqinter> \<Sqinter> \<Phi>) \<sqinter> \<Sqinter> \<Psi>)"
  proof -
    let ?\<phi> =
      "(\<^bold>\<langle>\<Sqinter> (\<Phi> @ \<Psi>)\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<Sqinter> \<Phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> \<Psi>\<^bold>\<rangle>)) \<rightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> (\<Phi> @ \<Psi>)\<^bold>\<rangle>) \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> \<Phi>\<^bold>\<rangle>) \<sqinter> \<^bold>\<langle>\<Sqinter> \<Psi>\<^bold>\<rangle>)"
    have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
    hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis by simp
  qed
  then show ?case using Cons Modus_Ponens by simp
qed

lemma (in Classical_Propositional_Logic) conj_absorption:
  assumes "\<chi> \<in> set \<Phi>"
  shows "\<turnstile> \<Sqinter> \<Phi> \<leftrightarrow> (\<chi> \<sqinter> \<Sqinter> \<Phi>)"
  using assms
proof (induct \<Phi>)
  case Nil
  then show ?case by simp
next
  case (Cons \<phi> \<Phi>)
  then show ?case
  proof (cases "\<phi> = \<chi>")
    case True
    then show ?thesis
      by (simp,
          metis biconditional_def
                implication_distribution
                trivial_implication
                weak_biconditional_weaken
                weak_conjunction_deduction_equivalence)
  next
    case False
    then show ?thesis
      by (metis Cons.prems
                Arbitrary_Conjunction.simps(2)
                Modus_Ponens
                arbitrary_conjunction_antitone
                biconditional_introduction
                remdups.simps(2)
                set_remdups
                set_subset_Cons)
  qed
qed

lemma (in Classical_Propositional_Logic) conj_extract: "\<turnstile> \<Squnion> (map ((\<sqinter>) \<phi>) \<Psi>) \<leftrightarrow> (\<phi> \<sqinter> \<Squnion> \<Psi>)"
proof (induct \<Psi>)
  case Nil
  then show ?case
    by (simp add: Ex_Falso_Quodlibet biconditional_def conjunction_right_elimination)
next
  case (Cons \<psi> \<Psi>)
  have "\<turnstile> \<Squnion> (map ((\<sqinter>) \<phi>) \<Psi>) \<leftrightarrow> (\<phi> \<sqinter> \<Squnion> \<Psi>)
        \<rightarrow> ((\<phi> \<sqinter> \<psi>) \<squnion> \<Squnion> (map ((\<sqinter>) \<phi>) \<Psi>)) \<leftrightarrow> (\<phi> \<sqinter> (\<psi> \<squnion> \<Squnion> \<Psi>))"
  proof -
    let ?\<phi> = "\<^bold>\<langle>\<Squnion> (map ((\<sqinter>) \<phi>) \<Psi>)\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> \<Psi>\<^bold>\<rangle>)
              \<rightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>\<Squnion> (map ((\<sqinter>) \<phi>) \<Psi>)\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Psi>\<^bold>\<rangle>))"
    have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
    hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis by simp
  qed
  then show ?case using Cons Modus_Ponens by simp
qed

lemma (in Classical_Propositional_Logic) conj_multi_extract:
  "\<turnstile> \<Squnion> (map \<Sqinter> (map ((@) \<Delta>) \<Sigma>)) \<leftrightarrow> (\<Sqinter> \<Delta> \<sqinter> \<Squnion> (map \<Sqinter> \<Sigma>))"
proof (induct \<Sigma>)
  case Nil
  then show ?case
    by (simp, metis list.simps(8) Arbitrary_Disjunction.simps(1) conj_extract)
next
  case (Cons \<sigma> \<Sigma>)
  moreover have
    "\<turnstile>   \<Squnion> (map \<Sqinter> (map ((@) \<Delta>) \<Sigma>)) \<leftrightarrow> (\<Sqinter> \<Delta> \<sqinter> \<Squnion> (map \<Sqinter> \<Sigma>))
      \<rightarrow> \<Sqinter> (\<Delta> @ \<sigma>) \<leftrightarrow> (\<Sqinter> \<Delta> \<sqinter> \<Sqinter> \<sigma>)
      \<rightarrow> (\<Sqinter> (\<Delta> @ \<sigma>) \<squnion> \<Squnion> (map (\<Sqinter> \<circ> (@) \<Delta>) \<Sigma>)) \<leftrightarrow> (\<Sqinter> \<Delta> \<sqinter> (\<Sqinter> \<sigma> \<squnion> \<Squnion> (map \<Sqinter> \<Sigma>)))"
  proof -
    let ?\<phi> =
      "   \<^bold>\<langle>\<Squnion> (map \<Sqinter> (map ((@) \<Delta>) \<Sigma>))\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<Sqinter> \<Delta>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> (map \<Sqinter> \<Sigma>)\<^bold>\<rangle>)
       \<rightarrow> \<^bold>\<langle>\<Sqinter> (\<Delta> @ \<sigma>)\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<Sqinter> \<Delta>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> \<sigma>\<^bold>\<rangle>)
       \<rightarrow> (\<^bold>\<langle>\<Sqinter> (\<Delta> @ \<sigma>)\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (map (\<Sqinter> \<circ> (@) \<Delta>) \<Sigma>)\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<Sqinter> \<Delta>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<Sqinter> \<sigma>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (map \<Sqinter> \<Sigma>)\<^bold>\<rangle>))"
    have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
    hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis by simp
  qed
  hence
    "\<turnstile> (\<Sqinter> (\<Delta> @ \<sigma>) \<squnion> \<Squnion> (map (\<Sqinter> \<circ> (@) \<Delta>) \<Sigma>)) \<leftrightarrow> (\<Sqinter> \<Delta> \<sqinter> (\<Sqinter> \<sigma> \<squnion> \<Squnion> (map \<Sqinter> \<Sigma>)))"
    using Cons.hyps arbitrary_conj_concat_equiv Modus_Ponens by blast
  then show ?case by simp
qed

lemma (in Classical_Propositional_Logic) extract_inner_concat:
  "\<turnstile> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> (@) \<Delta>)) \<Psi>) \<leftrightarrow> (\<Sqinter> (map snd \<Delta>) \<sqinter> \<Squnion> (map (\<Sqinter> \<circ> map snd) \<Psi>))"
proof (induct \<Delta>)
  case Nil
  then show ?case
    by (simp,
        meson Modus_Ponens
              biconditional_introduction
              conjunction_introduction
              conjunction_right_elimination
              verum_tautology)
next
  case (Cons \<chi> \<Delta>)
  let ?\<Delta>' = "map snd \<Delta>"
  let ?\<chi>' = "snd \<chi>"
  let ?\<Pi> = "\<lambda>\<phi>. \<Sqinter> (map snd \<phi>)"
  let ?\<Pi>\<Delta> = "\<lambda>\<phi>. \<Sqinter> (?\<Delta>' @ map snd \<phi>)"
  from Cons have
    "\<turnstile> \<Squnion> (map ?\<Pi>\<Delta> \<Psi>) \<leftrightarrow> (\<Sqinter> ?\<Delta>' \<sqinter> \<Squnion> (map ?\<Pi> \<Psi>))"
    by auto
  moreover have \<star>: "map (\<lambda>\<phi>. ?\<chi>' \<sqinter> ?\<Pi>\<Delta> \<phi>) = map ((\<sqinter>) ?\<chi>') \<circ> map ?\<Pi>\<Delta>"
    by fastforce
  have "\<Squnion> (map (\<lambda>\<phi>. ?\<chi>' \<sqinter> ?\<Pi>\<Delta> \<phi>) \<Psi>) = \<Squnion> (map ((\<sqinter>) ?\<chi>') (map ?\<Pi>\<Delta> \<Psi>))"
    by (simp add: \<star>)
  hence
    "\<turnstile> \<Squnion> (map (\<lambda>\<phi>. ?\<chi>' \<sqinter> ?\<Pi>\<Delta> \<phi>) \<Psi>) \<leftrightarrow> (?\<chi>' \<sqinter> \<Squnion> (map (\<lambda>\<phi>. ?\<Pi>\<Delta> \<phi>) \<Psi>))"
    using conj_extract by presburger
  moreover have
    "\<turnstile> \<Squnion> (map ?\<Pi>\<Delta> \<Psi>) \<leftrightarrow> (\<Sqinter> ?\<Delta>' \<sqinter> \<Squnion> (map ?\<Pi> \<Psi>))
    \<rightarrow> \<Squnion> (map (\<lambda>\<phi>. ?\<chi>' \<sqinter> ?\<Pi>\<Delta> \<phi>) \<Psi>) \<leftrightarrow> (?\<chi>' \<sqinter> \<Squnion> (map ?\<Pi>\<Delta> \<Psi>))
    \<rightarrow> \<Squnion> (map (\<lambda>\<phi>. ?\<chi>' \<sqinter> ?\<Pi>\<Delta> \<phi>) \<Psi>) \<leftrightarrow> ((?\<chi>' \<sqinter> \<Sqinter> ?\<Delta>') \<sqinter> \<Squnion> (map ?\<Pi> \<Psi>))"
  proof -
    let ?\<phi> = "\<^bold>\<langle>\<Squnion> (map ?\<Pi>\<Delta> \<Psi>)\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<Sqinter> ?\<Delta>'\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> (map ?\<Pi> \<Psi>)\<^bold>\<rangle>)
              \<rightarrow> \<^bold>\<langle>\<Squnion> (map (\<lambda>\<phi>. ?\<chi>' \<sqinter> ?\<Pi>\<Delta> \<phi>) \<Psi>)\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>?\<chi>'\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> (map ?\<Pi>\<Delta> \<Psi>)\<^bold>\<rangle>)
              \<rightarrow> \<^bold>\<langle>\<Squnion> (map (\<lambda>\<phi>. ?\<chi>' \<sqinter> ?\<Pi>\<Delta> \<phi>) \<Psi>)\<^bold>\<rangle> \<leftrightarrow> ((\<^bold>\<langle>?\<chi>'\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> ?\<Delta>'\<^bold>\<rangle>) \<sqinter> \<^bold>\<langle>\<Squnion> (map ?\<Pi> \<Psi>)\<^bold>\<rangle>)"
    have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
    hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis by simp
  qed
  ultimately have "\<turnstile> \<Squnion> (map (\<lambda>\<phi>. ?\<chi>' \<sqinter> \<Sqinter> (?\<Delta>' @ map snd \<phi>)) \<Psi>)
                  \<leftrightarrow> ((?\<chi>' \<sqinter> \<Sqinter> ?\<Delta>') \<sqinter> \<Squnion> (map (\<lambda>\<phi>. \<Sqinter> (map snd \<phi>)) \<Psi>))"
    using Modus_Ponens by blast
  thus ?case by simp
qed

lemma (in Classical_Propositional_Logic) extract_inner_concat_remdups:
  "\<turnstile> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) \<Delta>)) \<Psi>) \<leftrightarrow>
    (\<Sqinter> (map snd \<Delta>) \<sqinter> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) \<Psi>))"
proof -
  have "\<forall> \<Psi>. \<turnstile> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) \<Delta>)) \<Psi>) \<leftrightarrow>
               (\<Sqinter> (map snd \<Delta>) \<sqinter> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) \<Psi>))"
  proof (induct \<Delta>)
    case Nil
    then show ?case
      by (simp,
          meson Modus_Ponens
                biconditional_introduction
                conjunction_introduction
                conjunction_right_elimination
                verum_tautology)
  next
    case (Cons \<delta> \<Delta>)
    {
      fix \<Psi>
      have " \<turnstile>    \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) (\<delta> # \<Delta>))) \<Psi>)
              \<leftrightarrow> (\<Sqinter> (map snd (\<delta> # \<Delta>)) \<sqinter> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) \<Psi>))"
      proof (cases "\<delta> \<in> set \<Delta>")
        assume "\<delta> \<in> set \<Delta>"
        have
          "\<turnstile>    \<Sqinter> (map snd \<Delta>) \<leftrightarrow> (snd \<delta> \<sqinter> \<Sqinter> (map snd \<Delta>))
             \<rightarrow> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) \<Delta>)) \<Psi>)
                \<leftrightarrow> (\<Sqinter> (map snd \<Delta>) \<sqinter> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) \<Psi>))
             \<rightarrow> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) \<Delta>)) \<Psi>)
                \<leftrightarrow> ((snd \<delta> \<sqinter> \<Sqinter> (map snd \<Delta>)) \<sqinter> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) \<Psi>))"
        proof -
          let ?\<phi> = "   \<^bold>\<langle>\<Sqinter> (map snd \<Delta>)\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>snd \<delta>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> (map snd \<Delta>)\<^bold>\<rangle>)
                    \<rightarrow> \<^bold>\<langle>\<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) \<Delta>)) \<Psi>)\<^bold>\<rangle>
                      \<leftrightarrow> (\<^bold>\<langle>\<Sqinter> (map snd \<Delta>)\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) \<Psi>)\<^bold>\<rangle>)
                    \<rightarrow> \<^bold>\<langle>\<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) \<Delta>)) \<Psi>)\<^bold>\<rangle>
                      \<leftrightarrow> ((\<^bold>\<langle>snd \<delta>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> (map snd \<Delta>)\<^bold>\<rangle>) \<sqinter> \<^bold>\<langle>\<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) \<Psi>)\<^bold>\<rangle>)"
          have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
          hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
          thus ?thesis by simp
        qed
        moreover have "\<turnstile> \<Sqinter> (map snd \<Delta>) \<leftrightarrow> (snd \<delta> \<sqinter> \<Sqinter> (map snd \<Delta>))"
          by (simp add: \<open>\<delta> \<in> set \<Delta>\<close> conj_absorption)
        ultimately have
          "\<turnstile>    \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) \<Delta>)) \<Psi>)
             \<leftrightarrow> ((snd \<delta> \<sqinter> \<Sqinter> (map snd \<Delta>)) \<sqinter> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) \<Psi>))"
          using Cons.hyps Modus_Ponens by blast
        moreover have "map snd \<circ> remdups \<circ> (@) (\<delta> # \<Delta>) = map snd \<circ> remdups \<circ> (@) \<Delta>"
          using \<open>\<delta> \<in> set \<Delta>\<close> by fastforce
        ultimately show ?thesis using Cons by simp
      next
        assume "\<delta> \<notin> set \<Delta>"
        hence \<dagger>:
          "\<Sqinter> \<circ> (map snd \<circ> remdups) = (\<lambda>\<psi>. \<Sqinter> (map snd (remdups \<psi>)))"
          "   (\<lambda>\<psi>. \<Sqinter> (map snd (if \<delta> \<in> set \<psi> then remdups (\<Delta> @ \<psi>) else \<delta> # remdups (\<Delta> @ \<psi>))))
            = \<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) (\<delta> # \<Delta>))"
          by fastforce+
        show ?thesis
        proof (induct \<Psi>)
          case Nil
          then show ?case
            by (simp, metis list.simps(8) Arbitrary_Disjunction.simps(1) conj_extract)
        next
          case (Cons \<psi> \<Psi>)
          have "\<turnstile> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) \<Delta>)) [\<psi>])
                \<leftrightarrow> (\<Sqinter> (map snd \<Delta>) \<sqinter> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) [\<psi>]))"
            using \<open>\<forall>\<Psi>. \<turnstile>     \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) \<Delta>)) \<Psi>)
                        \<leftrightarrow> (\<Sqinter> (map snd \<Delta>) \<sqinter> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) \<Psi>))\<close>
            by blast
          hence
            "\<turnstile>   (\<Sqinter> (map snd (remdups (\<Delta> @ \<psi>))) \<squnion> \<bottom>)
               \<leftrightarrow> (\<Sqinter> (map snd \<Delta>) \<sqinter> \<Sqinter> (map snd (remdups \<psi>)) \<squnion> \<bottom>)"
          by simp
          hence \<star>:
            "\<turnstile> \<Sqinter> (map snd (remdups (\<Delta> @ \<psi>))) \<leftrightarrow> (\<Sqinter> (map snd \<Delta>) \<sqinter> \<Sqinter> (map snd (remdups \<psi>)))"
            by (metis (no_types, hide_lams)
                      biconditional_conjunction_weaken_rule
                      biconditional_symmetry_rule
                      biconditional_transitivity_rule
                      disjunction_def
                      double_negation_biconditional
                      negation_def)
          have "\<turnstile>    \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) (\<delta> # \<Delta>))) \<Psi>)
                  \<leftrightarrow> (\<Sqinter> (map snd (\<delta> # \<Delta>)) \<sqinter> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) \<Psi>))"
            using Cons by blast
          hence \<diamondsuit>: "\<turnstile>    \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) (\<delta> # \<Delta>))) \<Psi>)
                      \<leftrightarrow> ((snd \<delta> \<sqinter> \<Sqinter> (map snd \<Delta>)) \<sqinter> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) \<Psi>))"
            by simp
          show ?case
          proof (cases "\<delta> \<in> set \<psi>")
            assume "\<delta> \<in> set \<psi>"
            have "snd \<delta> \<in> set (map snd (remdups \<psi>))"
              using \<open>\<delta> \<in> set \<psi>\<close> by auto
            hence \<spadesuit>: "\<turnstile> \<Sqinter> (map snd (remdups \<psi>)) \<leftrightarrow> (snd \<delta> \<sqinter> \<Sqinter> (map snd (remdups \<psi>)))"
              using conj_absorption by blast
            have
              "\<turnstile>    (\<Sqinter> (map snd (remdups \<psi>)) \<leftrightarrow> (snd \<delta> \<sqinter> \<Sqinter> (map snd (remdups \<psi>))))
                 \<rightarrow> (\<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) (\<delta> # \<Delta>))) \<Psi>)
                        \<leftrightarrow> ((snd \<delta> \<sqinter> \<Sqinter> (map snd \<Delta>)) \<sqinter> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) \<Psi>)))
                 \<rightarrow> (\<Sqinter> (map snd (remdups (\<Delta> @ \<psi>))) \<leftrightarrow> (\<Sqinter> (map snd \<Delta>) \<sqinter> \<Sqinter> (map snd (remdups \<psi>))))
                 \<rightarrow>    (\<Sqinter> (map snd (remdups (\<Delta> @ \<psi>)))
                         \<squnion> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) (\<delta> # \<Delta>))) \<Psi>))
                    \<leftrightarrow> ((snd \<delta> \<sqinter> \<Sqinter> (map snd \<Delta>))
                         \<sqinter> (\<Sqinter> (map snd (remdups \<psi>)) \<squnion> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) \<Psi>)))"
            proof -
              let ?\<phi> =
                "   (\<^bold>\<langle>\<Sqinter> (map snd (remdups \<psi>))\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>snd \<delta>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> (map snd (remdups \<psi>))\<^bold>\<rangle>))
                 \<rightarrow>    (\<^bold>\<langle>\<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) (\<delta> # \<Delta>))) \<Psi>)\<^bold>\<rangle>
                    \<leftrightarrow> ((\<^bold>\<langle>snd \<delta>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> (map snd \<Delta>)\<^bold>\<rangle>) \<sqinter> \<^bold>\<langle>\<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) \<Psi>)\<^bold>\<rangle>))
                 \<rightarrow>    (\<^bold>\<langle>\<Sqinter> (map snd (remdups (\<Delta> @ \<psi>)))\<^bold>\<rangle>
                    \<leftrightarrow> (\<^bold>\<langle>\<Sqinter> (map snd \<Delta>)\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> (map snd (remdups \<psi>))\<^bold>\<rangle>))
                 \<rightarrow>    (\<^bold>\<langle>\<Sqinter> (map snd (remdups (\<Delta> @ \<psi>)))\<^bold>\<rangle>
                         \<squnion> \<^bold>\<langle>\<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) (\<delta> # \<Delta>))) \<Psi>)\<^bold>\<rangle>)
                    \<leftrightarrow> ((\<^bold>\<langle>snd \<delta>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> (map snd \<Delta>)\<^bold>\<rangle>)
                         \<sqinter> (\<^bold>\<langle>\<Sqinter> (map snd (remdups \<psi>))\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) \<Psi>)\<^bold>\<rangle>))"
              have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
              hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
              thus ?thesis by simp
            qed
            hence
              "\<turnstile>     (\<Sqinter> (map snd (remdups (\<Delta> @ \<psi>)))
                      \<squnion> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) (\<delta> # \<Delta>))) \<Psi>))
                  \<leftrightarrow> ((snd \<delta> \<sqinter> \<Sqinter> (map snd \<Delta>))
                      \<sqinter> (\<Sqinter> (map snd (remdups \<psi>)) \<squnion> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) \<Psi>)))"
              using \<star> \<diamondsuit> \<spadesuit> Modus_Ponens by blast
            thus ?thesis using \<open>\<delta> \<notin> set \<Delta>\<close> \<open>\<delta> \<in> set \<psi>\<close>
              by (simp add: \<dagger>)
          next
            assume "\<delta> \<notin> set \<psi>"
            have
              "\<turnstile>       (\<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) (\<delta> # \<Delta>))) \<Psi>)
                    \<leftrightarrow> ((snd \<delta> \<sqinter> \<Sqinter> (map snd \<Delta>)) \<sqinter> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) \<Psi>)))
                 \<rightarrow> (\<Sqinter> (map snd (remdups (\<Delta> @ \<psi>))) \<leftrightarrow> (\<Sqinter> (map snd \<Delta>) \<sqinter> \<Sqinter> (map snd (remdups \<psi>))))
                 \<rightarrow>    ((snd \<delta> \<sqinter> \<Sqinter> (map snd (remdups (\<Delta> @ \<psi>))))
                        \<squnion> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) (\<delta> # \<Delta>))) \<Psi>))
                    \<leftrightarrow> ((snd \<delta> \<sqinter> \<Sqinter> (map snd \<Delta>))
                        \<sqinter> (\<Sqinter> (map snd (remdups \<psi>)) \<squnion> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) \<Psi>)))"
            proof -
              let ?\<phi> =
                "      (\<^bold>\<langle>\<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) (\<delta> # \<Delta>))) \<Psi>)\<^bold>\<rangle>
                    \<leftrightarrow> ((\<^bold>\<langle>snd \<delta>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> (map snd \<Delta>)\<^bold>\<rangle>) \<sqinter> \<^bold>\<langle>\<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) \<Psi>)\<^bold>\<rangle>))
                 \<rightarrow>    (\<^bold>\<langle>\<Sqinter> (map snd (remdups (\<Delta> @ \<psi>)))\<^bold>\<rangle>
                    \<leftrightarrow> (\<^bold>\<langle>\<Sqinter> (map snd \<Delta>)\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> (map snd (remdups \<psi>))\<^bold>\<rangle>))
                 \<rightarrow>    ((\<^bold>\<langle>snd \<delta>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> (map snd (remdups (\<Delta> @ \<psi>)))\<^bold>\<rangle>)
                        \<squnion> \<^bold>\<langle>\<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) (\<delta> # \<Delta>))) \<Psi>)\<^bold>\<rangle>)
                    \<leftrightarrow> ((\<^bold>\<langle>snd \<delta>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> (map snd \<Delta>)\<^bold>\<rangle>)
                        \<sqinter> (\<^bold>\<langle>\<Sqinter> (map snd (remdups \<psi>))\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) \<Psi>)\<^bold>\<rangle>))"
              have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
              hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
              thus ?thesis by simp
            qed
            hence
              "\<turnstile>   ((snd \<delta> \<sqinter> \<Sqinter> (map snd (remdups (\<Delta> @ \<psi>))))
                    \<squnion> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups \<circ> (@) (\<delta> # \<Delta>))) \<Psi>))
                 \<leftrightarrow> ((snd \<delta> \<sqinter> \<Sqinter> (map snd \<Delta>))
                    \<sqinter> (\<Sqinter> (map snd (remdups \<psi>)) \<squnion> \<Squnion> (map (\<Sqinter> \<circ> (map snd \<circ> remdups)) \<Psi>)))"
              using \<star> \<diamondsuit> Modus_Ponens by blast
            then show ?thesis using \<open>\<delta> \<notin> set \<psi>\<close> \<open>\<delta> \<notin> set \<Delta>\<close> by (simp add: \<dagger>)
          qed
        qed
      qed
    }
    then show ?case by fastforce
  qed
  thus ?thesis by blast
qed

lemma remove1_remdups_removeAll: "remove1 x (remdups A) = remdups (removeAll x A)"
proof (induct A)
  case Nil
  then show ?case by simp
next
  case (Cons a A)
  then show ?case
    by (cases "a = x", (simp add: Cons)+)
qed

lemma mset_remdups:
  assumes "mset A = mset B"
  shows "mset (remdups A) = mset (remdups B)"
proof -
  have "\<forall> B. mset A = mset B \<longrightarrow> mset (remdups A) = mset (remdups B)"
  proof (induct A)
    case Nil
    then show ?case by simp
  next
    case (Cons a A)
    {
      fix B
      assume "mset (a # A) = mset B"
      hence "mset A = mset (remove1 a B)"
        by (metis add_mset_add_mset_same_iff
                  list.set_intros(1)
                  mset.simps(2)
                  mset_eq_perm
                  mset_eq_setD
                  perm_remove)
      hence "mset (remdups A) = mset (remdups (remove1 a B))"
        using Cons.hyps by blast
      hence "mset (remdups (a # (remdups A))) = mset (remdups (a # (remdups (remove1 a B))))"
        by (metis mset_eq_setD set_eq_iff_mset_remdups_eq list.simps(15))
      hence "  mset (remdups (a # (removeAll a (remdups A))))
             = mset (remdups (a # (removeAll a (remdups (remove1 a B)))))"
        by (metis insert_Diff_single list.set(2) set_eq_iff_mset_remdups_eq set_removeAll)
      hence "  mset (remdups (a # (remdups (removeAll a A))))
             = mset (remdups (a # (remdups (removeAll a (remove1 a B)))))"
        by (metis distinct_remdups distinct_remove1_removeAll remove1_remdups_removeAll)
      hence "mset (remdups (remdups (a # A))) = mset (remdups (remdups (a # (remove1 a B))))"
        by (metis \<open>mset A = mset (remove1 a B)\<close>
                  list.set(2)
                  mset_eq_setD
                  set_eq_iff_mset_remdups_eq)
      hence "mset (remdups (a # A)) = mset (remdups (a # (remove1 a B)))"
        by (metis remdups_remdups)
      hence "mset (remdups (a # A)) = mset (remdups B)"
        using \<open>mset (a # A) = mset B\<close> mset_eq_setD set_eq_iff_mset_remdups_eq by blast
    }
    then show ?case by simp
  qed
  thus ?thesis using assms by blast
qed

lemma mset_mset_map_snd_remdups:
  assumes "mset (map mset A) = mset (map mset B)"
  shows "mset (map (mset \<circ> (map snd) \<circ> remdups) A) = mset (map (mset \<circ> (map snd) \<circ> remdups) B)"
proof -
  {
    fix B :: "('a \<times> 'b) list list"
    fix b :: "('a \<times> 'b) list"
    assume "b \<in> set B"
    hence "  mset (map (mset \<circ> (map snd) \<circ> remdups) (b # (remove1 b B)))
         = mset (map (mset \<circ> (map snd) \<circ> remdups) B)"
    proof (induct B)
      case Nil
      then show ?case by simp
    next
      case (Cons b' B)
      then show ?case
      by (cases "b = b'", simp+)
    qed
  }
  note \<diamondsuit> = this
  have
    "\<forall> B :: ('a \<times> 'b) list list.
     mset (map mset A) = mset (map mset B)
       \<longrightarrow> mset (map (mset \<circ> (map snd) \<circ> remdups) A) = mset (map (mset \<circ> (map snd) \<circ> remdups) B)"
  proof (induct A)
    case Nil
    then show ?case by simp
  next
    case (Cons a A)
    {
      fix B
      assume \<spadesuit>: "mset (map mset (a # A)) = mset (map mset B)"
      hence "mset a \<in># mset (map mset B)"
        by (simp,
            metis \<spadesuit>
                  image_set
                  list.set_intros(1)
                  list.simps(9)
                  mset_eq_setD)
      from this obtain b where \<dagger>:
        "b \<in> set B"
        "mset a = mset b"
        by auto
      with \<spadesuit> have "mset (map mset A) = mset (remove1 (mset b) (map mset B))"
        by (simp add: union_single_eq_diff)
      moreover have "mset B = mset (b # remove1 b B)" using \<dagger> by simp
      hence "mset (map mset B) = mset (map mset (b # (remove1 b B)))"
        by (simp,
            metis image_mset_add_mset
                  mset.simps(2)
                  mset_remove1)
      ultimately have "mset (map mset A) = mset (map mset (remove1 b B))"
        by simp
      hence "  mset (map (mset \<circ> (map snd) \<circ> remdups) A)
             = mset (map (mset \<circ> (map snd) \<circ> remdups) (remove1 b B))"
        using Cons.hyps by blast
      moreover have "(mset \<circ> (map snd) \<circ> remdups) a = (mset \<circ> (map snd) \<circ> remdups) b"
        using \<dagger>(2) mset_remdups by fastforce
      ultimately have
        "  mset (map (mset \<circ> (map snd) \<circ> remdups) (a # A))
         = mset (map (mset \<circ> (map snd) \<circ> remdups) (b # (remove1 b B)))"
        by simp
      moreover have
        "  mset (map (mset \<circ> (map snd) \<circ> remdups) (b # (remove1 b B)))
         = mset (map (mset \<circ> (map snd) \<circ> remdups) B)"
        using \<dagger>(1) \<diamondsuit> by blast
      ultimately have
        "  mset (map (mset \<circ> (map snd) \<circ> remdups) (a # A))
         = mset (map (mset \<circ> (map snd) \<circ> remdups) B)"
        by simp
    }
    then show ?case by blast
  qed
  thus ?thesis using assms by blast
qed

lemma image_mset_cons_homomorphism:
  "image_mset mset (image_mset ((#) \<phi>) \<Phi>) = image_mset ((+) {# \<phi> #}) (image_mset mset \<Phi>)"
  by (induct \<Phi>, simp+)

lemma image_mset_append_homomorphism:
  "image_mset mset (image_mset ((@) \<Delta>) \<Phi>) = image_mset ((+) (mset \<Delta>)) (image_mset mset \<Phi>)"
  by (induct \<Phi>, simp+)

lemma image_mset_add_collapse:
  fixes A B :: "'a multiset"
  shows "image_mset ((+) A) (image_mset ((+) B) X) = image_mset ((+) (A + B)) X"
  by (induct X, simp, simp)

lemma mset_remdups_append_msub:
  "mset (remdups A) \<subseteq># mset (remdups (B @ A))"
proof -
  have "\<forall> B. mset (remdups A) \<subseteq># mset (remdups (B @ A))"
  proof (induct A)
    case Nil
    then show ?case by simp
  next
    case (Cons a A)
    {
      fix B
      have \<dagger>: "mset (remdups (B @ (a # A))) = mset (remdups (a # (B @ A)))"
        by (induct B, simp+)
      have "mset (remdups (a # A)) \<subseteq># mset (remdups (B @ (a # A)))"
      proof (cases "a \<in> set B \<and> a \<notin> set A")
        case True
        hence \<dagger>: "mset (remove1 a (remdups (B @ A))) = mset (remdups ((removeAll a B) @ A))"
          by (simp add: remove1_remdups_removeAll)
        hence "   (add_mset a (mset (remdups A)) \<subseteq># mset (remdups (B @ A)))
               = (mset (remdups A) \<subseteq># mset (remdups ((removeAll a B) @ A)))"
          using True
          by (simp add: insert_subset_eq_iff)
        then show ?thesis
          by (metis \<dagger> Cons True
                    Un_insert_right
                    list.set(2)
                    mset.simps(2)
                    mset_subset_eq_insertD
                    remdups.simps(2)
                    set_append
                    set_eq_iff_mset_remdups_eq
                    set_mset_mset set_remdups)
      next
        case False
        then show ?thesis using \<dagger> Cons by simp
      qed
    }
    thus ?case by blast
  qed
  thus ?thesis by blast
qed

lemma (in Classical_Propositional_Logic) optimal_witness_list_intersect_biconditional:
  assumes "mset \<Xi> \<subseteq># mset \<Gamma>"
      and "mset \<Phi> \<subseteq># mset (\<Gamma> \<ominus> \<Xi>)"
      and "mset \<Psi> \<subseteq># mset (\<WW>\<^sub>\<rightarrow> \<phi> \<Xi>)"
    shows "\<exists> \<Sigma>. \<turnstile> ((\<Phi> @ \<Psi>) :\<rightarrow> \<phi>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> \<Sigma>) \<rightarrow> \<phi>)
                \<and> (\<forall> \<sigma> \<in> set \<Sigma>. mset \<sigma> \<subseteq># mset \<Gamma> \<and> length \<sigma> + 1 \<ge> length (\<Phi> @ \<Psi>))"
proof -
  have "\<exists> \<Sigma>. \<turnstile> (\<Psi> :\<rightarrow> \<phi>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> \<Sigma>) \<rightarrow> \<phi>)
             \<and> (\<forall> \<sigma> \<in> set \<Sigma>. mset \<sigma> \<subseteq># mset \<Xi> \<and> length \<sigma> + 1 \<ge> length \<Psi>)"
  proof -
    from assms(3) obtain \<Psi>\<^sub>0 :: "('a list \<times> 'a) list"  where \<Psi>\<^sub>0:
      "mset \<Psi>\<^sub>0 \<subseteq># mset (\<VV> \<Xi>)"
      "map (\<lambda>(\<Psi>,\<psi>). (\<Psi> :\<rightarrow> \<phi> \<rightarrow> \<psi>)) \<Psi>\<^sub>0 = \<Psi>"
      using mset_sub_map_list_exists by fastforce
    let ?\<Pi>\<^sub>C = "\<lambda> (\<Delta>,\<delta>) \<Sigma>. (map ((#) (\<Delta>, \<delta>)) \<Sigma>) @ (map ((@) (\<VV> \<Delta>)) \<Sigma>)"
    let ?T\<^sub>\<Sigma> = "\<lambda> \<Psi>. foldr ?\<Pi>\<^sub>C \<Psi> [[]]"
    let ?\<Sigma> = "map (map snd \<circ> remdups) (?T\<^sub>\<Sigma> \<Psi>\<^sub>0)"
    have I: "\<turnstile> (\<Psi> :\<rightarrow> \<phi>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> ?\<Sigma>) \<rightarrow> \<phi>)"
    proof -
      let ?\<Sigma>\<^sub>\<alpha> = "map (map snd) (?T\<^sub>\<Sigma> \<Psi>\<^sub>0)"
      let ?\<Psi>' = "map (\<lambda>(\<Psi>,\<psi>). (\<Psi> :\<rightarrow> \<phi> \<rightarrow> \<psi>)) \<Psi>\<^sub>0"
      {
        fix \<Psi> :: "('a list \<times> 'a) list"
        let ?\<Sigma>\<^sub>\<alpha> = "map (map snd) (?T\<^sub>\<Sigma> \<Psi>)"
        let ?\<Sigma> = "map (map snd \<circ> remdups) (?T\<^sub>\<Sigma> \<Psi>)"
        have "\<turnstile> (\<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>) \<rightarrow> \<phi>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> ?\<Sigma>) \<rightarrow> \<phi>)"
        proof (induct \<Psi>)
          case Nil
          then show ?case by (simp add: biconditional_reflection)
        next
          case (Cons \<Delta>\<delta> \<Psi>)
          let ?\<Delta> = "fst \<Delta>\<delta>"
          let ?\<delta> = "snd \<Delta>\<delta>"
          let ?\<Sigma>\<^sub>\<alpha> = "map (map snd) (?T\<^sub>\<Sigma> \<Psi>)"
          let ?\<Sigma> = "map (map snd \<circ> remdups) (?T\<^sub>\<Sigma> \<Psi>)"
          let ?\<Sigma>\<^sub>\<alpha>' = "map (map snd) (?T\<^sub>\<Sigma> ((?\<Delta>,?\<delta>) # \<Psi>))"
          let ?\<Sigma>' = "map (map snd \<circ> remdups) (?T\<^sub>\<Sigma> ((?\<Delta>,?\<delta>) # \<Psi>))"
          {
            fix \<Delta> :: "'a list"
            fix \<delta> :: 'a
            let ?\<Sigma>\<^sub>\<alpha>' = "map (map snd) (?T\<^sub>\<Sigma> ((\<Delta>,\<delta>) # \<Psi>))"
            let ?\<Sigma>' = "map (map snd \<circ> remdups) (?T\<^sub>\<Sigma> ((\<Delta>,\<delta>) # \<Psi>))"
            let ?\<Phi> = "map (map snd \<circ> (@) [(\<Delta>, \<delta>)]) (?T\<^sub>\<Sigma> \<Psi>)"
            let ?\<Psi> = "map (map snd \<circ> (@) (\<VV> \<Delta>)) (?T\<^sub>\<Sigma> \<Psi>)"
            let ?\<Delta> = "map (map snd \<circ> remdups \<circ> (@) [(\<Delta>, \<delta>)]) (?T\<^sub>\<Sigma> \<Psi>)"
            let ?\<Omega> = "map (map snd \<circ> remdups \<circ> (@) (\<VV> \<Delta>)) (?T\<^sub>\<Sigma> \<Psi>)"
            have "\<turnstile> (\<Squnion> (map \<Sqinter> ?\<Phi> @ map \<Sqinter> ?\<Psi>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> ?\<Phi>) \<squnion> \<Squnion> (map \<Sqinter> ?\<Psi>))) \<rightarrow>
                    (\<Squnion> (map \<Sqinter> ?\<Delta> @ map \<Sqinter> ?\<Omega>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> ?\<Delta>) \<squnion> \<Squnion> (map \<Sqinter> ?\<Omega>))) \<rightarrow>
                    (\<Squnion> (map \<Sqinter> ?\<Phi>) \<leftrightarrow> (\<Sqinter> [\<delta>] \<sqinter> \<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>))) \<rightarrow>
                    (\<Squnion> (map \<Sqinter> ?\<Psi>) \<leftrightarrow> (\<Sqinter> \<Delta> \<sqinter> \<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>))) \<rightarrow>
                    (\<Squnion> (map \<Sqinter> ?\<Delta>) \<leftrightarrow> (\<Sqinter> [\<delta>] \<sqinter> \<Squnion> (map \<Sqinter> ?\<Sigma>))) \<rightarrow>
                    (\<Squnion> (map \<Sqinter> ?\<Omega>) \<leftrightarrow> (\<Sqinter> \<Delta> \<sqinter> \<Squnion> (map \<Sqinter> ?\<Sigma>))) \<rightarrow>
                    ((\<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>) \<rightarrow> \<phi>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> ?\<Sigma>) \<rightarrow> \<phi>)) \<rightarrow>
                    ((\<Squnion> (map \<Sqinter> ?\<Phi> @ map \<Sqinter> ?\<Psi>) \<rightarrow> \<phi>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> ?\<Delta> @ map \<Sqinter> ?\<Omega>) \<rightarrow> \<phi>))"
            proof -
              let ?\<phi> =
                "(\<^bold>\<langle>\<Squnion> (map \<Sqinter> ?\<Phi> @ map \<Sqinter> ?\<Psi>)\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<Squnion> (map \<Sqinter> ?\<Phi>)\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (map \<Sqinter> ?\<Psi>)\<^bold>\<rangle>)) \<rightarrow>
                 (\<^bold>\<langle>\<Squnion> (map \<Sqinter> ?\<Delta> @ map \<Sqinter> ?\<Omega>)\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<Squnion> (map \<Sqinter> ?\<Delta>)\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (map \<Sqinter> ?\<Omega>)\<^bold>\<rangle>)) \<rightarrow>
                 (\<^bold>\<langle>\<Squnion> (map \<Sqinter> ?\<Phi>)\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<Sqinter> [\<delta>]\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>)\<^bold>\<rangle>)) \<rightarrow>
                 (\<^bold>\<langle>\<Squnion> (map \<Sqinter> ?\<Psi>)\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<Sqinter> \<Delta>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>)\<^bold>\<rangle>)) \<rightarrow>
                 (\<^bold>\<langle>\<Squnion> (map \<Sqinter> ?\<Delta>)\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<Sqinter> [\<delta>]\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> (map \<Sqinter> ?\<Sigma>)\<^bold>\<rangle>)) \<rightarrow>
                 (\<^bold>\<langle>\<Squnion> (map \<Sqinter> ?\<Omega>)\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<Sqinter> \<Delta>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> (map \<Sqinter> ?\<Sigma>)\<^bold>\<rangle>)) \<rightarrow>
                 ((\<^bold>\<langle>\<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>)\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<phi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<Squnion> (map \<Sqinter> ?\<Sigma>)\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<phi>\<^bold>\<rangle>)) \<rightarrow>
                 ((\<^bold>\<langle>\<Squnion> (map \<Sqinter> ?\<Phi> @ map \<Sqinter> ?\<Psi>)\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<phi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<Squnion> (map \<Sqinter> ?\<Delta> @ map \<Sqinter> ?\<Omega>)\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<phi>\<^bold>\<rangle>))"
              have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
              hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
              thus ?thesis by simp
            qed
            moreover
            have "map snd (\<VV> \<Delta>) = \<Delta>" by (induct \<Delta>, auto)
            hence "\<turnstile> \<Squnion> (map \<Sqinter> ?\<Phi> @ map \<Sqinter> ?\<Psi>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> ?\<Phi>) \<squnion> \<Squnion> (map \<Sqinter> ?\<Psi>))"
                  "\<turnstile> \<Squnion> (map \<Sqinter> ?\<Delta> @ map \<Sqinter> ?\<Omega>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> ?\<Delta>) \<squnion> \<Squnion> (map \<Sqinter> ?\<Omega>))"
                  "\<turnstile> \<Squnion> (map \<Sqinter> ?\<Phi>) \<leftrightarrow> (\<Sqinter> [\<delta>] \<sqinter> \<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>))"
                  "\<turnstile> \<Squnion> (map \<Sqinter> ?\<Psi>) \<leftrightarrow> (\<Sqinter> \<Delta> \<sqinter> \<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>))"
                  "\<turnstile> \<Squnion> (map \<Sqinter> ?\<Delta>) \<leftrightarrow> (\<Sqinter> [\<delta>] \<sqinter> \<Squnion> (map \<Sqinter> ?\<Sigma>))"
                  "\<turnstile> \<Squnion> (map \<Sqinter> ?\<Omega>) \<leftrightarrow> (\<Sqinter> \<Delta> \<sqinter> \<Squnion> (map \<Sqinter> ?\<Sigma>))"
              using arbitrary_disj_concat_equiv
                    extract_inner_concat [where \<Delta> = "[(\<Delta>, \<delta>)]" and \<Psi> = "?T\<^sub>\<Sigma> \<Psi>"]
                    extract_inner_concat [where \<Delta> = "\<VV> \<Delta>" and \<Psi> = "?T\<^sub>\<Sigma> \<Psi>"]
                    extract_inner_concat_remdups [where \<Delta> = "[(\<Delta>, \<delta>)]" and \<Psi> = "?T\<^sub>\<Sigma> \<Psi>"]
                    extract_inner_concat_remdups [where \<Delta> = "\<VV> \<Delta>" and \<Psi> = "?T\<^sub>\<Sigma> \<Psi>"]
              by auto
            ultimately have
              "\<turnstile> ((\<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>) \<rightarrow> \<phi>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> ?\<Sigma>) \<rightarrow> \<phi>)) \<rightarrow>
                  (\<Squnion> (map \<Sqinter> ?\<Phi> @ map \<Sqinter> ?\<Psi>) \<rightarrow> \<phi>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> ?\<Delta> @ map \<Sqinter> ?\<Omega>) \<rightarrow> \<phi>)"
              using Modus_Ponens by blast
            moreover have "(#) (\<Delta>, \<delta>) = (@) [(\<Delta>, \<delta>)]" by fastforce
            ultimately have
              "\<turnstile> ((\<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>) \<rightarrow> \<phi>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> ?\<Sigma>) \<rightarrow> \<phi>)) \<rightarrow>
                 ((\<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>') \<rightarrow> \<phi>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> ?\<Sigma>') \<rightarrow> \<phi>))"
              by auto
          }
          hence
            "\<turnstile> ((\<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>') \<rightarrow> \<phi>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> ?\<Sigma>') \<rightarrow> \<phi>))"
            using Cons Modus_Ponens by blast
          moreover have "\<Delta>\<delta> = (?\<Delta>,?\<delta>)" by fastforce
          ultimately show ?case by metis
        qed
      }
      hence "\<turnstile> (\<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>) \<rightarrow> \<phi>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> ?\<Sigma>) \<rightarrow> \<phi>)" by blast
      moreover have "\<turnstile> (?\<Psi>' :\<rightarrow> \<phi>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>) \<rightarrow> \<phi>)"
      proof (induct \<Psi>\<^sub>0)
        case Nil
        have "\<turnstile> \<phi> \<leftrightarrow> ((\<top> \<squnion> \<bottom>) \<rightarrow> \<phi>)"
        proof -
          let ?\<phi> = "\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> ((\<top> \<squnion> \<bottom>) \<rightarrow> \<^bold>\<langle>\<phi>\<^bold>\<rangle>)"
          have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
          hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
          thus ?thesis by simp
        qed
        thus ?case by simp
      next
        case (Cons \<psi>\<^sub>0 \<Psi>\<^sub>0)
        let ?\<Xi> = "fst \<psi>\<^sub>0"
        let ?\<delta> = "snd \<psi>\<^sub>0"
        let ?\<Psi>' = "map (\<lambda>(\<Psi>,\<psi>). (\<Psi> :\<rightarrow> \<phi> \<rightarrow> \<psi>)) \<Psi>\<^sub>0"
        let ?\<Sigma>\<^sub>\<alpha> = "map (map snd) (?T\<^sub>\<Sigma> \<Psi>\<^sub>0)"
        {
          fix \<Xi> :: "'a list"
          have "map snd (\<VV> \<Xi>) = \<Xi>" by (induct \<Xi>, auto)
          hence "map snd \<circ> (@) (\<VV> \<Xi>) = (@) \<Xi> \<circ> map snd" by fastforce
        }
        moreover have "(map snd \<circ> (#) (?\<Xi>, ?\<delta>)) = (@) [?\<delta>] \<circ> map snd" by fastforce
        ultimately have \<dagger>:
          "map (map snd) (?T\<^sub>\<Sigma> (\<psi>\<^sub>0 # \<Psi>\<^sub>0)) = map ((#) ?\<delta>) ?\<Sigma>\<^sub>\<alpha> @ map ((@) ?\<Xi>) ?\<Sigma>\<^sub>\<alpha>"
          "map (\<lambda>(\<Psi>,\<psi>). (\<Psi> :\<rightarrow> \<phi> \<rightarrow> \<psi>)) (\<psi>\<^sub>0 # \<Psi>\<^sub>0) = ?\<Xi> :\<rightarrow> \<phi> \<rightarrow> ?\<delta> # ?\<Psi>'"
          by (simp add: case_prod_beta')+
        have A: "\<turnstile> (?\<Psi>' :\<rightarrow> \<phi>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>) \<rightarrow> \<phi>)" using Cons.hyps by auto
        have B: "\<turnstile> (?\<Xi> :\<rightarrow> \<phi>) \<leftrightarrow> (\<Sqinter> ?\<Xi> \<rightarrow> \<phi>)"
          by (simp add: list_curry_uncurry)
        have C: "\<turnstile>    \<Squnion> (map \<Sqinter> (map ((#) ?\<delta>) ?\<Sigma>\<^sub>\<alpha>) @ map \<Sqinter> (map ((@) ?\<Xi>) ?\<Sigma>\<^sub>\<alpha>))
                   \<leftrightarrow> (\<Squnion> (map \<Sqinter> (map ((#) ?\<delta>) ?\<Sigma>\<^sub>\<alpha>)) \<squnion> \<Squnion> (map \<Sqinter> (map ((@) ?\<Xi>) ?\<Sigma>\<^sub>\<alpha>)))"
          using arbitrary_disj_concat_equiv by blast
        have "map \<Sqinter> (map ((#) ?\<delta>) ?\<Sigma>\<^sub>\<alpha>) = (map ((\<sqinter>) ?\<delta>) (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>))" by auto
        hence D: "\<turnstile> \<Squnion> (map \<Sqinter> (map ((#) ?\<delta>) ?\<Sigma>\<^sub>\<alpha>)) \<leftrightarrow> (?\<delta> \<sqinter> \<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>))"
          using conj_extract by presburger
        have E: "\<turnstile> \<Squnion> (map \<Sqinter> (map ((@) ?\<Xi>) ?\<Sigma>\<^sub>\<alpha>)) \<leftrightarrow> (\<Sqinter> ?\<Xi> \<sqinter> \<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>))"
          using conj_multi_extract by blast
        have
          "\<turnstile>        (?\<Psi>' :\<rightarrow> \<phi>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>) \<rightarrow> \<phi>)
             \<rightarrow>     (?\<Xi> :\<rightarrow> \<phi>) \<leftrightarrow> (\<Sqinter> ?\<Xi> \<rightarrow> \<phi>)
             \<rightarrow>     \<Squnion> (map \<Sqinter> (map ((#) ?\<delta>) ?\<Sigma>\<^sub>\<alpha>) @ map \<Sqinter> (map ((@) ?\<Xi>) ?\<Sigma>\<^sub>\<alpha>))
                \<leftrightarrow> (\<Squnion> (map \<Sqinter> (map ((#) ?\<delta>) ?\<Sigma>\<^sub>\<alpha>)) \<squnion> \<Squnion> (map \<Sqinter> (map ((@) ?\<Xi>) ?\<Sigma>\<^sub>\<alpha>)))
             \<rightarrow>     \<Squnion> (map \<Sqinter> (map ((#) ?\<delta>) ?\<Sigma>\<^sub>\<alpha>)) \<leftrightarrow> (?\<delta> \<sqinter> \<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>))
             \<rightarrow>     \<Squnion> (map \<Sqinter> (map ((@) ?\<Xi>) ?\<Sigma>\<^sub>\<alpha>)) \<leftrightarrow> (\<Sqinter> ?\<Xi> \<sqinter> \<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>))
             \<rightarrow>    ((?\<Xi> :\<rightarrow> \<phi> \<rightarrow> ?\<delta>) \<rightarrow> ?\<Psi>' :\<rightarrow> \<phi>)
                \<leftrightarrow> (\<Squnion> (map \<Sqinter> (map ((#) ?\<delta>) ?\<Sigma>\<^sub>\<alpha>) @ map \<Sqinter> (map ((@) ?\<Xi>) ?\<Sigma>\<^sub>\<alpha>)) \<rightarrow> \<phi>)"
        proof -
          let ?\<phi> =
            "         \<^bold>\<langle>?\<Psi>' :\<rightarrow> \<phi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>)\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<phi>\<^bold>\<rangle>)
               \<rightarrow>     \<^bold>\<langle>(?\<Xi> :\<rightarrow> \<phi>)\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<Sqinter> ?\<Xi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<phi>\<^bold>\<rangle>)
               \<rightarrow>     \<^bold>\<langle>\<Squnion> (map \<Sqinter> (map ((#) ?\<delta>) ?\<Sigma>\<^sub>\<alpha>) @ map \<Sqinter> (map ((@) ?\<Xi>) ?\<Sigma>\<^sub>\<alpha>))\<^bold>\<rangle>
                  \<leftrightarrow> (\<^bold>\<langle>\<Squnion> (map \<Sqinter> (map ((#) ?\<delta>) ?\<Sigma>\<^sub>\<alpha>))\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (map \<Sqinter> (map ((@) ?\<Xi>) ?\<Sigma>\<^sub>\<alpha>))\<^bold>\<rangle>)
               \<rightarrow>     \<^bold>\<langle>\<Squnion> (map \<Sqinter> (map ((#) ?\<delta>) ?\<Sigma>\<^sub>\<alpha>))\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>?\<delta>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>)\<^bold>\<rangle>)
               \<rightarrow>     \<^bold>\<langle>\<Squnion> (map \<Sqinter> (map ((@) ?\<Xi>) ?\<Sigma>\<^sub>\<alpha>))\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<Sqinter> ?\<Xi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> (map \<Sqinter> ?\<Sigma>\<^sub>\<alpha>)\<^bold>\<rangle>)
               \<rightarrow>    ((\<^bold>\<langle>?\<Xi> :\<rightarrow> \<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>?\<delta>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>?\<Psi>' :\<rightarrow> \<phi>\<^bold>\<rangle>)
                  \<leftrightarrow> (\<^bold>\<langle>\<Squnion> (map \<Sqinter> (map ((#) ?\<delta>) ?\<Sigma>\<^sub>\<alpha>) @ map \<Sqinter> (map ((@) ?\<Xi>) ?\<Sigma>\<^sub>\<alpha>))\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<phi>\<^bold>\<rangle>)"
          have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
          hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
          thus ?thesis by simp
        qed
        hence
          "\<turnstile>    ((?\<Xi> :\<rightarrow> \<phi> \<rightarrow> ?\<delta>) \<rightarrow> ?\<Psi>' :\<rightarrow> \<phi>)
             \<leftrightarrow> (\<Squnion> (map \<Sqinter> (map ((#) ?\<delta>) ?\<Sigma>\<^sub>\<alpha>) @ map \<Sqinter> (map ((@) ?\<Xi>) ?\<Sigma>\<^sub>\<alpha>)) \<rightarrow> \<phi>)"
          using A B C D E Modus_Ponens by blast
        thus ?case using \<dagger> by simp
      qed
      ultimately show ?thesis using biconditional_transitivity_rule \<Psi>\<^sub>0 by blast
    qed
    have II: "\<forall> \<sigma> \<in> set ?\<Sigma>. length \<sigma> + 1 \<ge> length \<Psi>"
    proof -
      let ?\<M> = "length \<circ> fst"
      let ?\<S> = "sort_key (- ?\<M>)"
      let ?\<Sigma>' = "map (map snd \<circ> remdups) (?T\<^sub>\<Sigma> (?\<S> \<Psi>\<^sub>0))"
      have "mset \<Psi>\<^sub>0 = mset (?\<S> \<Psi>\<^sub>0)" by simp

      have "\<forall> \<Phi>. mset \<Psi>\<^sub>0 = mset \<Phi> \<longrightarrow> mset (map mset (?T\<^sub>\<Sigma> \<Psi>\<^sub>0)) = mset (map mset (?T\<^sub>\<Sigma> \<Phi>))"
      proof (induct \<Psi>\<^sub>0)
        case Nil
        then show ?case by simp
      next
        case (Cons \<psi> \<Psi>\<^sub>0)
        obtain \<Delta> \<delta> where "\<psi> = (\<Delta>,\<delta>)" by fastforce
        {
          fix \<Phi>
          assume "mset (\<psi> # \<Psi>\<^sub>0) = mset \<Phi>"
          hence "mset \<Psi>\<^sub>0 = mset (remove1 \<psi> \<Phi>)"
            by (simp add: union_single_eq_diff)
          have "\<psi> \<in> set \<Phi>" using \<open>mset (\<psi> # \<Psi>\<^sub>0) = mset \<Phi>\<close>
            using mset_eq_setD by fastforce
          hence "mset (map mset (?T\<^sub>\<Sigma> \<Phi>)) = mset (map mset (?T\<^sub>\<Sigma> (\<psi> # (remove1 \<psi> \<Phi>))))"
          proof (induct \<Phi>)
            case Nil
            then show ?case by simp
          next
            case (Cons \<phi> \<Phi>)
            then show ?case proof (cases "\<phi> = \<psi>")
              case True
              then show ?thesis by simp
            next
              case False
              let ?\<Sigma>' = "?T\<^sub>\<Sigma> (\<psi> # (remove1 \<psi> \<Phi>))"
              have \<dagger>: "mset (map mset ?\<Sigma>') = mset (map mset (?T\<^sub>\<Sigma> \<Phi>))"
                using Cons False by simp
              obtain \<Delta>' \<delta>'
                where "\<phi> = (\<Delta>',\<delta>')"
                by fastforce
              let ?\<Sigma> = "?T\<^sub>\<Sigma> (remove1 \<psi> \<Phi>)"
              let ?\<mm> = "image_mset mset"
              have
                "mset (map mset (?T\<^sub>\<Sigma> (\<psi> # remove1 \<psi> (\<phi> # \<Phi>)))) =
                 mset (map mset (?\<Pi>\<^sub>C \<psi> (?\<Pi>\<^sub>C \<phi> ?\<Sigma>)))"
                using False by simp
              hence "mset (map mset (?T\<^sub>\<Sigma> (\<psi> # remove1 \<psi> (\<phi> # \<Phi>)))) =
                     (?\<mm> \<circ> (image_mset ((#) \<psi>) \<circ> image_mset ((#) \<phi>))) (mset ?\<Sigma>) +
                     (?\<mm> \<circ> (image_mset ((#) \<psi>) \<circ> image_mset ((@) (\<VV> \<Delta>')))) (mset ?\<Sigma>) +
                     (?\<mm> \<circ> (image_mset ((@) (\<VV> \<Delta>)) \<circ> image_mset ((#) \<phi>))) (mset ?\<Sigma>) +
                     (?\<mm> \<circ> (image_mset ((@) (\<VV> \<Delta>)) \<circ> image_mset ((@) (\<VV> \<Delta>')))) (mset ?\<Sigma>)"
                using \<open>\<psi> = (\<Delta>,\<delta>)\<close> \<open>\<phi> = (\<Delta>',\<delta>')\<close>
                by (simp add: multiset.map_comp)
              hence "mset (map mset (?T\<^sub>\<Sigma> (\<psi> # remove1 \<psi> (\<phi> # \<Phi>)))) =
                     (?\<mm> \<circ> (image_mset ((#) \<phi>) \<circ> image_mset ((#) \<psi>))) (mset ?\<Sigma>) +
                     (?\<mm> \<circ> (image_mset ((@) (\<VV> \<Delta>')) \<circ> image_mset ((#) \<psi>))) (mset ?\<Sigma>) +
                     (?\<mm> \<circ> (image_mset ((#) \<phi>) \<circ> image_mset ((@) (\<VV> \<Delta>)))) (mset ?\<Sigma>) +
                     (?\<mm> \<circ> (image_mset ((@) (\<VV> \<Delta>')) \<circ> image_mset ((@) (\<VV> \<Delta>)))) (mset ?\<Sigma>)"
                by (simp add: image_mset_cons_homomorphism
                              image_mset_append_homomorphism
                              image_mset_add_collapse
                              add_mset_commute
                              add.commute)
              hence "mset (map mset (?T\<^sub>\<Sigma> (\<psi> # remove1 \<psi> (\<phi> # \<Phi>)))) =
                     (?\<mm> \<circ> (image_mset ((#) \<phi>))) (mset ?\<Sigma>') +
                     (?\<mm> \<circ> (image_mset ((@) (\<VV> \<Delta>')))) (mset ?\<Sigma>')"
                using \<open>\<psi> = (\<Delta>,\<delta>)\<close>
                by (simp add: multiset.map_comp)
              hence "mset (map mset (?T\<^sub>\<Sigma> (\<psi> # remove1 \<psi> (\<phi> # \<Phi>)))) =
                     image_mset ((+) {#\<phi>#}) (mset (map mset ?\<Sigma>')) +
                     image_mset ((+) (mset (\<VV> \<Delta>'))) (mset (map mset ?\<Sigma>'))"
                by (simp add: image_mset_cons_homomorphism
                              image_mset_append_homomorphism)
              hence "mset (map mset (?T\<^sub>\<Sigma> (\<psi> # remove1 \<psi> (\<phi> # \<Phi>)))) =
                     image_mset ((+) {#\<phi>#}) (mset (map mset (?T\<^sub>\<Sigma> \<Phi>))) +
                     image_mset ((+) (mset (\<VV> \<Delta>'))) (mset (map mset (?T\<^sub>\<Sigma> \<Phi>)))"
                using \<dagger> by auto
              hence "mset (map mset (?T\<^sub>\<Sigma> (\<psi> # remove1 \<psi> (\<phi> # \<Phi>)))) =
                     (?\<mm> \<circ> (image_mset ((#) \<phi>))) (mset (?T\<^sub>\<Sigma> \<Phi>)) +
                     (?\<mm> \<circ> (image_mset ((@) (\<VV> \<Delta>')))) (mset (?T\<^sub>\<Sigma> \<Phi>))"
                by (simp add: image_mset_cons_homomorphism
                              image_mset_append_homomorphism)
              thus ?thesis using \<open>\<phi> = (\<Delta>',\<delta>')\<close> by (simp add: multiset.map_comp)
            qed
          qed
          hence "  image_mset mset (image_mset ((#) \<psi>) (mset (?T\<^sub>\<Sigma> (remove1 \<psi> \<Phi>)))) +
                   image_mset mset (image_mset ((@) (\<VV> \<Delta>)) (mset (?T\<^sub>\<Sigma> (remove1 \<psi> \<Phi>))))
                 = image_mset mset (mset (?T\<^sub>\<Sigma> \<Phi>))"
            by (simp add: \<open>\<psi> = (\<Delta>,\<delta>)\<close> multiset.map_comp)
          hence
            "  image_mset ((+) {# \<psi> #}) (image_mset mset (mset (?T\<^sub>\<Sigma> (remove1 \<psi> \<Phi>)))) +
               image_mset ((+) (mset (\<VV> \<Delta>))) (image_mset mset (mset (?T\<^sub>\<Sigma> (remove1 \<psi> \<Phi>))))
             = image_mset mset (mset (?T\<^sub>\<Sigma> \<Phi>))"
            by (simp add: image_mset_cons_homomorphism image_mset_append_homomorphism)
          hence
            "image_mset ((+) {# \<psi> #}) (image_mset mset (mset (?T\<^sub>\<Sigma> \<Psi>\<^sub>0))) +
             image_mset ((+) (mset (\<VV> \<Delta>))) (image_mset mset (mset (?T\<^sub>\<Sigma> \<Psi>\<^sub>0)))
           = image_mset mset (mset (?T\<^sub>\<Sigma> \<Phi>))"
            using Cons \<open>mset \<Psi>\<^sub>0 = mset (remove1 \<psi> \<Phi>)\<close>
            by fastforce
          hence
            "image_mset mset (image_mset ((#) \<psi>) (mset (?T\<^sub>\<Sigma> \<Psi>\<^sub>0))) +
             image_mset mset (image_mset ((@) (\<VV> \<Delta>)) (mset (?T\<^sub>\<Sigma> \<Psi>\<^sub>0)))
           = image_mset mset (mset (?T\<^sub>\<Sigma> \<Phi>))"
            by (simp add: image_mset_cons_homomorphism image_mset_append_homomorphism)
          hence "mset (map mset (?T\<^sub>\<Sigma> (\<psi> # \<Psi>\<^sub>0))) = mset (map mset (?T\<^sub>\<Sigma> \<Phi>))"
            by (simp add: \<open>\<psi> = (\<Delta>,\<delta>)\<close> multiset.map_comp)
        }
        then show ?case by blast
      qed
      hence "mset (map mset (?T\<^sub>\<Sigma> \<Psi>\<^sub>0)) = mset (map mset (?T\<^sub>\<Sigma> (?\<S> \<Psi>\<^sub>0)))"
        using \<open>mset \<Psi>\<^sub>0 = mset (?\<S> \<Psi>\<^sub>0)\<close> by blast
      hence "   mset (map (mset \<circ> (map snd) \<circ> remdups) (?T\<^sub>\<Sigma> \<Psi>\<^sub>0))
              = mset (map (mset \<circ> (map snd) \<circ> remdups) (?T\<^sub>\<Sigma> (?\<S> \<Psi>\<^sub>0)))"
        using mset_mset_map_snd_remdups by blast
      hence "mset (map mset ?\<Sigma>) = mset (map mset ?\<Sigma>')"
        by (simp add: fun.map_comp)
      hence "set (map mset ?\<Sigma>) = set (map mset ?\<Sigma>')"
        using mset_eq_setD by blast
      hence "\<forall> \<sigma> \<in> set ?\<Sigma>. \<exists> \<sigma>' \<in> set ?\<Sigma>'. mset \<sigma> = mset \<sigma>'"
        by fastforce
      hence "\<forall> \<sigma> \<in> set ?\<Sigma>. \<exists> \<sigma>' \<in> set ?\<Sigma>'. length \<sigma> = length \<sigma>'"
        using mset_eq_length by blast
      have "mset (?\<S> \<Psi>\<^sub>0) \<subseteq># mset (\<VV> \<Xi>)"
        by (simp add: \<Psi>\<^sub>0(1))
      {
        fix n
        have "\<forall> \<Psi>. mset \<Psi> \<subseteq># mset (\<VV> \<Xi>) \<longrightarrow>
                    sorted (map (- ?\<M>) \<Psi>) \<longrightarrow>
                    length \<Psi> = n \<longrightarrow>
                    (\<forall> \<sigma>' \<in> set (map (map snd \<circ> remdups) (?T\<^sub>\<Sigma> \<Psi>)). length \<sigma>' + 1 \<ge> n)"
        proof (induct n)
          case 0
          then show ?case by simp
        next
          case (Suc n)
          {
            fix \<Psi> :: "('a list \<times> 'a) list"
            assume A: "mset \<Psi> \<subseteq># mset (\<VV> \<Xi>)"
               and B: "sorted (map (- ?\<M>) \<Psi>)"
               and C: "length \<Psi> = n + 1"
            obtain \<Delta> \<delta> where "(\<Delta>, \<delta>) = hd \<Psi>"
              using prod.collapse by blast
            let ?\<Psi>' = "tl \<Psi>"
            have "mset ?\<Psi>' \<subseteq># mset (\<VV> \<Xi>)" using A
              by (induct \<Psi>, simp, simp, meson mset_subset_eq_insertD subset_mset_def)
            moreover
            have "sorted (map (- ?\<M>) (tl \<Psi>))"
              using B
              by (simp add: map_tl sorted_tl)
            moreover have "length ?\<Psi>' = n" using C
              by simp
            ultimately have \<star>: "\<forall> \<sigma>' \<in> set (map (map snd \<circ> remdups) (?T\<^sub>\<Sigma> ?\<Psi>')). length \<sigma>' + 1 \<ge> n"
              using Suc
              by blast
            from C have "\<Psi> = (\<Delta>, \<delta>) # ?\<Psi>'"
              by (metis \<open>(\<Delta>, \<delta>) = hd \<Psi>\<close>
                        One_nat_def
                        add_is_0
                        list.exhaust_sel
                        list.size(3)
                        nat.simps(3))
            have "distinct ((\<Delta>, \<delta>) # ?\<Psi>')"
              using A \<open>\<Psi> = (\<Delta>, \<delta>) # ?\<Psi>'\<close>
                    core_optimal_pre_witness_distinct
                    mset_distinct_msub_down
              by fastforce
            hence "set ((\<Delta>, \<delta>) # ?\<Psi>') \<subseteq> set (\<VV> \<Xi>)"
              by (metis A \<open>\<Psi> = (\<Delta>, \<delta>) # ?\<Psi>'\<close>
                        Un_iff
                        mset_le_perm_append
                        perm_set_eq set_append
                        subsetI)
            hence "\<forall> (\<Delta>', \<delta>') \<in> set ?\<Psi>'. (\<Delta>, \<delta>) \<noteq> (\<Delta>', \<delta>')"
                  "\<forall> (\<Delta>', \<delta>') \<in> set (\<VV> \<Xi>). ((\<Delta>, \<delta>) \<noteq> (\<Delta>', \<delta>')) \<longrightarrow> (length \<Delta> \<noteq> length \<Delta>')"
                  "set ?\<Psi>' \<subseteq> set (\<VV> \<Xi>)"
              using core_optimal_pre_witness_length_iff_eq [where \<Psi>="\<Xi>"]
                    \<open>distinct ((\<Delta>, \<delta>) # ?\<Psi>')\<close>
              by auto
            hence "\<forall> (\<Delta>', \<delta>') \<in> set ?\<Psi>'. length \<Delta> \<noteq> length \<Delta>'"
                  "sorted (map (- ?\<M>) ((\<Delta>, \<delta>) # ?\<Psi>'))"
              using B \<open>\<Psi> = (\<Delta>, \<delta>) # ?\<Psi>'\<close>
              by (fastforce, auto)
            hence "\<forall> (\<Delta>', \<delta>') \<in> set ?\<Psi>'. length \<Delta> > length \<Delta>'"
              by fastforce
            {
              fix \<sigma>' :: "'a list"
              assume "\<sigma>' \<in> set (map (map snd \<circ> remdups) (?T\<^sub>\<Sigma> \<Psi>))"
              hence "\<sigma>' \<in> set (map (map snd \<circ> remdups) (?T\<^sub>\<Sigma> ((\<Delta>, \<delta>) # ?\<Psi>')))"
                using \<open>\<Psi> = (\<Delta>, \<delta>) # ?\<Psi>'\<close>
                by simp
              from this obtain \<psi> where \<psi>:
                "\<psi> \<in> set (?T\<^sub>\<Sigma> ?\<Psi>')"
                "\<sigma>' = (map snd \<circ> remdups \<circ> (#) (\<Delta>, \<delta>)) \<psi> \<or>
                 \<sigma>' = (map snd \<circ> remdups \<circ> (@) (\<VV> \<Delta>)) \<psi>"
                by fastforce
              hence "length \<sigma>' \<ge> n"
              proof (cases "\<sigma>' = (map snd \<circ> remdups \<circ> (#) (\<Delta>, \<delta>)) \<psi>")
                case True
                {
                  fix \<Psi> :: "('a list \<times> 'a) list"
                  fix n :: "nat"
                  assume "\<forall> (\<Delta>, \<delta>) \<in> set \<Psi>. n > length \<Delta>"
                  hence "\<forall> \<sigma> \<in> set (?T\<^sub>\<Sigma> \<Psi>). \<forall> (\<Delta>, \<delta>) \<in> set \<sigma>. n > length \<Delta>"
                  proof (induct \<Psi>)
                    case Nil
                    then show ?case by simp
                  next
                    case (Cons \<psi> \<Psi>)
                    obtain \<Delta> \<delta> where "\<psi> = (\<Delta>, \<delta>)"
                      by fastforce
                    hence "n > length \<Delta>" using Cons.prems by fastforce
                    have 0: "\<forall> \<sigma> \<in> set (?T\<^sub>\<Sigma> \<Psi>). \<forall> (\<Delta>', \<delta>') \<in> set \<sigma>. n > length \<Delta>'"
                      using Cons by simp
                    {
                      fix \<sigma> :: "('a list \<times> 'a) list"
                      fix \<psi>' :: "'a list \<times> 'a"
                      assume 1: "\<sigma> \<in> set (?T\<^sub>\<Sigma> (\<psi> # \<Psi>))"
                         and 2: "\<psi>' \<in> set \<sigma>"
                      obtain \<Delta>' \<delta>' where "\<psi>' = (\<Delta>', \<delta>')"
                        by fastforce
                      have 3: "\<sigma> \<in> (#) (\<Delta>, \<delta>) ` set (?T\<^sub>\<Sigma> \<Psi>) \<or> \<sigma> \<in> (@) (\<VV> \<Delta>) ` set (?T\<^sub>\<Sigma> \<Psi>)"
                        using 1 \<open>\<psi> = (\<Delta>, \<delta>)\<close> by simp
                      have "n > length \<Delta>'"
                      proof (cases "\<sigma> \<in> (#) (\<Delta>, \<delta>) ` set (?T\<^sub>\<Sigma> \<Psi>)")
                        case True
                        from this obtain \<sigma>' where
                          "set \<sigma> = insert (\<Delta>, \<delta>) (set \<sigma>')"
                          "\<sigma>' \<in> set (?T\<^sub>\<Sigma> \<Psi>)"
                          by auto
                        then show ?thesis
                          using 0 \<open>\<psi>' \<in> set \<sigma>\<close> \<open>\<psi>' = (\<Delta>', \<delta>')\<close> \<open>n > length \<Delta>\<close>
                          by auto
                      next
                        case False
                        from this and 3 obtain \<sigma>' where \<sigma>':
                          "set \<sigma> = set (\<VV> \<Delta>) \<union> (set \<sigma>')"
                          "\<sigma>' \<in> set (?T\<^sub>\<Sigma> \<Psi>)"
                          by auto
                        have "\<forall> (\<Delta>', \<delta>') \<in> set (\<VV> \<Delta>). length \<Delta> > length \<Delta>'"
                          by (metis (mono_tags, lifting)
                                     case_prodI2
                                     core_optimal_pre_witness_nonelement
                                     not_le)
                        hence "\<forall> (\<Delta>', \<delta>') \<in> set (\<VV> \<Delta>). n > length \<Delta>'"
                          using \<open>n > length \<Delta>\<close> by auto
                        then show ?thesis using 0 \<sigma>' \<open>\<psi>' \<in> set \<sigma>\<close> \<open>\<psi>' = (\<Delta>', \<delta>')\<close> by fastforce
                      qed
                      hence "n > length (fst \<psi>')" using \<open>\<psi>' = (\<Delta>', \<delta>')\<close> by fastforce
                    }
                    then show ?case by fastforce
                  qed
                }
                hence "\<forall> \<sigma> \<in> set (?T\<^sub>\<Sigma> ?\<Psi>'). \<forall> (\<Delta>', \<delta>') \<in> set \<sigma>. length \<Delta> > length \<Delta>'"
                  using \<open>\<forall> (\<Delta>', \<delta>') \<in> set ?\<Psi>'. length \<Delta> > length \<Delta>'\<close>
                  by blast
                then show ?thesis using True \<star> \<psi>(1) by fastforce
              next
                case False
                have "\<forall> (\<Delta>', \<delta>') \<in> set ?\<Psi>'. length \<Delta> \<ge> length \<Delta>'"
                  using \<open>\<forall> (\<Delta>', \<delta>') \<in> set ?\<Psi>'. length \<Delta> > length \<Delta>'\<close>
                  by auto
                hence "\<forall> (\<Delta>', \<delta>') \<in> set \<Psi>. length \<Delta> \<ge> length \<Delta>'"
                  using \<open>\<Psi> = (\<Delta>, \<delta>) # ?\<Psi>'\<close>
                  by (metis case_prodI2 eq_iff prod.sel(1) set_ConsD)
                hence "length \<Delta> + 1 \<ge> length \<Psi>"
                  using A core_optimal_pre_witness_pigeon_hole
                  by fastforce
                hence "length \<Delta> \<ge> n"
                  using C
                  by simp
                have "length \<Delta> = length (\<VV> \<Delta>)"
                  by (induct \<Delta>, simp+)
                hence "length (remdups (\<VV> \<Delta>)) = length (\<VV> \<Delta>)"
                  by (simp add: core_optimal_pre_witness_distinct)
                hence "length (remdups (\<VV> \<Delta>)) \<ge> n"
                  using \<open>length \<Delta> = length (\<VV> \<Delta>)\<close> \<open>n \<le> length \<Delta>\<close>
                  by linarith
                have "mset (remdups (\<VV> \<Delta> @ \<psi>)) = mset (remdups (\<psi> @ \<VV> \<Delta>))"
                  by (simp add: mset_remdups)
                hence "length (remdups (\<VV> \<Delta> @ \<psi>)) \<ge> length (remdups (\<VV> \<Delta>))"
                  by (metis le_cases length_sub_mset mset_remdups_append_msub size_mset)
                hence "length (remdups (\<VV> \<Delta> @ \<psi>)) \<ge> n"
                  using \<open>n \<le> length (remdups (\<VV> \<Delta>))\<close> dual_order.trans by blast
                thus ?thesis using False \<psi>(2)
                  by simp
              qed
            }
            hence "\<forall> \<sigma>' \<in> set (map (map snd \<circ> remdups) (?T\<^sub>\<Sigma> \<Psi>)). length \<sigma>' \<ge> n"
              by blast
          }
          then show ?case by fastforce
        qed
      }
      hence "\<forall> \<sigma>' \<in> set ?\<Sigma>'. length \<sigma>' + 1 \<ge> length (?\<S> \<Psi>\<^sub>0)"
        using \<open>mset (?\<S> \<Psi>\<^sub>0) \<subseteq># mset (\<VV> \<Xi>)\<close>
        by fastforce
      hence "\<forall> \<sigma>' \<in> set ?\<Sigma>'. length \<sigma>' + 1 \<ge> length \<Psi>\<^sub>0" by simp
      hence "\<forall> \<sigma> \<in> set ?\<Sigma>. length \<sigma> + 1 \<ge> length \<Psi>\<^sub>0"
        using \<open>\<forall> \<sigma> \<in> set ?\<Sigma>. \<exists> \<sigma>' \<in> set ?\<Sigma>'. length \<sigma> = length \<sigma>'\<close>
        by fastforce
      thus ?thesis using \<Psi>\<^sub>0 by fastforce
    qed
    have III: "\<forall> \<sigma> \<in> set ?\<Sigma>. mset \<sigma> \<subseteq># mset \<Xi>"
    proof -
      have "remdups (\<VV> \<Xi>) = \<VV> \<Xi>"
        by (simp add: core_optimal_pre_witness_distinct distinct_remdups_id)
      from \<Psi>\<^sub>0(1) have "set \<Psi>\<^sub>0 \<subseteq> set (\<VV> \<Xi>)"
        by (metis (no_types, lifting) \<open>remdups (\<VV> \<Xi>) = \<VV> \<Xi>\<close>
                                      mset_remdups_set_sub_iff
                                      mset_remdups_subset_eq
                                      subset_mset.dual_order.trans)
      hence "\<forall> \<sigma> \<in> set (?T\<^sub>\<Sigma> \<Psi>\<^sub>0). set \<sigma> \<subseteq> set (\<VV> \<Xi>)"
      proof (induct \<Psi>\<^sub>0)
        case Nil
        then show ?case by simp
      next
        case (Cons \<psi> \<Psi>\<^sub>0)
        hence "\<forall> \<sigma> \<in> set (?T\<^sub>\<Sigma> \<Psi>\<^sub>0). set \<sigma> \<subseteq> set (\<VV> \<Xi>)" by auto
        obtain \<Delta> \<delta> where "\<psi> = (\<Delta>,\<delta>)" by fastforce
        hence "(\<Delta>, \<delta>) \<in> set (\<VV> \<Xi>)" using Cons by simp
        {
          fix \<sigma> :: "('a list \<times> 'a) list"
          assume \<star>: "\<sigma> \<in> (#) (\<Delta>, \<delta>) ` set (?T\<^sub>\<Sigma> \<Psi>\<^sub>0) \<union> (@) (\<VV> \<Delta>) ` set (?T\<^sub>\<Sigma> \<Psi>\<^sub>0)"
          have "set \<sigma> \<subseteq> set (\<VV> \<Xi>)"
          proof (cases "\<sigma> \<in> (#) (\<Delta>, \<delta>) ` set (?T\<^sub>\<Sigma> \<Psi>\<^sub>0)")
            case True
            then show ?thesis
              using \<open>\<forall> \<sigma> \<in> set (?T\<^sub>\<Sigma> \<Psi>\<^sub>0). set \<sigma> \<subseteq> set (\<VV> \<Xi>)\<close> \<open>(\<Delta>, \<delta>) \<in> set (\<VV> \<Xi>)\<close>
              by fastforce
          next
            case False
            hence "\<sigma> \<in> (@) (\<VV> \<Delta>) ` set (?T\<^sub>\<Sigma> \<Psi>\<^sub>0)" using \<star> by simp
            moreover have "set (\<VV> \<Delta>) \<subseteq> set (\<VV> \<Xi>)"
              using core_optimal_pre_witness_element_inclusion \<open>(\<Delta>, \<delta>) \<in> set (\<VV> \<Xi>)\<close>
              by fastforce
            ultimately show ?thesis
              using \<open>\<forall> \<sigma> \<in> set (?T\<^sub>\<Sigma> \<Psi>\<^sub>0). set \<sigma> \<subseteq> set (\<VV> \<Xi>)\<close>
              by force
          qed
        }
        hence "\<forall>\<sigma>\<in>(#) (\<Delta>, \<delta>) ` set (?T\<^sub>\<Sigma> \<Psi>\<^sub>0) \<union> (@) (\<VV> \<Delta>) ` set (?T\<^sub>\<Sigma> \<Psi>\<^sub>0). set \<sigma> \<subseteq> set (\<VV> \<Xi>)"
          by auto
        thus ?case using \<open>\<psi> = (\<Delta>, \<delta>)\<close> by simp
      qed
      hence "\<forall> \<sigma> \<in> set (?T\<^sub>\<Sigma> \<Psi>\<^sub>0). mset (remdups \<sigma>) \<subseteq># mset (remdups (\<VV> \<Xi>))"
        using mset_remdups_set_sub_iff by blast
      hence "\<forall> \<sigma> \<in> set ?\<Sigma>. mset \<sigma> \<subseteq># mset (map snd (\<VV> \<Xi>))"
        using map_monotonic \<open>remdups (\<VV> \<Xi>) = \<VV> \<Xi>\<close>
        by auto
      moreover have "map snd (\<VV> \<Xi>) = \<Xi>" by (induct \<Xi>, simp+)
      ultimately show ?thesis by simp
    qed
    show ?thesis using I II III by fastforce
  qed
  from this obtain \<Sigma>\<^sub>0 where \<Sigma>\<^sub>0:
    "\<turnstile> (\<Psi> :\<rightarrow> \<phi>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> \<Sigma>\<^sub>0) \<rightarrow> \<phi>)"
    "\<forall> \<sigma> \<in> set \<Sigma>\<^sub>0. mset \<sigma> \<subseteq># mset \<Xi> \<and> length \<sigma> + 1 \<ge> length \<Psi>"
    by blast
  moreover
  have "(\<Phi> @ \<Psi>) :\<rightarrow> \<phi> = \<Phi> :\<rightarrow> (\<Psi> :\<rightarrow> \<phi>)" by (induct \<Phi>, simp+)
  hence "\<turnstile> ((\<Phi> @ \<Psi>) :\<rightarrow> \<phi>) \<leftrightarrow> (\<Sqinter> \<Phi> \<rightarrow> (\<Psi> :\<rightarrow> \<phi>))"
    by (simp add: list_curry_uncurry)
  moreover have "\<turnstile> (\<Psi> :\<rightarrow> \<phi>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> \<Sigma>\<^sub>0) \<rightarrow> \<phi>)
                \<rightarrow> (\<Phi> @ \<Psi>) :\<rightarrow> \<phi> \<leftrightarrow> (\<Sqinter> \<Phi> \<rightarrow> \<Psi> :\<rightarrow> \<phi>)
                \<rightarrow> (\<Phi> @ \<Psi>) :\<rightarrow> \<phi> \<leftrightarrow> ((\<Sqinter> \<Phi> \<sqinter> \<Squnion> (map \<Sqinter> \<Sigma>\<^sub>0)) \<rightarrow> \<phi>)"
  proof -
    let ?\<phi> = "\<^bold>\<langle>\<Psi> :\<rightarrow> \<phi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<Squnion> (map \<Sqinter> \<Sigma>\<^sub>0)\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<phi>\<^bold>\<rangle>)
           \<rightarrow> \<^bold>\<langle>(\<Phi> @ \<Psi>) :\<rightarrow> \<phi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<Sqinter> \<Phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<Psi> :\<rightarrow> \<phi>\<^bold>\<rangle>)
           \<rightarrow> \<^bold>\<langle>(\<Phi> @ \<Psi>) :\<rightarrow> \<phi>\<^bold>\<rangle> \<leftrightarrow> ((\<^bold>\<langle>\<Sqinter> \<Phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> (map \<Sqinter> \<Sigma>\<^sub>0)\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>\<phi>\<^bold>\<rangle>)"
    have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
    hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis by simp
  qed
  moreover
  let ?\<Sigma> = "map ((@) \<Phi>) \<Sigma>\<^sub>0"
  have "\<forall>\<phi> \<psi> \<chi>. \<turnstile> (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<chi> \<rightarrow> \<psi> \<or> \<not> \<turnstile> \<chi> \<rightarrow> \<phi>"
    by (meson Modus_Ponens flip_hypothetical_syllogism)
  hence "\<turnstile> ((\<Sqinter> \<Phi> \<sqinter> \<Squnion> (map \<Sqinter> \<Sigma>\<^sub>0)) \<rightarrow> \<phi>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> ?\<Sigma>) \<rightarrow> \<phi>)"
    using append_dnf_distribute biconditional_def by fastforce
  ultimately have "\<turnstile> (\<Phi> @ \<Psi>) :\<rightarrow> \<phi> \<leftrightarrow> (\<Squnion> (map \<Sqinter> ?\<Sigma>) \<rightarrow> \<phi>)"
    using Modus_Ponens biconditional_transitivity_rule
    by blast
  moreover
  {
    fix \<sigma>
    assume "\<sigma> \<in> set ?\<Sigma>"
    from this obtain \<sigma>\<^sub>0 where \<sigma>\<^sub>0: "\<sigma> = \<Phi> @ \<sigma>\<^sub>0" "\<sigma>\<^sub>0 \<in> set \<Sigma>\<^sub>0" by (simp, blast)
    hence "mset \<sigma>\<^sub>0 \<subseteq># mset \<Xi>" using \<Sigma>\<^sub>0(2) by blast
    hence "mset \<sigma> \<subseteq># mset (\<Phi> @ \<Xi>)" using \<sigma>\<^sub>0(1) by simp
    hence "mset \<sigma> \<subseteq># mset \<Gamma>" using assms(1) assms(2)
      by (simp, meson subset_mset.dual_order.trans subset_mset.le_diff_conv2)
    moreover
    have "length \<sigma> + 1 \<ge> length (\<Phi> @ \<Psi>)" using \<Sigma>\<^sub>0(2) \<sigma>\<^sub>0 by simp
    ultimately have "mset \<sigma> \<subseteq># mset \<Gamma>" "length \<sigma> + 1 \<ge> length (\<Phi> @ \<Psi>)" by auto
  }
  ultimately
  show ?thesis by blast
qed

lemma (in Classical_Propositional_Logic) unproving_core_optimal_witness:
  assumes "\<not> \<turnstile> \<phi>"
  shows "0 < (\<parallel> \<Gamma> \<parallel>\<^sub>\<phi>)
     =  (\<exists> \<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset \<Gamma> \<and>
              map (uncurry (\<squnion>)) \<Sigma> :\<turnstile> \<phi> \<and>
              1 + (\<parallel> map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> \<parallel>\<^sub>\<phi>) = \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>)"
proof (rule iffI)
  assume "0 < \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>"
  from this obtain \<Xi> where \<Xi>: "\<Xi> \<in> \<C> \<Gamma> \<phi>" "length \<Xi> < length \<Gamma>"
    using \<open>\<not> \<turnstile> \<phi>\<close>
          complement_core_size_def
          core_size_intro
          unproving_core_existence
    by fastforce
  from this obtain \<psi> where \<psi>: "\<psi> \<in> set (\<Gamma> \<ominus> \<Xi>)"
    by (metis \<open>0 < \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>\<close>
              less_not_refl
              list.exhaust
              list.set_intros(1)
              list.size(3)
              complement_core_size_intro)
  let ?\<Sigma> = "\<WW> \<phi> (\<psi> # \<Xi>)"
  let ?\<Sigma>\<^sub>A = "\<WW>\<^sub>\<squnion> \<phi> (\<psi> # \<Xi>)"
  let ?\<Sigma>\<^sub>B = "\<WW>\<^sub>\<rightarrow> \<phi> (\<psi> # \<Xi>)"
  have \<diamondsuit>: "mset (\<psi> # \<Xi>) \<subseteq># mset \<Gamma>"
           "\<psi> # \<Xi> :\<turnstile> \<phi>"
    using \<Xi>(1) \<psi>
          unproving_core_def
          list_deduction_theorem
          unproving_core_complement_deduction
          msub_listSubtract_elem_cons_msub [where \<Xi>="\<Xi>"]
    by blast+
  moreover have "map snd ?\<Sigma> = \<psi> # \<Xi>" by (induct \<Xi>, simp+)
  ultimately have "?\<Sigma>\<^sub>A :\<turnstile> \<phi>"
                  "mset (map snd ?\<Sigma>) \<subseteq># mset \<Gamma>"
    using core_optimal_witness_deduction
          list_deduction_def weak_biconditional_weaken
    by (metis+)
  moreover
  {
    let ?\<Gamma>' = "?\<Sigma>\<^sub>B @ \<Gamma> \<ominus> map snd ?\<Sigma>"
    have A: "length ?\<Sigma>\<^sub>B = 1 + length \<Xi>"
      by (induct \<Xi>, simp+)
    have B: "?\<Sigma>\<^sub>B \<in> \<C> ?\<Gamma>' \<phi>"
    proof -
      have "\<not> ?\<Sigma>\<^sub>B :\<turnstile> \<phi>"
        by (metis (no_types, lifting)
                  \<Xi>(1) \<open>?\<Sigma>\<^sub>A :\<turnstile> \<phi>\<close>
                  Modus_Ponens list_deduction_def
                  optimal_witness_split_identity
                  unproving_core_def
                  mem_Collect_eq)
      moreover have "mset ?\<Sigma>\<^sub>B \<subseteq># mset ?\<Gamma>'"
        by simp
      hence "\<forall> \<Psi>. mset \<Psi> \<subseteq># mset ?\<Gamma>' \<longrightarrow> \<not> \<Psi> :\<turnstile> \<phi> \<longrightarrow> length \<Psi> \<le> length ?\<Sigma>\<^sub>B"
      proof -
        have "\<forall> \<Psi> \<in> \<C> ?\<Gamma>' \<phi>. length \<Psi> = length ?\<Sigma>\<^sub>B"
        proof (rule ccontr)
          assume "\<not> (\<forall> \<Psi> \<in> \<C> ?\<Gamma>' \<phi>. length \<Psi> = length ?\<Sigma>\<^sub>B)"
          from this obtain \<Psi> where
            \<Psi>: "\<Psi> \<in> \<C> ?\<Gamma>' \<phi>"
               "length \<Psi> \<noteq> length ?\<Sigma>\<^sub>B"
            by blast
          have "length \<Psi> \<ge> length ?\<Sigma>\<^sub>B"
            using \<Psi>(1)
                  \<open>\<not> ?\<Sigma>\<^sub>B :\<turnstile> \<phi>\<close>
                  \<open>mset ?\<Sigma>\<^sub>B \<subseteq># mset ?\<Gamma>'\<close>
            unfolding unproving_core_def
            by blast
          hence "length \<Psi> > length ?\<Sigma>\<^sub>B"
            using \<Psi>(2)
            by linarith
          have "length \<Psi> = length (\<Psi> \<ominus> ?\<Sigma>\<^sub>B) + length (\<Psi> \<^bold>\<inter> ?\<Sigma>\<^sub>B)"
            (is "length \<Psi> = length ?A + length ?B")
            by (metis (no_types, lifting)
                      length_append
                      list_diff_intersect_comp
                      mset_append
                      mset_eq_length)
          {
            fix \<sigma>
            assume "mset \<sigma> \<subseteq># mset \<Gamma>"
                   "length \<sigma> + 1 \<ge> length (?A @ ?B)"
            hence "length \<sigma> + 1 \<ge> length \<Psi>"
              using \<open>length \<Psi> = length ?A + length ?B\<close>
              by simp
            hence "length \<sigma> + 1 > length ?\<Sigma>\<^sub>B"
              using \<open>length \<Psi> > length ?\<Sigma>\<^sub>B\<close> by linarith
            hence "length \<sigma> + 1 > length \<Xi> + 1"
              using A by simp
            hence "length \<sigma> > length \<Xi>" by linarith
            have "\<sigma> :\<turnstile> \<phi>"
            proof (rule ccontr)
              assume "\<not> \<sigma> :\<turnstile> \<phi>"
              hence "length \<sigma> \<le> length \<Xi>"
                using \<open>mset \<sigma> \<subseteq># mset \<Gamma>\<close> \<Xi>(1)
                unfolding unproving_core_def
                by blast
              thus "False" using \<open>length \<sigma> > length \<Xi>\<close> by linarith
            qed
          }
          moreover
          have "mset \<Psi> \<subseteq># mset ?\<Gamma>'"
               "\<not> \<Psi> :\<turnstile> \<phi>"
               "\<forall>\<Phi>. mset \<Phi> \<subseteq># mset ?\<Gamma>' \<and> \<not> \<Phi> :\<turnstile> \<phi> \<longrightarrow> length \<Phi> \<le> length \<Psi>"
            using \<Psi>(1) unproving_core_def by blast+
          hence "mset ?A \<subseteq># mset (\<Gamma> \<ominus> map snd ?\<Sigma>)"
            by (simp add: add.commute subset_eq_diff_conv)
          hence "mset ?A \<subseteq># mset (\<Gamma> \<ominus> (\<psi> # \<Xi>))"
            using \<open>map snd ?\<Sigma> = \<psi> # \<Xi>\<close> by metis
          moreover
          have "mset ?B \<subseteq># mset (\<WW>\<^sub>\<rightarrow> \<phi> (\<psi> # \<Xi>))"
            using list_intersect_right_project by blast
          ultimately obtain \<Sigma> where \<Sigma>: "\<turnstile> ((?A @ ?B) :\<rightarrow> \<phi>) \<leftrightarrow> (\<Squnion> (map \<Sqinter> \<Sigma>) \<rightarrow> \<phi>)"
                                       "\<forall>\<sigma>\<in>set \<Sigma>. \<sigma> :\<turnstile> \<phi>"
            using \<diamondsuit> optimal_witness_list_intersect_biconditional
            by metis
          hence "\<turnstile> \<Squnion> (map \<Sqinter> \<Sigma>) \<rightarrow> \<phi>"
            using weak_disj_of_conj_equiv by blast
          hence "?A @ ?B :\<turnstile> \<phi>"
            using \<Sigma>(1) Modus_Ponens list_deduction_def weak_biconditional_weaken
            by blast
          moreover have "set (?A @ ?B) = set \<Psi>"
            using list_diff_intersect_comp union_code set_mset_mset by metis
          hence "?A @ ?B :\<turnstile> \<phi> = \<Psi> :\<turnstile> \<phi>"
            using list_deduction_monotonic by blast
          ultimately have "\<Psi> :\<turnstile> \<phi>" by metis
          thus "False" using \<Psi>(1) unfolding unproving_core_def by blast
        qed
        moreover have "\<exists> \<Psi>. \<Psi> \<in> \<C> ?\<Gamma>' \<phi>"
          using assms unproving_core_existence by blast
        ultimately show ?thesis
          using unproving_core_def
          by fastforce
      qed
      ultimately show ?thesis
        unfolding unproving_core_def
        by fastforce
    qed
    have C: "\<forall>\<Xi> \<Gamma> \<phi>. \<Xi> \<in> \<C> \<Gamma> \<phi> \<longrightarrow> length \<Xi> = \<bar> \<Gamma> \<bar>\<^sub>\<phi>"
      using core_size_intro by blast
    then have D: "length \<Xi> = \<bar> \<Gamma> \<bar>\<^sub>\<phi>"
      using \<open>\<Xi> \<in> \<C> \<Gamma> \<phi>\<close> by blast
    have
      "\<forall>(\<Sigma> ::'a list) \<Gamma> n. (\<not> mset \<Sigma> \<subseteq># mset \<Gamma> \<or> length (\<Gamma> \<ominus> \<Sigma>) \<noteq> n) \<or> length \<Gamma> = n + length \<Sigma>"
      using listSubtract_msub_eq by blast
    then have E: "length \<Gamma> = length (\<Gamma> \<ominus> map snd (\<WW> \<phi> (\<psi> # \<Xi>))) + length (\<psi> # \<Xi>)"
      using \<open>map snd (\<WW> \<phi> (\<psi> # \<Xi>)) = \<psi> # \<Xi>\<close> \<open>mset (\<psi> # \<Xi>) \<subseteq># mset \<Gamma>\<close> by presburger
    have "1 + length \<Xi> = \<bar> \<WW>\<^sub>\<rightarrow> \<phi> (\<psi> # \<Xi>) @ \<Gamma> \<ominus> map snd (\<WW> \<phi> (\<psi> # \<Xi>)) \<bar>\<^sub>\<phi>"
      using C B A by presburger
    hence "1 + (\<parallel> map (uncurry (\<rightarrow>)) ?\<Sigma> @ \<Gamma> \<ominus> map snd ?\<Sigma> \<parallel>\<^sub>\<phi>) = \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>"
      using D E \<open>map snd (\<WW> \<phi> (\<psi> # \<Xi>)) = \<psi> # \<Xi>\<close> complement_core_size_def by force
  }
  ultimately
   show "\<exists> \<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset \<Gamma> \<and>
              map (uncurry (\<squnion>)) \<Sigma> :\<turnstile> \<phi> \<and>
              1 + (\<parallel> map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> \<parallel>\<^sub>\<phi>) = \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>"
  by metis
next
  assume "\<exists> \<Sigma>. mset (map snd \<Sigma>) \<subseteq># mset \<Gamma> \<and>
               map (uncurry (\<squnion>)) \<Sigma> :\<turnstile> \<phi> \<and>
               1 + (\<parallel> map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> \<parallel>\<^sub>\<phi>) = \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>"
  thus "0 < \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>"
    by auto
qed

primrec (in Minimal_Logic) core_witness :: "('a \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'a) list" ("\<UU>")
  where
    "\<UU> _ [] = []"
  | "\<UU> \<Sigma> (\<xi> # \<Xi>) = (case find (\<lambda> \<sigma>. \<xi> = snd \<sigma>) \<Sigma> of
                       None \<Rightarrow> \<UU> \<Sigma> \<Xi>
                     | Some \<sigma> \<Rightarrow> \<sigma> # (\<UU> (remove1 \<sigma> \<Sigma>) \<Xi>))"

lemma (in Minimal_Logic) core_witness_right_msub:
  "mset (map snd (\<UU> \<Sigma> \<Xi>)) \<subseteq># mset \<Xi>"
proof -
  have "\<forall> \<Sigma>. mset (map snd (\<UU> \<Sigma> \<Xi>)) \<subseteq># mset \<Xi>"
  proof (induct \<Xi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<xi> \<Xi>)
    {
      fix \<Sigma>
      have "mset (map snd (\<UU> \<Sigma> (\<xi> # \<Xi>))) \<subseteq># mset (\<xi> # \<Xi>)"
      proof (cases "find (\<lambda> \<sigma>. \<xi> = snd \<sigma>) \<Sigma>")
        case None
        then show ?thesis
          by (simp, metis Cons.hyps
                          add_mset_add_single
                          mset_map mset_subset_eq_add_left subset_mset.order_trans)
      next
        case (Some \<sigma>)
        note \<sigma> = this
        hence "\<xi> = snd \<sigma>"
          by (meson find_Some_predicate)
        moreover
        have "\<sigma> \<in> set \<Sigma>"
        using \<sigma>
        proof (induct \<Sigma>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<sigma>' \<Sigma>)
          then show ?case
            by (cases "\<xi> = snd \<sigma>'", simp+)
        qed
        ultimately show ?thesis using \<sigma> Cons.hyps by simp
      qed
    }
    then show ?case by simp
  qed
  thus ?thesis by simp
qed

lemma (in Minimal_Logic) core_witness_left_msub:
  "mset (\<UU> \<Sigma> \<Xi>) \<subseteq># mset \<Sigma>"
proof -
  have "\<forall> \<Sigma>. mset (\<UU> \<Sigma> \<Xi>) \<subseteq># mset \<Sigma>"
  proof (induct \<Xi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<xi> \<Xi>)
    {
      fix \<Sigma>
      have "mset (\<UU> \<Sigma> (\<xi> # \<Xi>)) \<subseteq># mset \<Sigma>"
      proof (cases "find (\<lambda> \<sigma>. \<xi> = snd \<sigma>) \<Sigma>")
        case None
        then show ?thesis using Cons.hyps by simp
      next
        case (Some \<sigma>)
        note \<sigma> = this
        hence "\<sigma> \<in> set \<Sigma>"
        proof (induct \<Sigma>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<sigma>' \<Sigma>)
          then show ?case
            by (cases "\<xi> = snd \<sigma>'", simp+)
        qed
        moreover from Cons.hyps have "mset (\<UU> (remove1 \<sigma> \<Sigma>) \<Xi>) \<subseteq># mset (remove1 \<sigma> \<Sigma>)"
          by blast
        hence "mset (\<UU> \<Sigma> (\<xi> # \<Xi>)) \<subseteq># mset (\<sigma> # remove1 \<sigma> \<Sigma>)" using \<sigma> by simp
        ultimately show ?thesis by simp
      qed
    }
    then show ?case by simp
  qed
  thus ?thesis by simp
qed

lemma (in Minimal_Logic) core_witness_right_projection:
  "mset (map snd (\<UU> \<Sigma> \<Xi>)) = mset ((map snd \<Sigma>) \<^bold>\<inter> \<Xi>)"
proof -
  have "\<forall> \<Sigma>. mset (map snd (\<UU> \<Sigma> \<Xi>)) = mset ((map snd \<Sigma>) \<^bold>\<inter> \<Xi>)"
  proof (induct \<Xi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<xi> \<Xi>)
    {
      fix \<Sigma>
      have "mset (map snd (\<UU> \<Sigma> (\<xi> # \<Xi>))) = mset (map snd \<Sigma> \<^bold>\<inter> \<xi> # \<Xi>)"
      proof (cases "find (\<lambda> \<sigma>. \<xi> = snd \<sigma>) \<Sigma>")
        case None
        hence "\<xi> \<notin> set (map snd \<Sigma>)"
        proof (induct \<Sigma>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<sigma> \<Sigma>)
          have "find (\<lambda>\<sigma>. \<xi> = snd \<sigma>) \<Sigma> = None"
               "\<xi> \<noteq> snd \<sigma>"
            using Cons.prems
            by (auto, metis Cons.prems find.simps(2) find_None_iff list.set_intros(1))
          then show ?case using Cons.hyps by simp
        qed
        then show ?thesis using None Cons.hyps by simp
      next
        case (Some \<sigma>)
        hence "\<sigma> \<in> set \<Sigma>" "\<xi> = snd \<sigma>"
          by (meson find_Some_predicate find_Some_set_membership)+
        moreover
        from \<open>\<sigma> \<in> set \<Sigma>\<close> have "mset \<Sigma> = mset (\<sigma> # (remove1 \<sigma> \<Sigma>))"
          by simp
        hence "mset (map snd \<Sigma>) = mset ((snd \<sigma>) # (remove1 (snd \<sigma>) (map snd \<Sigma>)))"
              "mset (map snd \<Sigma>) = mset (map snd (\<sigma> # (remove1 \<sigma> \<Sigma>)))"
          by (simp add: \<open>\<sigma> \<in> set \<Sigma>\<close>, metis map_monotonic subset_mset.eq_iff)
        hence "mset (map snd (remove1 \<sigma> \<Sigma>)) = mset (remove1 (snd \<sigma>) (map snd \<Sigma>))"
          by simp
        ultimately show ?thesis using Some Cons.hyps by simp
      qed
    }
    then show ?case by simp
  qed
  thus ?thesis by simp
qed

(* TODO: Move to logic *)
lemma (in Classical_Propositional_Logic) witness_list_implication_rule:
  "\<turnstile> (map (uncurry (\<squnion>)) \<Sigma> :\<rightarrow> \<phi>) \<rightarrow> \<Sqinter> (map (\<lambda> (\<chi>, \<xi>). (\<chi> \<rightarrow> \<xi>) \<rightarrow> \<phi>) \<Sigma>) \<rightarrow> \<phi>"
proof (induct \<Sigma>)
  case Nil
  then show ?case using Axiom_1 by simp
next
  case (Cons \<sigma> \<Sigma>)
  let ?\<chi> = "fst \<sigma>"
  let ?\<xi> = "snd \<sigma>"
  let ?\<Sigma>\<^sub>A = "map (uncurry (\<squnion>)) \<Sigma>"
  let ?\<Sigma>\<^sub>B = "map (\<lambda> (\<chi>, \<xi>). (\<chi> \<rightarrow> \<xi>) \<rightarrow> \<phi>) \<Sigma>"
  assume "\<turnstile> ?\<Sigma>\<^sub>A :\<rightarrow> \<phi> \<rightarrow> \<Sqinter> ?\<Sigma>\<^sub>B \<rightarrow> \<phi>"
  moreover have
    "\<turnstile> (?\<Sigma>\<^sub>A :\<rightarrow> \<phi> \<rightarrow> \<Sqinter> ?\<Sigma>\<^sub>B \<rightarrow> \<phi>)
     \<rightarrow> ((?\<chi> \<squnion> ?\<xi>) \<rightarrow> ?\<Sigma>\<^sub>A :\<rightarrow> \<phi>) \<rightarrow> (((?\<chi> \<rightarrow> ?\<xi>) \<rightarrow> \<phi>) \<sqinter> \<Sqinter> ?\<Sigma>\<^sub>B) \<rightarrow> \<phi>"
  proof -
      let ?\<phi> = "(\<^bold>\<langle>?\<Sigma>\<^sub>A :\<rightarrow> \<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<Sqinter> ?\<Sigma>\<^sub>B\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<phi>\<^bold>\<rangle>)
                \<rightarrow> (((\<^bold>\<langle>?\<chi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>?\<xi>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>?\<Sigma>\<^sub>A :\<rightarrow> \<phi>\<^bold>\<rangle>) \<rightarrow> (((\<^bold>\<langle>?\<chi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>?\<xi>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>\<phi>\<^bold>\<rangle>) \<sqinter> \<^bold>\<langle>\<Sqinter> ?\<Sigma>\<^sub>B\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>\<phi>\<^bold>\<rangle>)"
      have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
      hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
      thus ?thesis by simp
  qed
  ultimately have "\<turnstile> ((?\<chi> \<squnion> ?\<xi>) \<rightarrow> ?\<Sigma>\<^sub>A :\<rightarrow> \<phi>) \<rightarrow> (((?\<chi> \<rightarrow> ?\<xi>) \<rightarrow> \<phi>) \<sqinter> \<Sqinter> ?\<Sigma>\<^sub>B) \<rightarrow> \<phi>"
    using Modus_Ponens by blast
  moreover
  have "(\<lambda> \<sigma>. (fst \<sigma> \<rightarrow> snd \<sigma>) \<rightarrow> \<phi>) = (\<lambda> (\<chi>, \<xi>). (\<chi> \<rightarrow> \<xi>) \<rightarrow> \<phi>)"
       "uncurry (\<squnion>) = (\<lambda> \<sigma>. fst \<sigma> \<squnion> snd \<sigma>)"
    by fastforce+
  hence "(\<lambda> (\<chi>, \<xi>). (\<chi> \<rightarrow> \<xi>) \<rightarrow> \<phi>) \<sigma> = (?\<chi> \<rightarrow> ?\<xi>) \<rightarrow> \<phi>"
        "uncurry (\<squnion>) \<sigma> = ?\<chi> \<squnion> ?\<xi>"
    by metis+
  ultimately show ?case by simp
qed

lemma (in Classical_Propositional_Logic) witness_core_size_increase:
  assumes "\<not> \<turnstile> \<phi>"
      and "mset (map snd \<Sigma>) \<subseteq># mset \<Gamma>"
      and "map (uncurry (\<squnion>)) \<Sigma> :\<turnstile> \<phi>"
    shows "(\<bar> \<Gamma> \<bar>\<^sub>\<phi>) < (\<bar> map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> \<bar>\<^sub>\<phi>)"
proof -
  from \<open>\<not> \<turnstile> \<phi>\<close> obtain \<Xi> where \<Xi>: "\<Xi> \<in> \<C> \<Gamma> \<phi>"
    using unproving_core_existence by blast
  let ?\<Sigma>' = "\<Sigma> \<ominus> \<UU> \<Sigma> \<Xi>"
  let ?\<Sigma>\<Xi>' = "map (uncurry (\<squnion>)) (\<UU> \<Sigma> \<Xi>) @ map (uncurry (\<rightarrow>)) (\<UU> \<Sigma> \<Xi>)"
  have "mset \<Sigma> = mset (\<UU> \<Sigma> \<Xi> @ ?\<Sigma>')" by (simp add: core_witness_left_msub)
  hence "set (map (uncurry (\<squnion>)) \<Sigma>) = set (map (uncurry (\<squnion>)) ((\<UU> \<Sigma> \<Xi>) @ ?\<Sigma>'))"
    by (metis mset_map mset_eq_setD)
  hence "map (uncurry (\<squnion>)) ((\<UU> \<Sigma> \<Xi>) @ ?\<Sigma>') :\<turnstile> \<phi>"
    using list_deduction_monotonic assms(3)
    by blast
  hence "map (uncurry (\<squnion>)) (\<UU> \<Sigma> \<Xi>) @ map (uncurry (\<squnion>)) ?\<Sigma>' :\<turnstile> \<phi>" by simp
  moreover
  {
    fix \<Phi> \<Psi>
    have "((\<Phi> @ \<Psi>) :\<rightarrow> \<phi>) = (\<Phi> :\<rightarrow> (\<Psi> :\<rightarrow> \<phi>))"
      by (induct \<Phi>, simp+)
    hence "(\<Phi> @ \<Psi>) :\<turnstile> \<phi> = \<Phi> :\<turnstile> (\<Psi> :\<rightarrow> \<phi>)"
      unfolding list_deduction_def
      by (induct \<Phi>, simp+)
  }
  ultimately have "map (uncurry (\<squnion>)) (\<UU> \<Sigma> \<Xi>) :\<turnstile> map (uncurry (\<squnion>)) ?\<Sigma>' :\<rightarrow> \<phi>"
    by simp
  moreover have "set (map (uncurry (\<squnion>)) (\<UU> \<Sigma> \<Xi>)) \<subseteq> set ?\<Sigma>\<Xi>'"
    by simp
  ultimately have "?\<Sigma>\<Xi>' :\<turnstile> map (uncurry (\<squnion>)) ?\<Sigma>' :\<rightarrow> \<phi>"
    using list_deduction_monotonic by blast
  hence "?\<Sigma>\<Xi>' :\<turnstile> \<Sqinter> (map (\<lambda> (\<chi>, \<gamma>). (\<chi> \<rightarrow> \<gamma>) \<rightarrow> \<phi>) ?\<Sigma>') \<rightarrow> \<phi>"
    using list_deduction_modus_ponens
          list_deduction_weaken
          witness_list_implication_rule
    by blast
  hence "?\<Sigma>\<Xi>' $\<turnstile> [\<Sqinter> (map (\<lambda> (\<chi>, \<gamma>). (\<chi> \<rightarrow> \<gamma>) \<rightarrow> \<phi>) ?\<Sigma>') \<rightarrow> \<phi>]"
    using segmented_deduction_one_collapse by metis
  hence
    "?\<Sigma>\<Xi>' @ (map snd (\<UU> \<Sigma> \<Xi>)) \<ominus> (map snd (\<UU> \<Sigma> \<Xi>))
       $\<turnstile> [\<Sqinter> (map (\<lambda> (\<chi>, \<gamma>). (\<chi> \<rightarrow> \<gamma>) \<rightarrow> \<phi>) ?\<Sigma>') \<rightarrow> \<phi>]"
    by simp
  hence "map snd (\<UU> \<Sigma> \<Xi>) $\<turnstile> [\<Sqinter> (map (\<lambda> (\<chi>, \<gamma>). (\<chi> \<rightarrow> \<gamma>) \<rightarrow> \<phi>) ?\<Sigma>') \<rightarrow> \<phi>]"
    using segmented_witness_left_split [where \<Gamma>="map snd (\<UU> \<Sigma> \<Xi>)"
                                          and \<Sigma>="\<UU> \<Sigma> \<Xi>"]
    by fastforce
  hence "map snd (\<UU> \<Sigma> \<Xi>) $\<turnstile> [\<Sqinter> (map (\<lambda> (\<chi>, \<gamma>). (\<chi> \<rightarrow> \<gamma>) \<rightarrow> \<phi>) ?\<Sigma>') \<rightarrow> \<phi>]"
    using core_witness_right_projection by auto
  hence "map snd (\<UU> \<Sigma> \<Xi>) :\<turnstile> \<Sqinter> (map (\<lambda> (\<chi>, \<gamma>). (\<chi> \<rightarrow> \<gamma>) \<rightarrow> \<phi>) ?\<Sigma>') \<rightarrow> \<phi>"
    using segmented_deduction_one_collapse by blast
  hence \<star>:
    "map snd (\<UU> \<Sigma> \<Xi>) @ \<Xi> \<ominus> (map snd \<Sigma>) :\<turnstile> \<Sqinter> (map (\<lambda> (\<chi>, \<gamma>). (\<chi> \<rightarrow> \<gamma>) \<rightarrow> \<phi>) ?\<Sigma>') \<rightarrow> \<phi>"
    (is "?\<Xi>\<^sub>0 :\<turnstile> _")
    using list_deduction_monotonic
    by (metis (no_types, lifting) append_Nil2
                                  segmented_cancel
                                  segmented_deduction.simps(1)
                                  segmented_list_deduction_antitonic)
  have "mset \<Xi> = mset (\<Xi> \<ominus> (map snd \<Sigma>)) + mset (\<Xi> \<^bold>\<inter> (map snd \<Sigma>))"
    using list_diff_intersect_comp by blast
  hence "mset \<Xi> = mset ((map snd \<Sigma>) \<^bold>\<inter> \<Xi>) + mset (\<Xi> \<ominus> (map snd \<Sigma>))"
    by (metis subset_mset.inf_commute list_intersect_mset_homomorphism union_commute)
  hence "mset \<Xi> = mset (map snd (\<UU> \<Sigma> \<Xi>)) + mset (\<Xi> \<ominus> (map snd \<Sigma>))"
    using core_witness_right_projection by simp
  hence "mset \<Xi> = mset ?\<Xi>\<^sub>0"
    by simp
  hence "set \<Xi> = set ?\<Xi>\<^sub>0"
    by (metis mset_eq_setD)
  have "\<not> ?\<Xi>\<^sub>0 :\<turnstile> \<Sqinter> (map (\<lambda> (\<chi>, \<gamma>). (\<chi> \<rightarrow> \<gamma>) \<rightarrow> \<phi>) ?\<Sigma>')"
  proof (rule notI)
    assume "?\<Xi>\<^sub>0 :\<turnstile> \<Sqinter> (map (\<lambda> (\<chi>, \<gamma>). (\<chi> \<rightarrow> \<gamma>) \<rightarrow> \<phi>) ?\<Sigma>')"
    hence "?\<Xi>\<^sub>0 :\<turnstile> \<phi>"
      using \<star> list_deduction_modus_ponens by blast
    hence "\<Xi> :\<turnstile> \<phi>"
      using list_deduction_monotonic \<open>set \<Xi> = set ?\<Xi>\<^sub>0\<close> by blast
    thus "False"
      using \<Xi> unproving_core_def by blast
  qed
  moreover
  have "mset (map snd (\<UU> \<Sigma> \<Xi>)) \<subseteq># mset ?\<Xi>\<^sub>0"
       "mset (map (uncurry (\<rightarrow>)) (\<UU> \<Sigma> \<Xi>) @ ?\<Xi>\<^sub>0 \<ominus> map snd (\<UU> \<Sigma> \<Xi>))
      = mset (map (uncurry (\<rightarrow>)) (\<UU> \<Sigma> \<Xi>) @ \<Xi> \<ominus> (map snd \<Sigma>))"
       (is "_ = mset ?\<Xi>\<^sub>1")
    by auto
  hence "?\<Xi>\<^sub>1 \<preceq> ?\<Xi>\<^sub>0"
    by (metis add.commute
              witness_stronger_theory
              add_diff_cancel_right'
              listSubtract.simps(1)
              listSubtract_mset_homomorphism
              list_diff_intersect_comp
              list_intersect_right_project
              msub_stronger_theory_intro
              stronger_theory_combine
              stronger_theory_empty_list_intro
              self_append_conv)
  ultimately have
    "\<not> ?\<Xi>\<^sub>1 :\<turnstile> \<Sqinter> (map (\<lambda> (\<chi>, \<gamma>). (\<chi> \<rightarrow> \<gamma>) \<rightarrow> \<phi>) ?\<Sigma>')"
    using stronger_theory_deduction_monotonic by blast
  from this obtain \<chi> \<gamma> where
    "(\<chi>,\<gamma>) \<in> set ?\<Sigma>'"
    "\<not> (\<chi> \<rightarrow> \<gamma>) # ?\<Xi>\<^sub>1 :\<turnstile> \<phi>"
    using list_deduction_theorem
    by fastforce
  have "mset (\<chi> \<rightarrow> \<gamma> # ?\<Xi>\<^sub>1) \<subseteq># mset (map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma>)"
  proof -
    let ?A = "map (uncurry (\<rightarrow>)) \<Sigma>"
    let ?B = "map (uncurry (\<rightarrow>)) (\<UU> \<Sigma> \<Xi>)"
    have "(\<chi>,\<gamma>) \<in> (set \<Sigma> - set (\<UU> \<Sigma> \<Xi>))"
    proof -
      from \<open>(\<chi>,\<gamma>) \<in> set ?\<Sigma>'\<close> have "\<gamma> \<in># mset (map snd (\<Sigma> \<ominus> \<UU> \<Sigma> \<Xi>))"
        by (metis set_mset_mset image_eqI set_map snd_conv)
      hence "\<gamma> \<in># mset (map snd \<Sigma> \<ominus> map snd (\<UU> \<Sigma> \<Xi>))"
        by (metis core_witness_left_msub map_listSubtract_mset_equivalence)
      hence "\<gamma> \<in># mset (map snd \<Sigma> \<ominus> (map snd \<Sigma> \<^bold>\<inter> \<Xi>))"
        by (metis core_witness_right_projection listSubtract_mset_homomorphism)
      hence "\<gamma> \<in># mset (map snd \<Sigma> \<ominus> \<Xi>)"
        by (metis add_diff_cancel_right'
                  listSubtract_mset_homomorphism
                  list_diff_intersect_comp)
      moreover from assms(2) have "mset (map snd \<Sigma> \<ominus> \<Xi>) \<subseteq># mset (\<Gamma> \<ominus> \<Xi>)"
        by (simp, metis listSubtract_monotonic listSubtract_mset_homomorphism mset_map)
      ultimately have "\<gamma> \<in># mset (\<Gamma> \<ominus> \<Xi>)"
        by (simp add: mset_subset_eqD)
      hence "\<gamma> \<in> set (\<Gamma> \<ominus> \<Xi>)"
        using set_mset_mset by fastforce
      hence "\<gamma> \<in> set \<Gamma> - set \<Xi>"
        using \<Xi> by simp
      hence "\<gamma> \<notin> set \<Xi>"
        by blast
      hence "\<forall> \<Sigma>. (\<chi>,\<gamma>) \<notin> set (\<UU> \<Sigma> \<Xi>)"
      proof (induct \<Xi>)
        case Nil
        then show ?case by simp
      next
        case (Cons \<xi> \<Xi>)
        {
          fix \<Sigma>
          have "(\<chi>, \<gamma>) \<notin> set (\<UU> \<Sigma> (\<xi> # \<Xi>))"
          proof (cases "find (\<lambda>\<sigma>. \<xi> = snd \<sigma>) \<Sigma>")
            case None
            then show ?thesis using Cons by simp
          next
            case (Some \<sigma>)
            moreover from this have "snd \<sigma> = \<xi>"
              using find_Some_predicate by fastforce
            with Cons.prems have "\<sigma> \<noteq> (\<chi>,\<gamma>)" by fastforce
            ultimately show ?thesis using Cons by simp
          qed
        }
        then show ?case by blast
      qed
      moreover from \<open>(\<chi>,\<gamma>) \<in> set ?\<Sigma>'\<close> have "(\<chi>,\<gamma>) \<in> set \<Sigma>"
        by (meson listSubtract_set_trivial_upper_bound subsetCE)
      ultimately show ?thesis by fastforce
    qed
    with \<open>(\<chi>, \<gamma>) \<in> set ?\<Sigma>'\<close> have "mset ((\<chi>,\<gamma>) # \<UU> \<Sigma> \<Xi>) \<subseteq># mset \<Sigma>"
      by (meson core_witness_left_msub msub_listSubtract_elem_cons_msub)
    hence "mset (\<chi> \<rightarrow> \<gamma> # ?B) \<subseteq># mset (map (uncurry (\<rightarrow>)) \<Sigma>)"
      by (metis (no_types, lifting) \<open>(\<chi>, \<gamma>) \<in> set ?\<Sigma>'\<close>
                                    core_witness_left_msub
                                    map_listSubtract_mset_equivalence
                                    map_monotonic
                                    mset_eq_setD msub_listSubtract_elem_cons_msub
                                    pair_imageI
                                    set_map
                                    uncurry_def)
    moreover
    have "mset \<Xi> \<subseteq># mset \<Gamma>"
      using \<Xi> unproving_core_def
      by blast
    hence "mset (\<Xi> \<ominus> (map snd \<Sigma>)) \<subseteq># mset (\<Gamma> \<ominus> (map snd \<Sigma>))"
      using listSubtract_monotonic by blast
    ultimately show ?thesis
      using subset_mset.add_mono by fastforce
  qed
  moreover have "length ?\<Xi>\<^sub>1 = length ?\<Xi>\<^sub>0"
    by simp
  hence "length ?\<Xi>\<^sub>1 = length \<Xi>"
    using \<open>mset \<Xi> = mset ?\<Xi>\<^sub>0\<close> mset_eq_length by fastforce
  hence "length ((\<chi> \<rightarrow> \<gamma>) # ?\<Xi>\<^sub>1) = length \<Xi> + 1"
    by simp
  hence "length ((\<chi> \<rightarrow> \<gamma>) # ?\<Xi>\<^sub>1) = (\<bar> \<Gamma> \<bar>\<^sub>\<phi>) + 1"
    using \<Xi>
    by (simp add: core_size_intro)
  moreover from \<open>\<not> \<turnstile> \<phi>\<close> obtain \<Omega> where \<Omega>: "\<Omega> \<in> \<C> (map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma>) \<phi>"
    using unproving_core_existence by blast
  ultimately have "length \<Omega> \<ge> (\<bar> \<Gamma> \<bar>\<^sub>\<phi>) + 1"
    using unproving_core_def
    by (metis (no_types, lifting) \<open>\<not> \<chi> \<rightarrow> \<gamma> # ?\<Xi>\<^sub>1 :\<turnstile> \<phi>\<close> mem_Collect_eq)
  thus ?thesis
    using \<Omega> core_size_intro by auto
qed

lemma (in Classical_Propositional_Logic) unproving_core_stratified_deduction_lower_bound:
  assumes "\<not> \<turnstile> \<phi>"
    shows "(\<Gamma> #\<turnstile> n \<phi>) = (n \<le> \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>)"
proof -
  have "\<forall> \<Gamma>. (\<Gamma> #\<turnstile> n \<phi>) = (n \<le> \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>)"
  proof (induct n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    {
      fix \<Gamma>
      assume "\<Gamma> #\<turnstile> (Suc n) \<phi>"
      from this obtain \<Sigma> where \<Sigma>:
        "mset (map snd \<Sigma>) \<subseteq># mset \<Gamma>"
        "map (uncurry (\<squnion>)) \<Sigma> :\<turnstile> \<phi>"
        "map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> (map snd \<Sigma>) #\<turnstile> n \<phi>"
        by fastforce
      let ?\<Gamma>' = "map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> (map snd \<Sigma>)"
      have "length \<Gamma> = length ?\<Gamma>'"
        using \<Sigma>(1) listSubtract_msub_eq by fastforce
      hence "(\<parallel> \<Gamma> \<parallel>\<^sub>\<phi>) > (\<parallel> ?\<Gamma>' \<parallel>\<^sub>\<phi>)"
        by (metis \<Sigma>(1) \<Sigma>(2) \<open>\<not> \<turnstile> \<phi>\<close>
                  witness_core_size_increase
                  length_core_decomposition
                  add_less_cancel_right
                  nat_add_left_cancel_less)
      with \<Sigma>(3) Suc.hyps have "Suc n \<le> \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>"
        by auto
    }
    moreover
    {
      fix \<Gamma>
      assume "Suc n \<le> \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>"
      from this obtain \<Sigma> where \<Sigma>:
        "mset (map snd \<Sigma>) \<subseteq># mset \<Gamma>"
        "map (uncurry (\<squnion>)) \<Sigma> :\<turnstile> \<phi>"
        "1 + (\<parallel> map (uncurry (\<rightarrow>)) \<Sigma> @ \<Gamma> \<ominus> map snd \<Sigma> \<parallel>\<^sub>\<phi>) = \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>"
        (is "1 + (\<parallel> ?\<Gamma>' \<parallel>\<^sub>\<phi>) = \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>")
        by (metis Suc_le_D assms unproving_core_optimal_witness zero_less_Suc)
      have "n \<le> \<parallel> ?\<Gamma>' \<parallel>\<^sub>\<phi>"
        using \<Sigma>(3) \<open>Suc n \<le> \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>\<close> by linarith
      hence "?\<Gamma>' #\<turnstile> n \<phi>" using Suc by blast
      hence "\<Gamma> #\<turnstile> (Suc n) \<phi>" using \<Sigma>(1) \<Sigma>(2) by fastforce
    }
    ultimately show ?case by metis
  qed
  thus ?thesis by auto
qed

lemma (in Classical_Propositional_Logic) stratified_deduction_tautology_equiv:
  "(\<forall> n. \<Gamma> #\<turnstile> n \<phi>) = \<turnstile> \<phi>"
proof (cases "\<turnstile> \<phi>")
  case True
  then show ?thesis
    by (simp add: stratified_deduction_tautology_weaken)
next
  case False
  have "\<not> \<Gamma> #\<turnstile> (1 + length \<Gamma>) \<phi>"
  proof (rule notI)
    assume "\<Gamma> #\<turnstile> (1 + length \<Gamma>) \<phi>"
    hence "1 + length \<Gamma> \<le> \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>"
      using \<open>\<not> \<turnstile> \<phi>\<close> unproving_core_stratified_deduction_lower_bound by blast
    hence "1 + length \<Gamma> \<le> length \<Gamma>"
      using complement_core_size_def by fastforce
    thus "False" by linarith
  qed
  then show ?thesis
    using \<open>\<not> \<turnstile> \<phi>\<close> by blast
qed

lemma (in Classical_Propositional_Logic) unproving_core_max_stratified_deduction:
  "\<Gamma> #\<turnstile> n \<phi> = (\<forall> \<Phi> \<in> \<C> \<Gamma> \<phi>. n \<le> length (\<Gamma> \<ominus> \<Phi>))"
proof (cases "\<turnstile> \<phi>")
  case True
  from \<open>\<turnstile> \<phi>\<close> have "\<Gamma> #\<turnstile> n \<phi>"
    using stratified_deduction_tautology_weaken
    by blast
  moreover from \<open>\<turnstile> \<phi>\<close> have "\<C> \<Gamma> \<phi> = {}"
    using unproving_core_existence by auto
  hence "\<forall> \<Phi> \<in> \<C> \<Gamma> \<phi>. n \<le> length (\<Gamma> \<ominus> \<Phi>)" by blast
  ultimately show ?thesis by meson
next
  case False
  from \<open>\<not> \<turnstile> \<phi>\<close> have "(\<Gamma> #\<turnstile> n \<phi>) = (n \<le> \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>)"
    by (simp add: unproving_core_stratified_deduction_lower_bound)
  moreover have "(n \<le> \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>) = (\<forall> \<Phi> \<in> \<C> \<Gamma> \<phi>. n \<le> length (\<Gamma> \<ominus> \<Phi>))"
  proof (rule iffI)
    assume "n \<le> \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>"
    {
      fix \<Phi>
      assume "\<Phi> \<in> \<C> \<Gamma> \<phi>"
      hence "n \<le> length (\<Gamma> \<ominus> \<Phi>)"
        using \<open>n \<le> \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>\<close> complement_core_size_intro by auto
    }
    thus "\<forall>\<Phi> \<in> \<C> \<Gamma> \<phi>. n \<le> length (\<Gamma> \<ominus> \<Phi>)" by blast
  next
    assume "\<forall>\<Phi> \<in> \<C> \<Gamma> \<phi>. n \<le> length (\<Gamma> \<ominus> \<Phi>)"
    with \<open>\<not> \<turnstile> \<phi>\<close> obtain \<Phi> where
      "\<Phi> \<in> \<C> \<Gamma> \<phi>"
      "n \<le> length (\<Gamma> \<ominus> \<Phi>)"
      using unproving_core_existence
      by blast
    thus "n \<le> \<parallel> \<Gamma> \<parallel>\<^sub>\<phi>"
      by (simp add: complement_core_size_intro)
  qed
  ultimately show ?thesis by metis
qed

lemma (in Logical_Probability) list_probability_upper_bound:
  "(\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>) \<le> real (length \<Gamma>)"
proof (induct \<Gamma>)
  case Nil
  then show ?case by simp
next
  case (Cons \<gamma> \<Gamma>)
  moreover have "Pr \<gamma> \<le> 1" using unity_upper_bound by blast
  ultimately have "Pr \<gamma> + (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>) \<le> 1 + real (length \<Gamma>)" by linarith
  then show ?case by simp
qed

theorem (in Classical_Propositional_Logic) binary_limited_stratified_deduction_completeness:
  "(\<forall> Pr \<in> Binary_Probabilities. real n * Pr \<phi> \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)) = \<^bold>\<sim> \<Gamma> #\<turnstile> n (\<sim> \<phi>)"
proof -
  {
    fix Pr :: "'a \<Rightarrow> real"
    assume "Pr \<in> Binary_Probabilities"
    from this interpret Logical_Probability "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(\<rightarrow>)" "\<bottom>" "Pr"
      unfolding Binary_Probabilities_def
      by auto
    assume "\<^bold>\<sim> \<Gamma> #\<turnstile> n (\<sim> \<phi>)"
    moreover have "replicate n (\<sim> \<phi>) = \<^bold>\<sim> (replicate n \<phi>)"
      by (induct n, auto)
    ultimately have "\<^bold>\<sim> \<Gamma> $\<turnstile> \<^bold>\<sim> (replicate n \<phi>)"
      using stratified_segmented_deduction_replicate by metis
    hence "(\<Sum>\<phi>\<leftarrow>(replicate n \<phi>). Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
      using segmented_deduction_summation_introduction
      by blast
    moreover have "(\<Sum>\<phi>\<leftarrow>(replicate n \<phi>). Pr \<phi>) = real n * Pr \<phi>"
      by (induct n, simp, simp add: semiring_normalization_rules(3))
    ultimately have "real n * Pr \<phi> \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
      by simp
  }
  moreover
  {
    assume "\<not> \<^bold>\<sim> \<Gamma> #\<turnstile> n (\<sim> \<phi>)"
    have "\<exists> Pr \<in> Binary_Probabilities. real n * Pr \<phi> > (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
    proof -
      have "\<exists>\<Phi>. \<Phi> \<in> \<C> (\<^bold>\<sim> \<Gamma>) (\<sim> \<phi>)"
        using \<open>\<not> \<^bold>\<sim> \<Gamma> #\<turnstile> n (\<sim> \<phi>)\<close>
              unproving_core_existence
              stratified_deduction_tautology_weaken
        by blast
      from this obtain \<Phi> where \<Phi>: "(\<^bold>\<sim> \<Phi>) \<in> \<C> (\<^bold>\<sim> \<Gamma>) (\<sim> \<phi>)" "mset \<Phi> \<subseteq># mset \<Gamma>"
        by (metis (mono_tags, lifting)
                  unproving_core_def
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
        using MCS_Binary_Logical_Probability by blast
      moreover
      from this interpret Logical_Probability "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(\<rightarrow>)" "\<bottom>" "?Pr"
        unfolding Binary_Probabilities_def
        by auto
      have "\<forall> \<phi> \<in> set \<Phi>. ?Pr \<phi> = 0"
        using \<Phi>(1) \<Omega>(1) \<Omega>(3) arbitrary_disjunction_exclusion_MCS by auto
      with \<Phi>(2) have "(\<Sum>\<gamma>\<leftarrow>\<Gamma>. ?Pr \<gamma>) = (\<Sum>\<gamma>\<leftarrow>(\<Gamma> \<ominus> \<Phi>). ?Pr \<gamma>)"
      proof (induct \<Phi>)
        case Nil
        then show ?case by simp
      next
        case (Cons \<phi> \<Phi>)
        then show ?case
        proof -
          obtain \<omega> :: 'a where
            \<omega>: "\<not> mset \<Phi> \<subseteq># mset \<Gamma>
                \<or> \<omega> \<in> set \<Phi> \<and> \<omega> \<in> \<Omega>
                \<or> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. ?Pr \<gamma>) = (\<Sum>\<gamma>\<leftarrow>\<Gamma> \<ominus> \<Phi>. ?Pr \<gamma>)"
            using Cons.hyps by fastforce
          have A:
            "\<forall>(f :: 'a \<Rightarrow> real) (\<Gamma> ::'a list) \<Phi>.
                \<not> mset \<Phi> \<subseteq># mset \<Gamma>
              \<or> sum_list ((\<Sum>\<phi>\<leftarrow>\<Phi>. f \<phi>) # map f (\<Gamma> \<ominus> \<Phi>)) = (\<Sum>\<gamma>\<leftarrow>\<Gamma>. f \<gamma>)"
            using listSubstract_multisubset_list_summation by auto
          have B: "\<forall>rs. sum_list ((0::real) # rs) = sum_list rs"
            by auto
          have C: "\<forall>r rs. (0::real) = r \<or> sum_list (r # rs) \<noteq> sum_list rs"
            by simp
          have D: "\<forall>f. sum_list (sum_list (map f (\<phi> # \<Phi>)) # map f (\<Gamma> \<ominus> (\<phi> # \<Phi>)))
                     = (sum_list (map f \<Gamma>)::real)"
            using A Cons.prems(1) by blast
          have E: "mset \<Phi> \<subseteq># mset \<Gamma>"
            using Cons.prems(1) subset_mset.dual_order.trans by force
          then have F: "\<forall>f. (0::real) = sum_list (map f \<Phi>)
                           \<or> sum_list (map f \<Gamma>) \<noteq> sum_list (map f (\<Gamma> \<ominus> \<Phi>))"
            using C A by (metis (no_types))
          then have G: "(\<Sum>\<phi>'\<leftarrow>(\<phi> # \<Phi>). ?Pr \<phi>') = 0 \<or> \<omega> \<in> \<Omega>"
            using E \<omega> Cons.prems(2) by auto
          have H: "\<forall>\<Gamma> r::real. r = (\<Sum>\<gamma>\<leftarrow>\<Gamma>. ?Pr \<gamma>)
                             \<or> \<omega> \<in> set \<Phi>
                             \<or> r \<noteq> (\<Sum>\<gamma>\<leftarrow>(\<phi> # \<Gamma>). ?Pr \<gamma>)"
            using Cons.prems(2) by auto
          have "(1::real) \<noteq> 0" by linarith
          moreover
          { assume "\<omega> \<notin> set \<Phi>"
            then have "\<omega> \<notin> \<Omega> \<or> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. ?Pr \<gamma>) = (\<Sum>\<gamma>\<leftarrow>\<Gamma> \<ominus> (\<phi> # \<Phi>). ?Pr \<gamma>)"
              using H F E D B \<omega> by (metis (no_types) sum_list.Cons) }
          ultimately have ?thesis
            using G D B by (metis Cons.prems(2) list.set_intros(2))
          then show ?thesis
            by linarith
        qed
      qed
      hence "(\<Sum>\<gamma>\<leftarrow>\<Gamma>. ?Pr \<gamma>) \<le> real (length (\<Gamma> \<ominus> \<Phi>))"
        using list_probability_upper_bound
        by auto
            moreover
      have "length (\<^bold>\<sim> \<Gamma> \<ominus> \<^bold>\<sim> \<Phi>) < n"
        by (metis not_le \<Phi>(1) \<open>\<not> (\<^bold>\<sim> \<Gamma>) #\<turnstile> n (\<sim> \<phi>)\<close>
                  unproving_core_max_stratified_deduction
                  unproving_listSubtract_length_equiv)
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
  ultimately show ?thesis by fastforce
qed

lemma (in Classical_Propositional_Logic) binary_segmented_deduction_completeness:
  "(\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)) = \<^bold>\<sim> \<Gamma> $\<turnstile> \<^bold>\<sim> \<Phi>"
proof -
  {
    fix Pr :: "'a \<Rightarrow> real"
    assume "Pr \<in> Binary_Probabilities"
    from this interpret Logical_Probability "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(\<rightarrow>)" "\<bottom>" "Pr"
      unfolding Binary_Probabilities_def
      by auto
    assume "\<^bold>\<sim> \<Gamma> $\<turnstile> \<^bold>\<sim> \<Phi>"
    hence "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
      using segmented_deduction_summation_introduction
      by blast
  }
  moreover
  {
    assume "\<not> \<^bold>\<sim> \<Gamma> $\<turnstile> \<^bold>\<sim> \<Phi>"
    have "\<exists> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) > (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
    proof -
      from \<open>\<not> \<^bold>\<sim> \<Gamma> $\<turnstile> \<^bold>\<sim> \<Phi>\<close> have "\<not> \<^bold>\<sim> (\<^bold>\<sim> \<Phi>) @ \<^bold>\<sim> \<Gamma> #\<turnstile> (length (\<^bold>\<sim> \<Phi>)) \<bottom>"
        using segmented_stratified_falsum_equiv by blast
      moreover
      have "\<^bold>\<sim> (\<^bold>\<sim> \<Phi>) @ \<^bold>\<sim> \<Gamma> #\<turnstile> (length (\<^bold>\<sim> \<Phi>)) \<bottom> = \<^bold>\<sim> (\<^bold>\<sim> \<Phi>) @ \<^bold>\<sim> \<Gamma> #\<turnstile> (length \<Phi>) \<bottom>"
        by (induct \<Phi>, auto)
      moreover have "\<turnstile> \<sim> \<top> \<rightarrow> \<bottom>"
        by (simp add: negation_def)
      ultimately have "\<not> \<^bold>\<sim> (\<^bold>\<sim> \<Phi> @ \<Gamma>) #\<turnstile> (length \<Phi>) (\<sim> \<top>)"
        using stratified_deduction_implication by fastforce
      from this obtain Pr where Pr:
        "Pr \<in> Binary_Probabilities"
        "real (length \<Phi>) * Pr \<top> > (\<Sum>\<gamma>\<leftarrow> (\<^bold>\<sim> \<Phi> @ \<Gamma>). Pr \<gamma>)"
        using binary_limited_stratified_deduction_completeness
        by fastforce
      from this interpret Logical_Probability "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(\<rightarrow>)" "\<bottom>" "Pr"
        unfolding Binary_Probabilities_def
        by auto
      from Pr(2) have "real (length \<Phi>) > (\<Sum>\<gamma>\<leftarrow> \<^bold>\<sim> \<Phi>. Pr \<gamma>) + (\<Sum>\<gamma>\<leftarrow> \<Gamma>. Pr \<gamma>)"
        by (simp add: Unity)
      moreover have "(\<Sum>\<gamma>\<leftarrow> \<^bold>\<sim> \<Phi>. Pr \<gamma>) = real (length \<Phi>) - (\<Sum>\<gamma>\<leftarrow> \<Phi>. Pr \<gamma>)"
        using complementation
        by (induct \<Phi>, auto)
      ultimately show ?thesis
        using Pr(1) by auto
    qed
  }
  ultimately show ?thesis by fastforce
qed

theorem (in Classical_Propositional_Logic) segmented_deduction_completeness:
  "(\<forall> Pr \<in> Logical_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)) = \<^bold>\<sim> \<Gamma> $\<turnstile> \<^bold>\<sim> \<Phi>"
proof -
  {
    fix Pr :: "'a \<Rightarrow> real"
    assume "Pr \<in> Logical_Probabilities"
    from this interpret Logical_Probability "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(\<rightarrow>)" "\<bottom>" "Pr"
      unfolding Logical_Probabilities_def
      by auto
    assume "\<^bold>\<sim> \<Gamma> $\<turnstile> \<^bold>\<sim> \<Phi>"
    hence "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
      using segmented_deduction_summation_introduction
      by blast
  }
  thus ?thesis
    using Binary_Probabilities_subset binary_segmented_deduction_completeness
    by fastforce
qed

theorem (in Classical_Propositional_Logic) weakly_additive_completeness_collapse:
  "  (\<forall> Pr \<in> Logical_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>))
   = (\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>))"
  by (simp add: binary_segmented_deduction_completeness
                segmented_deduction_completeness)

lemma (in Classical_Propositional_Logic) stronger_theory_double_negation_right:
  "\<Phi> \<preceq> \<^bold>\<sim> (\<^bold>\<sim> \<Phi>)"
  by (induct \<Phi>, simp, simp add: Double_Negation negation_def stronger_theory_left_right_cons)

lemma (in Classical_Propositional_Logic) stronger_theory_double_negation_left:
  "\<^bold>\<sim> (\<^bold>\<sim> \<Phi>) \<preceq> \<Phi>"
  by (induct \<Phi>,
      simp,
      simp add: Double_Negation_converse negation_def stronger_theory_left_right_cons)

lemma (in Classical_Propositional_Logic) segmented_left_commute:
  "(\<Phi> @ \<Psi>) $\<turnstile> \<Xi> = (\<Psi> @ \<Phi>) $\<turnstile> \<Xi>"
proof -
  have "(\<Phi> @ \<Psi>) \<preceq> (\<Psi> @ \<Phi>)" "(\<Psi> @ \<Phi>) \<preceq> (\<Phi> @ \<Psi>)"
    using stronger_theory_reflexive stronger_theory_right_permutation perm_append_swap by blast+
  thus ?thesis
    using segmented_stronger_theory_left_monotonic
    by blast
qed

lemma (in Classical_Propositional_Logic) stratified_deduction_completeness:
  "(\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)) = (\<^bold>\<sim> \<Gamma> @ \<Phi>) #\<turnstile> (length \<Phi>) \<bottom>"
proof -
  have "(\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>))
            = \<^bold>\<sim> (\<^bold>\<sim> \<Phi>) @ \<^bold>\<sim> \<Gamma> #\<turnstile> (length (\<^bold>\<sim> \<Phi>)) \<bottom>"
    using binary_segmented_deduction_completeness segmented_stratified_falsum_equiv by blast
  also have "... = \<^bold>\<sim> (\<^bold>\<sim> \<Phi>) @ \<^bold>\<sim> \<Gamma> #\<turnstile> (length \<Phi>) \<bottom>" by (induct \<Phi>, auto)
  also have "... = \<^bold>\<sim> \<Gamma> @ \<^bold>\<sim> (\<^bold>\<sim> \<Phi>) #\<turnstile> (length \<Phi>) \<bottom>"
    by (simp add: segmented_left_commute stratified_segmented_deduction_replicate)
  also have "... = \<^bold>\<sim> \<Gamma> @ \<Phi> #\<turnstile> (length \<Phi>) \<bottom>"
    by (meson segmented_cancel
              segmented_stronger_theory_intro
              segmented_transitive
              stratified_segmented_deduction_replicate
              stronger_theory_double_negation_left
              stronger_theory_double_negation_right)
  finally show ?thesis by blast
qed

lemma (in Classical_Propositional_Logic) complement_core_completeness:
  "(\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)) = (length \<Phi> \<le> \<parallel> \<^bold>\<sim> \<Gamma> @ \<Phi> \<parallel>\<^sub>\<bottom>)"
proof (cases "\<turnstile> \<bottom>")
  case True
  hence "\<C> (\<^bold>\<sim> \<Gamma> @ \<Phi>) \<bottom> = {}"
    using unproving_core_existence by auto
  hence "length (\<^bold>\<sim> \<Gamma> @ \<Phi>) = \<parallel> \<^bold>\<sim> \<Gamma> @ \<Phi> \<parallel>\<^sub>\<bottom>"
    unfolding complement_core_size_def core_size_def by presburger
  then show ?thesis
    using True stratified_deduction_completeness stratified_deduction_tautology_weaken
    by auto
next
  case False
  then show ?thesis
    using stratified_deduction_completeness unproving_core_stratified_deduction_lower_bound
    by blast
qed

lemma (in Classical_Propositional_Logic) binary_core_partial_completeness:
  "(\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)) = ((\<bar> \<^bold>\<sim> \<Gamma> @ \<Phi> \<bar>\<^sub>\<bottom>) \<le> length \<Gamma>)"
proof -
  {
    fix Pr :: "'a \<Rightarrow> real"
    obtain \<rho> :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> real" where
        " (\<forall>\<Phi> \<Gamma>. \<rho> \<Phi> \<Gamma> \<in> Binary_Probabilities \<and> \<not> (\<Sum>\<phi>\<leftarrow>\<Phi>. (\<rho> \<Phi> \<Gamma>) \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. (\<rho> \<Phi> \<Gamma>) \<gamma>)
                 \<or> length \<Phi> \<le> \<parallel> \<^bold>\<sim> \<Gamma> @ \<Phi> \<parallel>\<^sub>\<bottom>)
        \<and> (\<forall>\<Phi> \<Gamma>. length \<Phi> \<le> (\<parallel> \<^bold>\<sim> \<Gamma> @ \<Phi> \<parallel>\<^sub>\<bottom>)
                   \<longrightarrow> (\<forall>Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)))"
    using complement_core_completeness by moura
  moreover have "\<forall>\<Gamma> \<phi> n. length \<Gamma> - n \<le> (\<parallel> \<Gamma> \<parallel>\<^sub>\<phi>) \<or> (\<bar> \<Gamma> \<bar>\<^sub>\<phi>) - n \<noteq> 0"
    by (metis add_diff_cancel_right'
              cancel_ab_semigroup_add_class.diff_right_commute
              diff_is_0_eq length_core_decomposition)
  moreover have "\<forall> \<Gamma> \<Phi> n. length (\<Gamma> @ \<Phi>) - n \<le> length \<Gamma> \<or> length \<Phi> - n \<noteq> 0"
    by force
  ultimately have
    "      (Pr \<in> Binary_Probabilities \<longrightarrow> (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>))
         \<and> (\<bar> \<^bold>\<sim> \<Gamma> @ \<Phi> \<bar>\<^sub>\<bottom>) \<le> length (\<^bold>\<sim> \<Gamma>)
    \<or>      \<not> (\<bar> \<^bold>\<sim> \<Gamma> @ \<Phi> \<bar>\<^sub>\<bottom>) \<le> length (\<^bold>\<sim> \<Gamma>)
         \<and> (\<exists>Pr. Pr \<in> Binary_Probabilities \<and> \<not> (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>))"
    by (metis (no_types) add_diff_cancel_left'
                         add_diff_cancel_right'
                         diff_is_0_eq length_append
                         length_core_decomposition)
  }
  then show ?thesis by auto
qed

lemma (in Classical_Propositional_Logic) nat_binary_probability:
  "\<forall> Pr \<in> Binary_Probabilities. \<exists>n :: nat. real n = (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>)"
proof (induct \<Phi>)
  case Nil
  then show ?case by simp
next
  case (Cons \<phi> \<Phi>)
  {
    fix Pr :: "'a \<Rightarrow> real"
    assume "Pr \<in> Binary_Probabilities"
    from Cons this obtain n where "real n = (\<Sum>\<phi>'\<leftarrow>\<Phi>. Pr \<phi>')" by fastforce
    hence \<star>: "(\<Sum>\<phi>'\<leftarrow>\<Phi>. Pr \<phi>') = real n" by simp
    have "\<exists> n. real n = (\<Sum>\<phi>'\<leftarrow>(\<phi> # \<Phi>). Pr \<phi>')"
    proof (cases "Pr \<phi> = 1")
      case True
      then show ?thesis
        by (simp add: \<star>, metis of_nat_Suc)
    next
      case False
      hence "Pr \<phi> = 0" using \<open>Pr \<in> Binary_Probabilities\<close> Binary_Probabilities_def by auto
      then show ?thesis using \<star>
        by simp
    qed
  }
  thus ?case by blast
qed

lemma (in Classical_Propositional_Logic) binary_ceiling_inequality:
  "\<forall> Pr \<in> Binary_Probabilities.
      ((\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + c \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)) = ((\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + \<lceil>c\<rceil> \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>))"
proof -
  {
    fix Pr
    assume "Pr \<in> Binary_Probabilities"
    have "((\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + c \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)) = ((\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + \<lceil>c\<rceil> \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>))"
    proof (rule iffI)
      assume assm: "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + c \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
      show "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + \<lceil>c\<rceil> \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
      proof (rule ccontr)
        assume "\<not> (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + \<lceil>c\<rceil> \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
        moreover
        obtain x :: int
          and  y :: int
          and  z :: int
          where xyz: "x = (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>)"
                     "y = \<lceil>c\<rceil>"
                     "z = (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
          using nat_binary_probability
          by (metis \<open>Pr \<in> Binary_Probabilities\<close> of_int_of_nat_eq)
        ultimately have "x + y - 1 \<ge> z" by linarith
        hence "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + c > (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)" using xyz by linarith
        thus "False" using assm by simp
      qed
    next
      assume "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + \<lceil>c\<rceil> \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
      thus "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + c \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
        by linarith
    qed
  }
  thus ?thesis by blast
qed

lemma (in Logical_Probability) probability_replicate_verum:
  fixes n :: nat
  shows "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + n = (\<Sum>\<phi>\<leftarrow>(replicate n \<top>) @ \<Phi>. Pr \<phi>)"
  using Unity
  by (induct n, auto)

lemma (in Classical_Propositional_Logic) weakly_additive_collapse:
  "  (\<forall> Pr \<in> Logical_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + c \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>))
   = (\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + \<lceil>c\<rceil> \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>))"
proof (rule iffI)
  assume "\<forall> Pr \<in> Logical_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + c \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
  hence "\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + c \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
    using Binary_Probabilities_subset by fastforce
  thus "\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + \<lceil>c\<rceil> \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
    using binary_ceiling_inequality by blast
next
  assume assm: "\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + \<lceil>c\<rceil> \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
  show "\<forall> Pr \<in> Logical_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + c \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
  proof (cases "c \<ge> 0")
    case True
    from this obtain n :: nat where "real n = \<lceil>c\<rceil>"
      by (metis (full_types)
                antisym_conv
                ceiling_le_zero
                ceiling_zero
                nat_0_iff
                nat_eq_iff2
                of_nat_nat)
    {
      fix Pr
      assume "Pr \<in> Binary_Probabilities"
      from this interpret Logical_Probability "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(\<rightarrow>)" "\<bottom>" "Pr"
        unfolding Binary_Probabilities_def
        by auto
      have "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + \<lceil>c\<rceil> \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
        using assm \<open>Pr \<in> Binary_Probabilities\<close> by blast
      hence "(\<Sum>\<phi>\<leftarrow>(replicate n \<top>) @ \<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
        using \<open>real n = \<lceil>c\<rceil>\<close>
              probability_replicate_verum [where \<Phi>=\<Phi> and n=n]
        by metis
    }
    hence "\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>(replicate n \<top>) @ \<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
      by blast
    hence \<dagger>: "\<forall> Pr \<in> Logical_Probabilities.
              (\<Sum>\<phi>\<leftarrow>(replicate n \<top>) @ \<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
      using weakly_additive_completeness_collapse by blast
    {
      fix Pr
      assume "Pr \<in> Logical_Probabilities"
      from this interpret Logical_Probability "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(\<rightarrow>)" "\<bottom>" "Pr"
        unfolding Logical_Probabilities_def
        by auto
      have "(\<Sum>\<phi>\<leftarrow>(replicate n \<top>) @ \<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
        using \<dagger> \<open>Pr \<in> Logical_Probabilities\<close> by blast
      hence "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + c \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
        using \<open>real n = \<lceil>c\<rceil>\<close>
              probability_replicate_verum [where \<Phi>=\<Phi> and n=n]
        by linarith
    }
    then show ?thesis by blast
  next
    case False
    hence "\<lceil>c\<rceil> \<le> 0" by auto
    from this obtain n :: nat where "real n = - \<lceil>c\<rceil>" by (metis neg_0_le_iff_le of_nat_nat)
    {
      fix Pr
      assume "Pr \<in> Binary_Probabilities"
      from this interpret Logical_Probability "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(\<rightarrow>)" "\<bottom>" "Pr"
        unfolding Binary_Probabilities_def
        by auto
      have "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + \<lceil>c\<rceil> \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
        using assm \<open>Pr \<in> Binary_Probabilities\<close> by blast
      hence "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>(replicate n \<top>) @ \<Gamma>. Pr \<gamma>)"
        using \<open>real n = - \<lceil>c\<rceil>\<close>
              probability_replicate_verum [where \<Phi>=\<Gamma> and n=n]
        by linarith
    }
    hence "\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>(replicate n \<top>) @ \<Gamma>. Pr \<gamma>)"
      by blast
    hence \<ddagger>: "\<forall> Pr \<in> Logical_Probabilities.
              (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>(replicate n \<top>) @ \<Gamma>. Pr \<gamma>)"
      using weakly_additive_completeness_collapse by blast
    {
      fix Pr
      assume "Pr \<in> Logical_Probabilities"
      from this interpret Logical_Probability "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(\<rightarrow>)" "\<bottom>" "Pr"
        unfolding Logical_Probabilities_def
        by auto
      have "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>(replicate n \<top>) @ \<Gamma>. Pr \<gamma>)"
        using \<ddagger> \<open>Pr \<in> Logical_Probabilities\<close> by blast
      hence "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + c \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
        using \<open>real n = - \<lceil>c\<rceil>\<close>
              probability_replicate_verum [where \<Phi>=\<Gamma> and n=n]
        by linarith
    }
    then show ?thesis by blast
  qed
qed

lemma (in Classical_Propositional_Logic) unproving_core_verum_extract:
  assumes "\<not> \<turnstile> \<phi>"
  shows "(\<bar> replicate n \<top> @ \<Phi> \<bar>\<^sub>\<phi>) = n + (\<bar> \<Phi> \<bar>\<^sub>\<phi>)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  {
    fix \<Phi>
    obtain \<Sigma> where "\<Sigma> \<in> \<C> (\<top> # \<Phi>) \<phi>"
      using assms unproving_core_existence by fastforce
    hence "\<top> \<in> set \<Sigma>"
      by (metis (no_types, lifting)
                list.set_intros(1)
                list_deduction_modus_ponens
                list_deduction_weaken
                unproving_core_complement_equiv
                unproving_core_def
                verum_tautology
                mem_Collect_eq)
    hence "\<not> (remove1 \<top> \<Sigma> :\<turnstile> \<phi>)"
      by (meson \<open>\<Sigma> \<in> \<C> (\<top> # \<Phi>) \<phi>\<close>
                list.set_intros(1)
                Axiom_1
                list_deduction_modus_ponens
                list_deduction_monotonic
                list_deduction_weaken
                unproving_core_complement_equiv
                set_remove1_subset)
    moreover
    have "mset \<Sigma> \<subseteq># mset (\<top> # \<Phi>)"
      using \<open>\<Sigma> \<in> \<C> (\<top> # \<Phi>) \<phi>\<close> unproving_core_def by blast
    hence "mset (remove1 \<top> \<Sigma>) \<subseteq># mset \<Phi>"
      using subset_eq_diff_conv by fastforce
    ultimately have "(\<bar> \<Phi> \<bar>\<^sub>\<phi>) \<ge> length (remove1 \<top> \<Sigma>)"
      by (metis (no_types, lifting)
                core_size_intro
                list_deduction_weaken
                unproving_core_def
                unproving_core_existence
                mem_Collect_eq)
    hence "(\<bar> \<Phi> \<bar>\<^sub>\<phi>) + 1 \<ge> length \<Sigma>"
      by (simp add: \<open>\<top> \<in> set \<Sigma>\<close> length_remove1)
    moreover have "(\<bar> \<Phi> \<bar>\<^sub>\<phi>) < length \<Sigma>"
    proof (rule ccontr)
      assume "\<not> (\<bar> \<Phi> \<bar>\<^sub>\<phi>) < length \<Sigma>"
      hence "(\<bar> \<Phi> \<bar>\<^sub>\<phi>) \<ge> length \<Sigma>" by linarith
      from this obtain \<Delta> where "\<Delta> \<in> \<C> \<Phi> \<phi>" "length \<Delta> \<ge> length \<Sigma>"
        using assms core_size_intro unproving_core_existence by fastforce
      hence "\<not> (\<top> # \<Delta>) :\<turnstile> \<phi>"
        using list_deduction_modus_ponens
              list_deduction_theorem
              list_deduction_weaken
              unproving_core_def
              verum_tautology
        by blast
      moreover have "mset (\<top> # \<Delta>) \<subseteq># mset (\<top> # \<Phi>)"
        using \<open>\<Delta> \<in> \<C> \<Phi> \<phi>\<close> unproving_core_def by auto
      ultimately have "length \<Sigma> \<ge> length (\<top> # \<Delta>)"
        using \<open>\<Sigma> \<in> \<C> (\<top> # \<Phi>) \<phi>\<close> unproving_core_def by blast
      hence "length \<Delta> \<ge> length (\<top> # \<Delta>)"
        using \<open>length \<Sigma> \<le> length \<Delta>\<close> dual_order.trans by blast
      thus "False" by simp
    qed
    ultimately have "(\<bar> \<top> # \<Phi> \<bar>\<^sub>\<phi>) = (1 + \<bar> \<Phi> \<bar>\<^sub>\<phi>)"
      by (metis Suc_eq_plus1 Suc_le_eq \<open>\<Sigma> \<in> \<C> (\<top> # \<Phi>) \<phi>\<close> add.commute le_antisym core_size_intro)
  }
  thus ?case using Suc by simp
qed


lemma (in Classical_Propositional_Logic) unproving_core_neg_verum_elim:
  "(\<bar> replicate n (\<sim> \<top>) @ \<Phi> \<bar>\<^sub>\<phi>) = (\<bar> \<Phi> \<bar>\<^sub>\<phi>)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  {
    fix \<Phi>
    have "(\<bar> (\<sim> \<top>) # \<Phi> \<bar>\<^sub>\<phi>) = (\<bar> \<Phi> \<bar>\<^sub>\<phi>)"
    proof (cases "\<turnstile> \<phi>")
      case True
      then show ?thesis
        unfolding core_size_def unproving_core_def
        by (simp add: list_deduction_weaken)
    next
      case False
      from this obtain \<Sigma> where "\<Sigma> \<in> \<C> ((\<sim> \<top>) # \<Phi>) \<phi>"
        using unproving_core_existence by fastforce
      have "[(\<sim> \<top>)] :\<turnstile> \<phi>"
        by (metis Modus_Ponens
                  Peirces_law
                  The_Principle_of_Pseudo_Scotus
                  list_deduction_theorem
                  list_deduction_weaken
                  negation_def
                  verum_def)
      hence "\<sim> \<top> \<notin> set \<Sigma>"
        by (meson \<open>\<Sigma> \<in> \<C> (\<sim> \<top> # \<Phi>) \<phi>\<close>
                  list.set_intros(1)
                  list_deduction_base_theory
                  list_deduction_theorem
                  list_deduction_weaken
                  unproving_core_complement_equiv)
      hence "remove1 (\<sim> \<top>) \<Sigma> = \<Sigma>"
        by (simp add: remove1_idem)
      moreover have "mset \<Sigma> \<subseteq># mset ((\<sim> \<top>) # \<Phi>)"
        using \<open>\<Sigma> \<in> \<C> (\<sim> \<top> # \<Phi>) \<phi>\<close> unproving_core_def by blast
      ultimately have "mset \<Sigma> \<subseteq># mset \<Phi>"
        by (metis add_mset_add_single mset.simps(2) mset_remove1 subset_eq_diff_conv)
      moreover have "\<not> (\<Sigma> :\<turnstile> \<phi>)"
        using \<open>\<Sigma> \<in> \<C> (\<sim> \<top> # \<Phi>) \<phi>\<close> unproving_core_def by blast
      ultimately have "(\<bar> \<Phi> \<bar>\<^sub>\<phi>) \<ge> length \<Sigma>"
        by (metis (no_types, lifting)
                  core_size_intro
                  list_deduction_weaken
                  unproving_core_def
                  unproving_core_existence
                  mem_Collect_eq)
      hence "(\<bar> \<Phi> \<bar>\<^sub>\<phi>) \<ge> (\<bar> (\<sim> \<top>) # \<Phi> \<bar>\<^sub>\<phi>)"
        using \<open>\<Sigma> \<in> \<C> (\<sim> \<top> # \<Phi>) \<phi>\<close> core_size_intro by auto
      moreover
      have "(\<bar> \<Phi> \<bar>\<^sub>\<phi>) \<le> (\<bar> (\<sim> \<top>) # \<Phi> \<bar>\<^sub>\<phi>)"
      proof -
        obtain \<Delta> where "\<Delta> \<in> \<C> \<Phi> \<phi>"
          using False unproving_core_existence by blast
        hence
          "\<not> \<Delta> :\<turnstile> \<phi>"
          "mset \<Delta> \<subseteq># mset ((\<sim> \<top>) # \<Phi>)"
          unfolding unproving_core_def
          by (simp,
              metis (mono_tags, lifting)
                    Diff_eq_empty_iff_mset
                    listSubtract.simps(2)
                    listSubtract_mset_homomorphism
                    unproving_core_def
                    mem_Collect_eq
                    mset_zero_iff
                    remove1.simps(1))
        hence "length \<Delta> \<le> length \<Sigma>"
          using \<open>\<Sigma> \<in> \<C> (\<sim> \<top> # \<Phi>) \<phi>\<close> unproving_core_def by blast
        thus ?thesis
          using \<open>\<Delta> \<in> \<C> \<Phi> \<phi>\<close> \<open>\<Sigma> \<in> \<C> (\<sim> \<top> # \<Phi>) \<phi>\<close> core_size_intro by auto
      qed
      ultimately show ?thesis
        using le_antisym by blast
    qed
  }
  thus ?case using Suc by simp
qed

lemma (in Classical_Propositional_Logic) binary_inequality_elim:
  assumes "\<not> \<turnstile> \<bottom>"
      and "\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + (c :: real) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
    shows "((\<bar> \<^bold>\<sim> \<Gamma> @ \<Phi> \<bar>\<^sub>\<bottom>) + c \<le> length \<Gamma>)"
proof (cases "c \<ge> 0")
  case True
  from this obtain n :: nat where "real n = \<lceil>c\<rceil>"
    by simp
  {
    fix Pr
    assume "Pr \<in> Binary_Probabilities"
    from this interpret Logical_Probability "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(\<rightarrow>)" "\<bottom>" "Pr"
      unfolding Binary_Probabilities_def
      by auto
    have "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + n \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
      by (metis assms(2) \<open>Pr \<in> Binary_Probabilities\<close> \<open>real n = \<lceil>c\<rceil>\<close> binary_ceiling_inequality)
    hence "(\<Sum>\<phi>\<leftarrow>(replicate n \<top>) @ \<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
      using probability_replicate_verum [where \<Phi>=\<Phi> and n=n]
      by metis
  }
  hence "(\<bar> \<^bold>\<sim> \<Gamma> @ replicate n \<top> @ \<Phi> \<bar>\<^sub>\<bottom>) \<le> length \<Gamma>"
    using binary_core_partial_completeness by blast
  moreover have "mset (\<^bold>\<sim> \<Gamma> @ replicate n \<top> @ \<Phi>) = mset (replicate n \<top> @ \<^bold>\<sim> \<Gamma> @ \<Phi>)"
    by simp
  ultimately have "(\<bar> replicate n \<top> @ \<^bold>\<sim> \<Gamma> @ \<Phi> \<bar>\<^sub>\<bottom>) \<le> length \<Gamma>"
    unfolding core_size_def unproving_core_def
    by metis
  hence "(\<bar> \<^bold>\<sim> \<Gamma> @ \<Phi> \<bar>\<^sub>\<bottom>) + \<lceil>c\<rceil> \<le> length \<Gamma>"
    using \<open>real n = \<lceil>c\<rceil>\<close> assms(1) unproving_core_verum_extract
    by auto
  then show ?thesis by linarith
next
  case False
  hence "\<lceil>c\<rceil> \<le> 0" by auto
  from this obtain n :: nat where "real n = - \<lceil>c\<rceil>" by (metis neg_0_le_iff_le of_nat_nat)
  {
    fix Pr
    assume "Pr \<in> Binary_Probabilities"
    from this interpret Logical_Probability "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(\<rightarrow>)" "\<bottom>" "Pr"
      unfolding Binary_Probabilities_def
      by auto
    have "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + \<lceil>c\<rceil> \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
      using assms(2) \<open>Pr \<in> Binary_Probabilities\<close> binary_ceiling_inequality
      by blast
    hence "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>) + n"
      using \<open>real n = - \<lceil>c\<rceil>\<close> by linarith
    hence "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>(replicate n \<top>) @ \<Gamma>. Pr \<gamma>)"
      using probability_replicate_verum [where \<Phi>=\<Gamma> and n=n]
      by metis
  }
  hence "(\<bar> \<^bold>\<sim> (replicate n \<top> @ \<Gamma>) @ \<Phi> \<bar>\<^sub>\<bottom>) \<le> length (replicate n \<top> @ \<Gamma>)"
    using binary_core_partial_completeness [where \<Phi>=\<Phi> and \<Gamma>="replicate n \<top> @ \<Gamma>"]
    by metis
  hence "(\<bar> \<^bold>\<sim> \<Gamma> @ \<Phi> \<bar>\<^sub>\<bottom>) \<le> n + length \<Gamma>"
    by (simp add: unproving_core_neg_verum_elim)
  then show ?thesis using \<open>real n = - \<lceil>c\<rceil>\<close> by linarith
qed

lemma (in Classical_Propositional_Logic) binary_inequality_intro:
  assumes "(\<bar> \<^bold>\<sim> \<Gamma> @ \<Phi> \<bar>\<^sub>\<bottom>) + (c :: real) \<le> length \<Gamma>"
  shows "\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + c \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
proof (cases "\<turnstile> \<bottom>")
  assume "\<turnstile> \<bottom>"
  {
    fix Pr
    assume "Pr \<in> Binary_Probabilities"
    from this interpret Logical_Probability "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(\<rightarrow>)" "\<bottom>" "Pr"
      unfolding Binary_Probabilities_def
      by auto
    have "False"
      using \<open>\<turnstile> \<bottom>\<close> consistency by blast
  }
  then show ?thesis by blast
next
  assume "\<not> \<turnstile> \<bottom>"
  then show ?thesis
  proof (cases "c \<ge> 0")
    assume "c \<ge> 0"
    from this obtain n :: nat where "real n = \<lceil>c\<rceil>"
      by (metis ceiling_mono ceiling_zero of_nat_nat)
    hence "n + (\<bar> \<^bold>\<sim> \<Gamma> @ \<Phi> \<bar>\<^sub>\<bottom>) \<le> length \<Gamma>"
      using assms by linarith
    hence "(\<bar> replicate n \<top> @ \<^bold>\<sim> \<Gamma> @ \<Phi> \<bar>\<^sub>\<bottom>) \<le> length \<Gamma>"
      by (simp add: \<open>\<not> \<turnstile> \<bottom>\<close> unproving_core_verum_extract)
    moreover have "mset (replicate n \<top> @ \<^bold>\<sim> \<Gamma> @ \<Phi>) = mset (\<^bold>\<sim> \<Gamma> @ replicate n \<top> @ \<Phi>)"
      by simp
    ultimately have "(\<bar> \<^bold>\<sim> \<Gamma> @ replicate n \<top> @ \<Phi> \<bar>\<^sub>\<bottom>) \<le> length \<Gamma>"
      unfolding core_size_def unproving_core_def
      by metis
    hence "\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>(replicate n \<top>) @ \<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
      using binary_core_partial_completeness by blast
    {
      fix Pr
      assume "Pr \<in> Binary_Probabilities"
      from this interpret Logical_Probability "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(\<rightarrow>)" "\<bottom>" "Pr"
        unfolding Binary_Probabilities_def
        by auto
      have "(\<Sum>\<phi>\<leftarrow>(replicate n \<top>) @ \<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
        using \<open>Pr \<in> Binary_Probabilities\<close>
              \<open>\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>(replicate n \<top>) @ \<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)\<close>
        by blast
      hence "(\<Sum>\<phi>\<leftarrow> \<Phi>. Pr \<phi>) + n \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
        by (simp add: probability_replicate_verum)
      hence "(\<Sum>\<phi>\<leftarrow> \<Phi>. Pr \<phi>) + c \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)"
        using \<open>real n = real_of_int \<lceil>c\<rceil>\<close> by linarith
    }
    then show ?thesis by blast
  next
    assume "\<not> (c \<ge> 0)"
    hence "\<lceil>c\<rceil> \<le> 0" by auto
    from this obtain n :: nat where "real n = - \<lceil>c\<rceil>" by (metis neg_0_le_iff_le of_nat_nat)
    hence "(\<bar> \<^bold>\<sim> \<Gamma> @ \<Phi> \<bar>\<^sub>\<bottom>) \<le> n + length \<Gamma>"
      using assms by linarith
    hence "(\<bar> \<^bold>\<sim> (replicate n \<top> @ \<Gamma>) @ \<Phi> \<bar>\<^sub>\<bottom>) \<le> length (replicate n \<top> @ \<Gamma>)"
      by (simp add: unproving_core_neg_verum_elim)
    hence "\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>(replicate n \<top>) @ \<Gamma>. Pr \<gamma>)"
      using binary_core_partial_completeness by blast
    {
      fix Pr
      assume "Pr \<in> Binary_Probabilities"
      from this interpret Logical_Probability "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(\<rightarrow>)" "\<bottom>" "Pr"
        unfolding Binary_Probabilities_def
        by auto
      have "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>(replicate n \<top>) @ \<Gamma>. Pr \<gamma>)"
        using \<open>Pr \<in> Binary_Probabilities\<close>
              \<open>\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) \<le> (\<Sum>\<gamma>\<leftarrow>(replicate n \<top>) @ \<Gamma>. Pr \<gamma>)\<close>
        by blast
      hence "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + \<lceil>c\<rceil> \<le> (\<Sum>\<gamma>\<leftarrow> \<Gamma>. Pr \<gamma>)"
        using \<open>real n = - \<lceil>c\<rceil>\<close> probability_replicate_verum by auto
      hence "(\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + c \<le> (\<Sum>\<gamma>\<leftarrow> \<Gamma>. Pr \<gamma>)"
        by linarith
    }
    then show ?thesis by blast
  qed
qed

lemma (in Classical_Propositional_Logic) binary_inequality_equiv:
  assumes "\<not> \<turnstile> \<bottom>"
  shows "(\<forall> Pr \<in> Binary_Probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>) + (c :: real) \<le> (\<Sum>\<gamma>\<leftarrow>\<Gamma>. Pr \<gamma>)) =
         ((\<bar> \<^bold>\<sim> \<Gamma> @ \<Phi> \<bar>\<^sub>\<bottom>) + c \<le> length \<Gamma>)"
  using assms binary_inequality_elim binary_inequality_intro by auto

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

lemma (in Logical_Probability)
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
                  "\<turnstile> \<sim>((a \<rightarrow> (\<sim> p)) \<sqinter> (b \<rightarrow> (\<sim> p))) \<leftrightarrow>s
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
      by (smurf insert_subset list.simps(15) list_deduction_monotonic set_subset_Cons)
    hence "[?Y, ?Z] :\<turnstile> p = ?\<Gamma> :\<turnstile> p" by simp
    moreover have "?\<Gamma> :\<turnstile> b" "?\<Gamma> :\<turnstile> b \<rightarrow> p"
      by (simp add: list_deduction_reflection)+
    hence "?\<Gamma> :\<turnstile> p" using list_deduction_modus_ponens by blast
    ultimately show "[?Y, ?Z] :\<turnstile> p" by simp
  qed
  moreover have "[?X, ?Y \<setminus> p, ?Z \<setminus> p] :\<turnstile> p"
    *)

end
