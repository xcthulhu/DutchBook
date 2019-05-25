theory Abstract_Finitely_Additive_Probability
  imports "../Logical/Logical_Probability_Completeness"
          Finite_Boolean_Algebra
begin

sledgehammer_params [smt_proofs = false]

no_notation
  verum ("\<top>") and
  falsum ("\<bottom>") and
  disjunction (infixr "\<squnion>" 67) and
  conjunction (infixr "\<sqinter>" 67) and
  Arbitrary_Conjunction ("\<Sqinter>") and
  Arbitrary_Disjunction ("\<Squnion>")

class \<P> = 
  fixes \<P> :: "'a \<Rightarrow> real"

class abstract_finitely_additive_probability = \<P> + boolean_algebra +
  assumes Non_Negative: "\<P> \<phi> \<ge> 0"
  assumes Unity: "\<P> \<top> = 1"
  assumes Finite_Additivity: "\<phi> \<sqinter> \<psi> = \<bottom> \<Longrightarrow> \<P> (\<phi> \<squnion> \<psi>) = \<P> \<phi> + \<P> \<psi>"

context boolean_algebra begin

definition residual (infixr "\<Rightarrow>" 70) where
  "\<phi> \<Rightarrow> \<psi> \<equiv> - \<phi> \<squnion> \<psi>"

lemma residual_galois_connection:
  "A \<sqinter> B \<le> C \<longleftrightarrow> B \<le> A \<Rightarrow> C"
proof
  assume "A \<sqinter> B \<le> C"
  have "B \<squnion> (A \<Rightarrow> C) = A \<Rightarrow> C \<squnion> B \<sqinter> \<top>"
    unfolding residual_def
    using inf_top.right_neutral 
          sup_commute 
    by presburger
  moreover have "\<top> = A \<Rightarrow> C \<squnion> A"
    unfolding residual_def
    using sup_commute sup_compl_top_left2
    by fastforce
  ultimately have "B \<squnion> (A \<Rightarrow> C) = A \<Rightarrow> C \<squnion> B \<sqinter> A"
    unfolding residual_def
    by (simp add: sup_inf_distrib1)
  moreover have "A \<sqinter> B \<squnion> C = C"
    using \<open>A \<sqinter> B \<le> C\<close> sup.absorb_iff2 by blast
  ultimately show "B \<le> A \<Rightarrow> C"
    unfolding residual_def
    by (metis inf_commute
              sup.absorb_iff2
              sup.semigroup_axioms 
              sup_commute 
              semigroup.assoc)
next
  assume "B \<le> A \<Rightarrow> C"
  hence "B \<sqinter> (A \<Rightarrow> C) = B"
    using inf_absorb1
    unfolding residual_def
    by fastforce
  moreover have "A \<Rightarrow> C = C \<squnion> - A"
    unfolding residual_def
    by (simp add: abel_semigroup.commute sup.abel_semigroup_axioms)
  moreover have "A \<sqinter> B \<sqinter> C = A \<sqinter> (B \<sqinter> C)"
      by (simp add: inf.semigroup_axioms semigroup.assoc)
  ultimately show "A \<sqinter> B \<le> C"
    unfolding residual_def
    by (metis (no_types) inf.orderI
                         inf_compl_bot_right
                         inf_sup_distrib1 
                         sup_bot.right_neutral)
qed

interpretation Classical_Propositional_Logic "(=) \<top>" "(\<Rightarrow>)" \<bottom>
proof standard
  fix \<phi> \<psi>
  show "\<top> = \<phi> \<Rightarrow> \<psi> \<Rightarrow> \<phi>"
    unfolding residual_def
    by (simp add: sup.commute)
next
  fix \<phi> \<psi> \<chi>
  show "\<top> = (\<phi> \<Rightarrow> \<psi> \<Rightarrow> \<chi>) \<Rightarrow> (\<phi> \<Rightarrow> \<psi>) \<Rightarrow> \<phi> \<Rightarrow> \<chi>"
  proof -
    have "\<top> = (\<phi> \<Rightarrow> \<chi>) \<Rightarrow> \<phi> \<Rightarrow> \<chi>"
      unfolding residual_def
      by (metis compl_sup_top)
    moreover have "- \<phi> \<Rightarrow> \<phi> \<Rightarrow> \<chi> = - \<phi> \<Rightarrow> (\<phi> \<Rightarrow> \<psi> \<Rightarrow> \<chi>) \<Rightarrow> \<phi> \<Rightarrow> \<chi>"
      unfolding residual_def
      by (metis sup_compl_top_left2 sup_left_commute)
    moreover have "\<psi> \<Rightarrow> (\<phi> \<Rightarrow> \<psi> \<Rightarrow> \<chi>) \<Rightarrow> \<phi> \<Rightarrow> \<chi> = \<chi> \<Rightarrow> \<phi> \<Rightarrow> \<chi>"
      unfolding residual_def
      by (metis compl_sup_top sup_compl_top_left2 sup_left_commute)
    ultimately have "\<top> = (\<phi> \<Rightarrow> \<psi> \<Rightarrow> \<chi>) \<Rightarrow> (\<phi> \<Rightarrow> \<chi>) \<squnion> - (\<phi> \<Rightarrow> \<psi>)"
      unfolding residual_def
      using abel_semigroup.commute 
            sup.abel_semigroup_axioms 
            sup_inf_distrib1
      by fastforce
    hence "\<top> = (\<phi> \<Rightarrow> \<psi>) \<Rightarrow> (\<phi> \<Rightarrow> \<psi> \<Rightarrow> \<chi>) \<Rightarrow> \<phi> \<Rightarrow> \<chi>"
      unfolding residual_def
      by (simp add: abel_semigroup.commute sup.abel_semigroup_axioms)
    thus ?thesis
      unfolding residual_def
      by (simp add: sup_left_commute)
  qed
next
  fix \<phi> \<psi>
  show "\<top> = \<phi> \<Rightarrow> \<psi> \<Longrightarrow> \<top> = \<phi> \<Longrightarrow> \<top> = \<psi>"
    unfolding residual_def
    using compl_top_eq
    by auto
next
  fix \<phi>
  show "\<top> = ((\<phi> \<Rightarrow> \<bottom>) \<Rightarrow> \<bottom>) \<Rightarrow> \<phi>"
    unfolding residual_def
    by simp
qed

lemmas Axiom_1 = Axiom_1
lemmas Axiom_2 = Axiom_2
lemmas Double_Negation = Double_Negation
lemmas Modus_Ponens = Modus_Ponens

definition probabilities :: "('a \<Rightarrow> real) set"
  where "probabilities = 
         { \<P>. class.abstract_finitely_additive_probability \<P> (-) uminus (\<sqinter>) (\<le>) (<) (\<squnion>) \<bottom> \<top> }"

lemma probabilities_alt_def:
  "probabilities = { \<P>. class.Logical_Probability ((=) \<top>) (\<Rightarrow>) \<bottom> \<P> }"
proof
  show "probabilities \<subseteq> { \<P>. class.Logical_Probability ((=) \<top>) (\<Rightarrow>) \<bottom> \<P> }"
  proof
    fix \<P>
    assume "\<P> \<in> probabilities"
    from this interpret 
      abstract_finitely_additive_probability \<P>
      unfolding probabilities_def
      by auto
    have "class.Logical_Probability ((=) \<top>) (\<Rightarrow>) \<bottom> \<P>"
    proof standard
      fix \<phi>
      show "0 \<le> \<P> \<phi>"
        by (simp add: Non_Negative)
    next
      fix \<phi>
      show "\<top> = \<phi> \<Longrightarrow> \<P> \<phi> = 1"
        using Unity by blast
    next
      fix \<phi> \<psi>
      assume "\<top> = (\<phi> \<Rightarrow> \<psi> \<Rightarrow> \<bottom>)"
      hence "\<phi> \<sqinter> \<psi> = \<bottom>"
        unfolding residual_def
        using compl_top_eq by auto
      thus "\<P> ((\<phi> \<Rightarrow> \<bottom>) \<Rightarrow> \<psi>) = \<P> \<phi> + \<P> \<psi>"
        unfolding residual_def
        by (simp add: Finite_Additivity)
    qed
    thus "\<P> \<in> { \<P>. class.Logical_Probability ((=) \<top>) (\<Rightarrow>) \<bottom> \<P> }" by auto
  qed
next
  show "{ \<P>. class.Logical_Probability ((=) \<top>) (\<Rightarrow>) \<bottom> \<P> } \<subseteq> probabilities"
  proof
    fix \<P>
    assume "\<P> \<in> { \<P>. class.Logical_Probability ((=) \<top>) (\<Rightarrow>) \<bottom> \<P> }"
    from this interpret Logical_Probability "(=) \<top>" "(\<Rightarrow>)" \<bottom> \<P>
      by auto
    have
      "class.abstract_finitely_additive_probability \<P> (-) uminus (\<sqinter>) (\<le>) (<) (\<squnion>) \<bottom> \<top>"
    proof standard
      fix \<phi>
      show "0 \<le> \<P> \<phi>"
        by (simp add: Non_Negative)
    next
      show "\<P> \<top> = 1"
        using Unity by blast
    next
      fix \<phi> \<psi>
      assume "\<phi> \<sqinter> \<psi> = \<bottom>"
      thus "\<P> (\<phi> \<squnion> \<psi>) = \<P> \<phi> + \<P> \<psi>"
        using Implicational_Additivity 
              compl_bot_eq 
              sup_bot.right_neutral 
              residual_def
        by force
    qed
    thus "\<P> \<in> probabilities"
      unfolding probabilities_def
      by auto
  qed
qed

definition dirac_measures where
  "dirac_measures = { \<delta> \<in> probabilities. (\<forall> \<phi>. \<delta> \<phi> = 0 \<or> \<delta> \<phi> = 1) }"

lemma dirac_measures_alt_def:
  "dirac_measures =
     { \<delta>. class.Logical_Probability ((=) \<top>) (\<Rightarrow>) \<bottom> \<delta> \<and> (\<forall>x. \<delta> x = 0 \<or> \<delta> x = 1) }"
  unfolding dirac_measures_def
            probabilities_alt_def
  by auto

lemma join_prime_to_dirac_measure:
  assumes "\<alpha> \<in> \<J>"
  shows "(\<lambda> \<phi>. if \<alpha> \<le> \<phi> then 1 else 0) \<in> dirac_measures"
  (is "?\<delta> \<in> dirac_measures")
proof -
  have "class.Logical_Probability ((=) \<top>) (\<Rightarrow>) \<bottom> ?\<delta>"
  proof standard
    fix \<phi>
    show "0 \<le> ?\<delta> \<phi>"
      by fastforce
  next
    fix \<phi>
    show "\<top> = \<phi> \<Longrightarrow> (if \<alpha> \<le> \<phi> then 1 else 0) = 1"
      using top_greatest by auto
  next
    fix \<phi> \<psi>
    assume "\<top> = \<phi> \<Rightarrow> \<psi> \<Rightarrow> \<bottom>"
    hence "\<phi> \<sqinter> \<psi> = \<bottom>"
      using compl_top_eq residual_def by auto
    hence "\<not> \<alpha> \<le> \<phi> \<or> \<not> \<alpha> \<le> \<psi>"
      using \<open>\<alpha> \<in> \<J>\<close>
      unfolding join_primes_def join_prime_def
      using bot_unique inf.boundedI by blast
    moreover have "\<alpha> \<le> \<phi> \<squnion> \<psi> \<longleftrightarrow> \<alpha> \<le> \<phi> \<or> \<alpha> \<le> \<psi>"
      using \<open>\<alpha> \<in> \<J>\<close>
      unfolding join_primes_def join_prime_def
      using le_supI1 le_supI2 by blast
    ultimately show "?\<delta> ((\<phi> \<Rightarrow> \<bottom>) \<Rightarrow> \<psi>) = ?\<delta> \<phi> + ?\<delta> \<psi>"
      unfolding residual_def
      by auto
  qed
  thus ?thesis
    unfolding dirac_measures_alt_def
    by simp
qed

lemma conditional_probability_measure:
  fixes   \<P> :: "'a \<Rightarrow> real"
  assumes "\<P> \<in> probabilities" and "\<P> \<psi> \<noteq> 0"
  shows   "(\<lambda> \<phi>. \<P> (\<phi> \<sqinter> \<psi>) / \<P> \<psi>) \<in> probabilities"
proof -
  from assms interpret 
    abstract_finitely_additive_probability \<P>
    unfolding probabilities_def
    by auto
  have "\<P> \<psi> > 0"
    using \<open>\<P> \<psi> \<noteq> 0\<close> 
          Non_Negative
          order_class.dual_order.order_iff_strict 
    by blast
  let ?\<P>' = "\<lambda> \<phi>. \<P> (\<phi> \<sqinter> \<psi>) / \<P> \<psi>"
  have "class.abstract_finitely_additive_probability ?\<P>' (-) uminus (\<sqinter>) (\<le>) (<) (\<squnion>) \<bottom> \<top>"
  proof standard
    fix \<phi>
    show "0 \<le> \<P> (\<phi> \<sqinter> \<psi>) / \<P> \<psi>"
      by (simp add: Non_Negative)
  next
    show "\<P> (\<top> \<sqinter> \<psi>) / \<P> \<psi> = 1"
      using \<open>0 < \<P> \<psi>\<close> inf_top_left by auto
  next
    fix \<phi> \<chi>
    assume "\<phi> \<sqinter> \<chi> = \<bottom>"
    hence "\<P> ((\<phi> \<squnion> \<chi>) \<sqinter> \<psi>) = \<P> (\<phi> \<sqinter> \<psi>) + \<P> (\<chi> \<sqinter> \<psi>)"
      by (metis Finite_Additivity 
                inf.assoc 
                inf.commute 
                inf_bot_right 
                inf_sup_distrib2) 
    thus "\<P> ((\<phi> \<squnion> \<chi>) \<sqinter> \<psi>) / \<P> \<psi> = \<P> (\<phi> \<sqinter> \<psi>) / \<P> \<psi> + \<P> (\<chi> \<sqinter> \<psi>) / \<P> \<psi>"
      by (simp add: add_divide_distrib)
  qed
  thus ?thesis
    unfolding probabilities_def
    by blast
qed

lemma probabilities_convex:
  fixes   \<P> \<Q> :: "'a \<Rightarrow> real" and \<alpha> :: real
  assumes "{\<P>,\<Q>} \<subseteq> probabilities" and "0 \<le> \<alpha>" and "\<alpha> \<le> 1"
  shows   "(\<lambda> \<phi>. \<alpha> * \<P> \<phi> + (1 - \<alpha>) * \<Q> \<phi>) \<in> probabilities"
proof -
  let ?\<M> = "\<lambda> \<phi>. \<alpha> * \<P> \<phi> + (1 - \<alpha>) * \<Q> \<phi>"
  from assms interpret abstract_finitely_additive_probability \<P>
    unfolding probabilities_def
    by auto
  note \<P>_Non_Negative      = Non_Negative
  note \<P>_Unity             = Unity
  note \<P>_Finite_Additivity = Finite_Additivity
  from assms interpret abstract_finitely_additive_probability \<Q>
    unfolding probabilities_def
    by auto
  have "class.abstract_finitely_additive_probability ?\<M> (-) uminus (\<sqinter>) (\<le>) (<) (\<squnion>) \<bottom> \<top>"
  proof standard
    fix \<phi>
    show "0 \<le> \<alpha> * \<P> \<phi> + (1 - \<alpha>) * \<Q> \<phi>"
      by (simp add: \<P>_Non_Negative Non_Negative \<open>0 \<le> \<alpha>\<close> \<open>\<alpha> \<le> 1\<close>)
  next
    show "\<alpha> * \<P> \<top> + (1 - \<alpha>) * \<Q> \<top> = 1"
      using \<P>_Unity Unity by auto
  next
    fix \<phi> \<psi>
    assume "\<phi> \<sqinter> \<psi> = \<bottom>"
    thus "  \<alpha> * \<P> (\<phi> \<squnion> \<psi>) + (1 - \<alpha>) * \<Q> (\<phi> \<squnion> \<psi>) 
          = \<alpha> * \<P> \<phi> + (1 - \<alpha>) * \<Q> \<phi> + (\<alpha> * \<P> \<psi> + (1 - \<alpha>) * \<Q> \<psi>)"
      by (simp add: \<P>_Finite_Additivity distrib_left Finite_Additivity)
  qed
  thus ?thesis
    unfolding probabilities_def
    by auto
qed

end

context abstract_finitely_additive_probability begin

interpretation Logical_Probability "(=) \<top>" "(\<Rightarrow>)" \<bottom> \<P>
proof -
  have "class.abstract_finitely_additive_probability \<P> (-) uminus (\<sqinter>) (\<le>) (<) (\<squnion>) \<bottom> \<top>"
    by standard
  hence "\<P> \<in> probabilities"
    unfolding probabilities_def
    by auto
  thus "class.Logical_Probability ((=) \<top>) (\<Rightarrow>) \<bottom> \<P>" 
    unfolding probabilities_alt_def 
    by blast
qed

lemma sum_rule: "\<P> a + \<P> b = \<P> (a \<sqinter> b) + \<P> (a \<squnion> b)"
  by (metis compl_inf 
            conjunction_def 
            disjunction_def 
            double_compl
            residual_def 
            sum_rule
            sup.commute 
            sup_bot.left_neutral)

lemma conditional_probability_join_prime:
  assumes "\<alpha> \<in> \<J>" and "\<P> \<alpha> \<noteq> 0"
  shows   "\<P> (\<phi> \<sqinter> \<alpha>) / \<P> \<alpha> = (if \<alpha> \<le> \<phi> then 1 else 0)"
proof (cases "\<alpha> \<le> \<phi>")
  case True
  hence "\<P> (\<phi> \<sqinter> \<alpha>) = \<P> \<alpha>"
    by (simp add: inf_absorb2)
  hence "\<P> (\<phi> \<sqinter> \<alpha>) / \<P> \<alpha> = 1"
    using \<open>\<P> \<alpha> \<noteq> 0\<close> right_inverse_eq by blast
  then show ?thesis 
    using \<open>\<alpha> \<le> \<phi>\<close> by simp
next
  case False
  hence "\<alpha> \<le> - \<phi>"
    using \<open>\<alpha> \<in> \<J>\<close> top_greatest
    unfolding join_primes_def join_prime_def
    by force
  hence "\<phi> \<sqinter> \<alpha> = \<bottom>"
    by (metis inf_absorb1 inf_compl_bot_right)
  hence "\<P> (\<phi> \<sqinter> \<alpha>) / \<P> \<alpha> = 0"
    using Finite_Additivity inf_bot_right sup_bot.right_neutral by fastforce
  then show ?thesis
    using \<open>\<not> \<alpha> \<le> \<phi>\<close> by auto
qed

lemma join_prime_conditional_probability:
  assumes "\<forall> \<phi>. \<P> (\<phi> \<sqinter> \<alpha>) / \<P> \<alpha> = (if \<alpha> \<le> \<phi> then 1 else 0)"
  shows   "\<alpha> \<in> \<J>"
proof -
  have "\<P> (\<top> \<sqinter> \<alpha>) / \<P> \<alpha> = 1"
    using assms top_greatest by auto
  hence "\<P> \<alpha> > 0"
    using less_eq_real_def Non_Negative by fastforce
  hence "\<alpha> \<noteq> \<bottom>"
    using Antithesis by auto
  moreover
  have \<star>: "\<forall> \<phi>. \<P> (\<phi> \<sqinter> \<alpha>) = (if \<alpha> \<le> \<phi> then \<P> \<alpha> else 0)"
    by (metis \<open>\<P> (\<top> \<sqinter> \<alpha>) / \<P> \<alpha> = 1\<close> 
              \<open>\<forall> \<phi>. \<P> (\<phi> \<sqinter> \<alpha>) / \<P> \<alpha> = (if \<alpha> \<le> \<phi> then 1 else 0)\<close> 
              divide_eq_0_iff
              inf.absorb2 zero_neq_one)
  {
    fix \<phi> \<psi>
    assume "\<alpha> \<le> \<phi> \<squnion> \<psi>"
    have "\<alpha> \<le> \<phi> \<or> \<alpha> \<le> \<psi>"
    proof (rule ccontr)
      assume "\<not> (\<alpha> \<le> \<phi> \<or> \<alpha> \<le> \<psi>)"
      hence "\<P> (\<phi> \<sqinter> \<alpha>) = 0"
            "\<P> (\<psi> \<sqinter> \<alpha>) = 0"
        using \<star> by auto
      hence "0 = \<P> ((\<phi> \<sqinter> \<alpha>) \<sqinter> (\<psi> \<sqinter> \<alpha>)) + \<P> ((\<phi> \<sqinter> \<alpha>) \<squnion> (\<psi> \<sqinter> \<alpha>))"
        using sum_rule by auto
      hence "0 = \<P> (\<phi> \<sqinter> \<psi> \<sqinter> \<alpha>) + \<P> ((\<phi> \<squnion> \<psi>) \<sqinter> \<alpha>)"
        by (simp add: inf.commute inf.left_commute inf_sup_distrib1)
      hence "0 = \<P> (\<phi> \<sqinter> \<psi> \<sqinter> \<alpha>) + \<P> \<alpha>"
        by (simp add: \<open>\<alpha> \<le> \<phi> \<squnion> \<psi>\<close> inf.absorb2)
      hence "0 > \<P> (\<phi> \<sqinter> \<psi> \<sqinter> \<alpha>)"
        using \<open>0 < \<P> \<alpha>\<close> by linarith
      thus False
        using Non_Negative not_le by blast
    qed
  }
  ultimately show ?thesis
    unfolding join_primes_def join_prime_def
    by blast
qed

lemma monotonicity: "a \<le> b \<Longrightarrow> \<P> a \<le> \<P> b"
  by (metis monotonicity 
            residual_def 
            sup.commute 
            sup.left_commute 
            sup_absorb1 
            sup_cancel_left1)

lemmas Antithesis = Antithesis

lemma complementation: "\<P> (- \<phi>) = 1 - \<P> \<phi>"
  by (metis add_diff_cancel_left' 
            Finite_Additivity 
            Unity 
            inf_compl_bot 
            sup_compl_top)

lemma finite_certainty:
  assumes "finite A" and "\<forall> a \<in> A. \<P> a = 1"
  shows   "\<P> (Finite_Set.fold (\<sqinter>) \<top> A) = 1"
  using assms
proof (induct A rule: finite_induct)
  case empty
  show "\<P> (Finite_Set.fold (\<sqinter>) \<top> {}) = 1"
    by (simp add: Unity) 
next
  case (insert a A)
  have \<star>: "\<P> (Finite_Set.fold (\<sqinter>) \<top> (insert a A)) = \<P> (a \<sqinter> Finite_Set.fold (\<sqinter>) \<top> A)"
       (is "\<P> ?A' = \<P> (a \<sqinter> ?A)")
    by (simp add: comp_fun_idem.fold_insert_idem insert.hyps(1) comp_fun_idem_inf) 
  have "\<P> ?A = 1"
    using insert.hyps(3) insert.prems by blast
  moreover have "\<P> a = 1"
    by (simp add: insert.prems)
  moreover
  have "a \<le> a \<squnion> ?A" by simp
  hence "1 \<le> \<P> (a \<squnion> ?A)"
    using monotonicity \<open>\<P> a = 1\<close>
    by fastforce
  hence "\<P> (a \<squnion> ?A) = 1"
    using unity_upper_bound [of "a \<squnion> ?A"]
    by linarith
  ultimately have "\<P> (a \<sqinter> ?A) = 1"
    using sum_rule [where a="a" and b="?A"]
    by linarith
  thus "\<P> ?A' = 1"
    using \<star> by auto
qed

lemma full_finite_additivity:
  assumes "finite A" and "\<forall> a \<in> A. \<forall> a' \<in> A. a \<noteq> a' \<longrightarrow> a \<sqinter> a' = \<bottom>"
  shows   "\<P> (Finite_Set.fold (\<squnion>) \<bottom> A) = (\<Sum> a \<in> A. \<P> a)"
  using assms
proof (induct A rule: finite_induct)
  case empty
  then show ?case
    using Antithesis by fastforce
next
  case (insert a A)
  hence "\<forall>a' \<in> A. a \<sqinter> a' = \<bottom>"
    by auto
  with \<open>finite A\<close> \<open>a \<notin> A\<close> have "a \<sqinter> (Finite_Set.fold (\<squnion>) \<bottom> A) = \<bottom>" (is "a \<sqinter> ?UA = \<bottom>")
  proof (induct A rule: finite_induct)
    case empty
    then show ?case by auto
  next
    case (insert a' A)
    hence "a \<sqinter> (Finite_Set.fold (\<squnion>) \<bottom> A) = \<bottom>" (is "a \<sqinter> ?UA = \<bottom>")
          "a \<sqinter> a' = \<bottom>"
      by auto
    moreover have "Finite_Set.fold (\<squnion>) \<bottom> ({a'} \<union> A) = a' \<squnion> ?UA" (is "?UA' = _")
      by (simp add: comp_fun_idem.fold_insert_idem \<open>finite A\<close> comp_fun_idem_sup)
    hence "a \<sqinter> ?UA' = (a \<sqinter> a') \<squnion> (a \<sqinter> ?UA)"
      using inf_sup_distrib1 by auto
    ultimately show ?case
      by auto 
  qed
  moreover have "Finite_Set.fold (\<squnion>) \<bottom> ({a} \<union> A) = a \<squnion> ?UA"
    by (simp add: comp_fun_idem.fold_insert_idem \<open>finite A\<close> comp_fun_idem_sup)
  moreover have "\<P> ?UA = (\<Sum> a \<in> A. \<P> a)"
    using insert by blast
  ultimately show ?case
    by (simp add: \<open>finite A\<close> \<open>a \<notin> A\<close> Finite_Additivity) 
qed

end

context finite_boolean_algebra begin

lemma join_prime_decomposition:
  fixes   \<P> :: "'a \<Rightarrow> real"
  assumes "\<P> \<in> probabilities"
  shows   "\<P> \<phi> = (\<Sum> \<alpha> \<in> \<J>. \<P> \<alpha> * (if \<alpha> \<le> \<phi> then 1 else 0))"
proof -
  interpret abstract_finitely_additive_probability \<P>
    using \<open>\<P> \<in> probabilities\<close>
    unfolding probabilities_def
    by blast
  have \<star>: "\<phi> = \<Squnion> { \<alpha> \<in> \<J>. \<alpha> \<le> \<phi> }" (is "\<phi> = \<Squnion> ?\<J>\<phi>")
    using join_prime_embedding_def 
          sup_join_prime_embedding_ident 
    by auto
  have "\<forall> \<alpha> \<in> ?\<J>\<phi>. \<forall> \<alpha>' \<in> ?\<J>\<phi>. \<alpha> \<noteq> \<alpha>' \<longrightarrow> \<alpha> \<sqinter> \<alpha>' = \<bottom>"
    unfolding join_primes_def
    by (metis inf.cobounded1 inf.commute join_prime_alt_def mem_Collect_eq)
  hence "\<P> (\<Squnion> ?\<J>\<phi>) = (\<Sum> \<alpha> \<in> ?\<J>\<phi>. \<P> \<alpha>)"
    by (simp add: Sup_def full_finite_additivity)
  with \<star> have \<dagger>: "\<P> \<phi> = (\<Sum> \<alpha> \<in> ?\<J>\<phi>. \<P> \<alpha>)" by auto
  have "finite ?\<J>\<phi>" by auto
  hence "(\<Sum> \<alpha> \<in> ?\<J>\<phi>. \<P> \<alpha>) = (\<Sum> \<alpha> \<in> ?\<J>\<phi>. \<P> \<alpha> * (if \<alpha> \<le> \<phi> then 1 else 0))"
    by (induct ?\<J>\<phi> rule: finite_induct, auto)
  with \<dagger> have "\<P> \<phi> = (\<Sum> \<alpha> \<in> ?\<J>\<phi>. \<P> \<alpha> * (if \<alpha> \<le> \<phi> then 1 else 0))"
    (is "_ = ?\<Sigma>1")
    by presburger
  moreover
  let ?n\<J>\<phi> = "{ \<alpha> \<in> \<J>. \<not> \<alpha> \<le> \<phi> }"
  have "finite ?n\<J>\<phi>" by auto
  hence "0 = (\<Sum> \<alpha> \<in> ?n\<J>\<phi>. \<P> \<alpha> * (if \<alpha> \<le> \<phi> then 1 else 0))"
    (is "_ = ?\<Sigma>2")
    by (induct ?n\<J>\<phi> rule: finite_induct, auto)
  with \<dagger> have \<ddagger>: "\<P> \<phi> = ?\<Sigma>1 + ?\<Sigma>2" by auto
  have "\<forall>\<alpha> \<in> ?\<J>\<phi> \<inter> ?n\<J>\<phi>. \<P> \<alpha> * (if \<alpha> \<le> \<phi> then 1 else 0) = 0" by auto
  with \<ddagger> have "\<P> \<phi> = (\<Sum> \<alpha> \<in> ?\<J>\<phi> \<union> ?n\<J>\<phi>. \<P> \<alpha> * (if \<alpha> \<le> \<phi> then 1 else 0))"
    by (simp add: sum.union_inter_neutral [where A="?\<J>\<phi>" and B="?n\<J>\<phi>"])
  moreover have "\<J> = ?\<J>\<phi> \<union> ?n\<J>\<phi>" by auto
  ultimately show ?thesis
    by auto
qed

lemma dirac_measure_to_join_prime:
  assumes "\<delta> \<in> dirac_measures"
  shows "\<Sqinter> { \<phi> . \<delta> \<phi> = 1 } \<in> \<J>"
  (is "?\<alpha> \<in> \<J>")
proof -
  interpret abstract_finitely_additive_probability \<delta>
    using \<open>\<delta> \<in> dirac_measures\<close>
    unfolding dirac_measures_def probabilities_def
    by blast
  have "\<forall> \<phi> \<in> { \<phi> . \<delta> \<phi> = 1 }. \<delta> \<phi> = 1"
       (is "\<forall> \<phi> \<in> ?A. \<delta> \<phi> = 1")
       by auto
  hence "\<delta> ?\<alpha> = 1"
    using finite_certainty Inf_def finite 
    by presburger
  hence "?\<alpha> \<noteq> \<bottom>"
    using Antithesis
    by auto
  moreover
  {
    fix y z
    assume "?\<alpha> \<le> y \<squnion> z"
    hence "1 \<le> \<delta> (y \<squnion> z)"
      using \<open>\<delta> ?\<alpha> = 1\<close> monotonicity
      by fastforce
    hence "\<delta> (y \<squnion> z) = 1"
      by (metis Unity 
                monotonicity 
                sup.cobounded2 
                sup_top_left 
                order_class.eq_iff)
    moreover have "\<delta> y = 0 \<Longrightarrow> \<delta> z = 0 \<Longrightarrow> \<delta> (y \<squnion> z) = 0"
      by (metis add.right_neutral 
                add_diff_cancel_left' 
                diff_ge_0_iff_ge 
                Non_Negative 
                sum_rule 
                order_class.eq_iff)
    ultimately have "\<delta> y \<noteq> 0 \<or> \<delta> z \<noteq> 0"
      by linarith
    hence "\<delta> y = 1 \<or> \<delta> z = 1"
      using \<open>\<delta> \<in> dirac_measures\<close>
      unfolding dirac_measures_def
      by auto
    hence "y \<in> ?A \<or> z \<in> ?A"
      by auto
    hence "?\<alpha> \<le> y \<or> ?\<alpha> \<le> z"
      using Inf_lower by auto
  }
  ultimately show ?thesis
    unfolding join_primes_def join_prime_def
    by auto
qed

lemma dirac_to_join_prime_ident:
  assumes "\<delta> \<in> dirac_measures"
  shows "(\<lambda> \<phi>. if \<Sqinter> { \<phi> . \<delta> \<phi> = 1 } \<le> \<phi> then 1 else 0) = \<delta>"
proof
  interpret abstract_finitely_additive_probability \<delta>
    using \<open>\<delta> \<in> dirac_measures\<close>
    unfolding dirac_measures_def probabilities_def
    by blast
  fix \<phi>
  show "(if \<Sqinter> { \<phi> . \<delta> \<phi> = 1 } \<le> \<phi> then 1 else 0) = \<delta> \<phi>"
  proof (cases "\<delta> \<phi> = 1")
    case True
    hence "\<Sqinter> { \<phi> . \<delta> \<phi> = 1 } \<le> \<phi>"
      by (fastforce simp add: Inf_lower)
    hence "(if \<Sqinter> { \<phi> . \<delta> \<phi> = 1 } \<le> \<phi> then 1 else 0) = 1"
      by auto
    then show ?thesis
      using \<open>\<delta> \<phi> = 1\<close>
      by simp
  next
    have "join_prime (\<Sqinter> { \<phi> . \<delta> \<phi> = 1 })"
      using \<open>\<delta> \<in> dirac_measures\<close> 
            dirac_measure_to_join_prime
      unfolding join_primes_def
      by blast
    case False
    hence "\<delta> \<phi> = 0"
      using \<open>\<delta> \<in> dirac_measures\<close>
      unfolding dirac_measures_def
      by auto
    hence "\<delta> (- \<phi>) = 1"
      using complementation
      by auto
    hence "\<Sqinter> { \<phi> . \<delta> \<phi> = 1 } \<le> - \<phi>"
      by (fastforce simp add: Inf_lower)
    hence "\<not> (\<Sqinter> { \<phi> . \<delta> \<phi> = 1 } \<le> \<phi>)"
      using \<open>join_prime (\<Sqinter> { \<phi> . \<delta> \<phi> = 1 })\<close>
      unfolding join_prime_def
      by (metis inf.boundedI inf_compl_bot le_bot)
    hence "(if \<Sqinter> { \<phi> . \<delta> \<phi> = 1 } \<le> \<phi> then 1 else 0) = 0"
      by auto
    then show ?thesis
      using \<open>\<delta> \<phi> = 0\<close>
      by auto
  qed
qed

lemma join_prime_to_dirac_ident:
  assumes "\<alpha> \<in> \<J>"
  shows "\<Sqinter>{ \<phi>. (\<lambda> \<phi>. if \<alpha> \<le> \<phi> then 1 else 0) \<phi> = (1 :: real)} = \<alpha>"
  (is "?\<alpha> = \<alpha>")
proof (rule antisym)
  have "\<alpha> \<in> { \<phi>. (\<lambda> \<phi>. if \<alpha> \<le> \<phi> then 1 else 0) \<phi> = 1 }"
    by simp
  thus "?\<alpha> \<le> \<alpha>"
    by (simp add: Inf_lower)
next
  {
    fix \<phi>
    assume "\<phi> \<in> { \<phi>. (\<lambda> \<phi>. if \<alpha> \<le> \<phi> then 1 else 0) \<phi> = (1 :: real) }"
    hence "(if \<alpha> \<le> \<phi> then 1 else 0) = (1 :: real)"
      by fastforce
    hence "\<alpha> \<le> \<phi>"
      by (meson zero_neq_one)
  }
  hence "\<forall> \<phi> \<in> { \<phi>. (\<lambda> \<phi>. if \<alpha> \<le> \<phi> then 1 else 0) \<phi> = (1 :: real) } . \<alpha> \<le> \<phi>"
    by blast
  thus "\<alpha> \<le> ?\<alpha>"
    using Inf_greatest by blast
qed

lemma dirac_join_prime_bij_betw:
  "bij_betw (\<lambda> \<alpha> \<phi>. if \<alpha> \<le> \<phi> then 1 else 0 :: real) \<J> dirac_measures"
  unfolding bij_betw_def
proof
  obtain to_\<delta> where to_\<delta>_def : "to_\<delta> = (\<lambda> \<alpha> \<phi> . if \<alpha> \<le> \<phi> then 1 else 0 :: real)" by auto
  {
    fix \<alpha>1 \<alpha>2
    assume "\<alpha>1 \<in> \<J>"
           "\<alpha>2 \<in> \<J>"
           "to_\<delta> \<alpha>1 = to_\<delta> \<alpha>2"
    moreover from this have 
      " \<Sqinter>{ \<phi>. (\<lambda> \<phi>. if \<alpha>1 \<le> \<phi> then 1 else 0) \<phi> = (1 :: real) }
      = \<Sqinter>{ \<phi>. (\<lambda> \<phi>. if \<alpha>2 \<le> \<phi> then 1 else 0) \<phi> = (1 :: real) }"
      unfolding to_\<delta>_def
      by metis 
    ultimately have "\<alpha>1 = \<alpha>2" 
      using join_prime_to_dirac_ident [of \<alpha>1]
            join_prime_to_dirac_ident [of \<alpha>2]
      by presburger  
  }
  hence "inj_on to_\<delta> \<J>"
    unfolding inj_on_def
    by blast
  thus "inj_on (\<lambda> \<alpha> \<phi>. if \<alpha> \<le> \<phi> then 1 else 0 :: real) \<J>"
    unfolding to_\<delta>_def
    by blast
    
next
  show "(\<lambda>\<alpha> \<phi>. if \<alpha> \<le> \<phi> then 1 else 0) ` \<J> = dirac_measures"
  proof
    {
      fix \<alpha>
      assume "\<alpha> \<in> \<J>"
      hence "(\<lambda>\<phi>. if \<alpha> \<le> \<phi> then 1 else 0) \<in> dirac_measures"
        using join_prime_to_dirac_measure by blast
    }
    thus "(\<lambda>\<alpha> \<phi>. if \<alpha> \<le> \<phi> then 1 else 0) ` \<J> \<subseteq> dirac_measures" by blast
  next
    {
      fix \<delta>
      assume "\<delta> \<in> dirac_measures"
      let ?\<alpha> = "\<Sqinter> { \<phi> . \<delta> \<phi> = 1 }"
      have "?\<alpha> \<in> \<J>"
        using \<open>\<delta> \<in> dirac_measures\<close> dirac_measure_to_join_prime by blast
      moreover have "(\<lambda>\<phi>. if ?\<alpha> \<le> \<phi> then 1 else 0) = \<delta>"
        using \<open>\<delta> \<in> dirac_measures\<close> dirac_to_join_prime_ident by blast
      ultimately have "\<delta> \<in> (\<lambda>\<alpha> \<phi>. if \<alpha> \<le> \<phi> then 1 else 0) ` \<J>"
        using image_iff by fastforce
    }
    thus " dirac_measures \<subseteq> (\<lambda>\<alpha> \<phi>. if \<alpha> \<le> \<phi> then 1 else 0) ` \<J>"
      using subsetI
      by blast
  qed
qed

end