(*:maxLineLen=80:*)

section \<open>Finite Boolean Algebra\<close>

(* TODO: Cite Birkoff and Priestley *)

theory Finite_Boolean_Algebra
  imports 
    "HOL-Library.Finite_Lattice"
    "HOL-Library.Lattice_Syntax"
    "HOL.Transcendental"
begin

sledgehammer_params [smt_proofs = false]

class finite_boolean_algebra = boolean_algebra + finite + Inf + Sup +
  assumes Inf_def: "\<Sqinter>A = Finite_Set.fold (\<sqinter>) \<top> A"
  assumes Sup_def: "\<Squnion>A = Finite_Set.fold (\<squnion>) \<bottom> A"
begin

subclass finite_distrib_lattice_complete
  using 
    Inf_fin.coboundedI
    Sup_fin.coboundedI
    finite_UNIV
    le_bot
    top_unique
    Inf_def
    Sup_def
  by (unfold_locales, blast, fastforce, auto)
end

definition (in bounded_lattice_bot) join_prime :: "'a \<Rightarrow> bool" where
  "join_prime x \<equiv> x \<noteq> \<bottom> \<and> (\<forall> y z . x \<le> y \<squnion> z \<longrightarrow> x \<le> y \<or> x \<le> z)"

lemma (in boolean_algebra) join_prime_alt_def:
  "join_prime x = (x \<noteq> \<bottom> \<and> (\<forall> y. y \<le> x \<longrightarrow> y = \<bottom> \<or> y = x))"
proof
  assume "join_prime x"
  hence "x \<noteq> \<bottom>"
    using join_prime_def by blast
  moreover
  {
    fix y
    assume "y \<le> x" "y \<noteq> x"
    hence "x = x \<squnion> y"
      using sup.orderE by blast
    also have "\<dots> = (x \<squnion> y) \<sqinter> (y \<squnion> -y)"
      by simp
    finally have "x = (x \<sqinter> -y) \<squnion> y"
      by (simp add: sup_inf_distrib2)
    hence "x \<le> -y"
      using \<open>join_prime x\<close> \<open>y \<noteq> x\<close> \<open>y \<le> x\<close> eq_iff
      unfolding join_prime_def
      by force
    hence "y \<le> y \<sqinter> -y"
      by (metis 
            \<open>x = x \<squnion> y\<close>
            inf.orderE
            inf_compl_bot_right
            inf_sup_absorb
            order_refl
            sup.commute)
    hence "y = \<bottom>"
      using sup_absorb2 by fastforce
  }
  ultimately show "x \<noteq> \<bottom> \<and> (\<forall> y. y \<le> x \<longrightarrow> y = \<bottom> \<or> y = x)" by auto
next
  assume atomic: "x \<noteq> \<bottom> \<and> (\<forall> y. y \<le> x \<longrightarrow> y = \<bottom> \<or> y = x)"
  hence "x \<noteq> \<bottom>" by auto
  moreover
  {
    fix y z
    assume "x \<le> y \<squnion> z"
    hence "x = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
      using inf.absorb1 inf_sup_distrib1 by fastforce
    moreover
    have "x \<le> y \<or> (x \<sqinter> y) = \<bottom>"
         "x \<le> z \<or> (x \<sqinter> z) = \<bottom>"
      using atomic inf.cobounded1 inf.cobounded2 by fastforce+
    ultimately have "x \<le> y \<or> x \<le> z"
      using atomic by auto
  }
  ultimately show "join_prime x"
    unfolding join_prime_def
    by auto
qed

lemma (in boolean_algebra) join_prime_disjoint:
  assumes "join_prime \<alpha>"
      and "join_prime \<beta>"
    shows "(\<alpha> = \<beta>) \<longleftrightarrow> (\<alpha> \<sqinter> \<beta> \<noteq> \<bottom>)"
proof
  assume "\<alpha> = \<beta>"
  hence "\<alpha> \<sqinter> \<beta> = \<alpha>"
    by simp
  thus "\<alpha> \<sqinter> \<beta> \<noteq> \<bottom>"
    using \<open>join_prime \<alpha>\<close>
    unfolding join_prime_def
    by auto
next
  assume "\<alpha> \<sqinter> \<beta> \<noteq> \<bottom>"
  show "\<alpha> = \<beta>"
  proof (rule ccontr)
    assume "\<alpha> \<noteq> \<beta>"
    hence "\<not> (\<alpha> \<le> \<beta>)"
      using \<open>join_prime \<alpha>\<close>
            \<open>join_prime \<beta>\<close>
      unfolding join_prime_alt_def
      by blast
    hence "\<alpha> \<le> - \<beta>"
      using assms(1) join_prime_def by force
    hence "\<alpha> \<sqinter> \<beta> = \<bottom>"
      by (metis inf.commute inf.orderE inf_compl_bot_right)
    thus False
      using \<open>\<alpha> \<sqinter> \<beta> \<noteq> \<bottom>\<close>
      by blast
  qed
qed

definition (in bounded_lattice_bot) join_primes ("\<J>") where
  "\<J> \<equiv> {a . join_prime a}"

fun (in order) descending_chain_list :: "'a list \<Rightarrow> bool" where
  "descending_chain_list [] = True"
| "descending_chain_list [x] = True"
| "descending_chain_list (x # x' # xs) 
     = (x < x' \<and> descending_chain_list (x' # xs))"

lemma (in order) descending_chain_list_tail:
  assumes "descending_chain_list (s # S)"
  shows "descending_chain_list S"
  using assms
  by (induct S, auto)

lemma (in order) descending_chain_list_drop_penultimate:
  assumes "descending_chain_list (s # s' # S)"
  shows "descending_chain_list (s # S)"
  using assms
  by (induct S, simp, auto)

lemma (in order) descending_chain_list_less_than_others:
  assumes "descending_chain_list (s # S)"
  shows   "\<forall>s' \<in> set S. s < s'"
  using assms
  by (induct S, auto, simp add: descending_chain_list_drop_penultimate)

lemma (in order) descending_chain_list_distinct:
  assumes "descending_chain_list S"
  shows "distinct S"
  using assms
  by (induct S,
      simp,
      meson 
        descending_chain_list_less_than_others
        descending_chain_list_tail
        distinct.simps(2)
        less_irrefl)

lemma (in finite_boolean_algebra) join_prime_lower_bound_exists:
  assumes "x \<noteq> \<bottom>"
  shows "\<exists> y \<in> \<J>. y \<le> x"
proof (rule ccontr)
  assume "\<not> (\<exists>y \<in> \<J>. y \<le> x)"
  hence fresh: "\<forall> y \<le> x. y \<noteq> \<bottom> \<longrightarrow> (\<exists>z < y. z \<noteq> \<bottom>)"
    unfolding join_primes_def
              join_prime_alt_def
    using dual_order.not_eq_order_implies_strict
    by fastforce
  {
    fix n :: nat
    have "\<exists> S . descending_chain_list S 
                \<and> length S = n 
                \<and> (\<forall>s \<in> set S. s \<noteq> \<bottom> \<and> s \<le> x)"
    proof (induct n)
      case 0
      have "descending_chain_list [] 
            \<and> length [] = 0 
            \<and> (\<forall>s \<in> set []. s \<noteq> \<bottom> \<and> s \<le> x)"
        by auto
      then show ?case by simp
    next
      case (Suc n)
      then show ?case proof (cases "n = 0")
        case True
        hence "descending_chain_list [x] 
               \<and> length [x] = Suc n 
               \<and> (\<forall>s \<in> set [x]. s \<noteq> \<bottom> \<and> s \<le> x)"
          using \<open>x \<noteq> \<bottom>\<close>
          by simp
        then show ?thesis
          by blast
      next
        case False
        from this obtain s S where
          "descending_chain_list (s # S)"
          "length (s # S) = n"
          "\<forall>s \<in> set (s # S). s \<noteq> \<bottom> \<and> s \<le> x"
          using Suc.hyps length_0_conv descending_chain_list.elims(2)
          by metis
        note A = this
        from this obtain s' where
          "s' < s"
          "s' \<noteq> \<bottom>"
          using fresh list.set_intros(1)
          by metis
        note B = this
        let ?S' = "s' # s # S"
        from A and B have
          "descending_chain_list ?S'"
          "length ?S' = Suc n"
          "\<forall>s \<in> set ?S'. s \<noteq> \<bottom> \<and> s \<le> x"
            by auto
        then show ?thesis by blast
      qed
    qed
  }
  from this obtain S :: "'a list" where
    "descending_chain_list S"
    "length S = 1 + (card (UNIV::'a set))"
    by auto
  hence "card (set S) = 1 + (card (UNIV::'a set))"
    using descending_chain_list_distinct
          distinct_card
    by fastforce
  hence "\<not> card (set S) \<le> card (UNIV::'a set)"
    by presburger
  thus "False"
    using card_mono finite_UNIV by blast
qed

definition (in bounded_lattice_bot) 
  join_prime_embedding :: "'a \<Rightarrow> 'a set" ("\<lbrace> _ \<rbrace>" [50]) where
  "\<lbrace> x \<rbrace> \<equiv> {a \<in> \<J>. a \<le> x}"

theorem (in finite_boolean_algebra) sup_join_prime_embedding_ident:
   "\<Squnion> \<lbrace> x \<rbrace> = x"
proof -
  have "\<forall> a \<in> \<lbrace> x \<rbrace>. a \<le> x" unfolding join_prime_embedding_def by auto
  hence "\<Squnion> \<lbrace> x \<rbrace> \<le> x"
    by (simp add: Sup_least)
  moreover
  {
    fix y
    assume "\<Squnion> \<lbrace> x \<rbrace> \<le> y"
    have "x \<le> y"
    proof (rule ccontr)
      assume "\<not> x \<le> y"
      hence "\<bottom> < x \<sqinter> -y"
        by (metis bot_less
                  compl_sup_top
                  inf_top_right
                  le_iff_sup
                  sup.commute
                  sup_bot_right
                  sup_inf_distrib1)
      from this obtain a where
        "a \<in> \<J>"
        "a \<le> x \<sqinter> -y"
        using join_prime_lower_bound_exists [of "x \<sqinter> -y"]
        by blast
      hence "a \<in> \<lbrace> x \<rbrace>"
        by (simp add: join_prime_embedding_def)
      hence "a \<le> y"
        using \<open>\<Squnion>\<lbrace> x \<rbrace> \<le> y\<close>
              Sup_upper
              order.trans
        by blast
      hence "a \<le> y \<sqinter> -y"
        using \<open>a \<le> x \<sqinter> - y\<close>
              inf.boundedE
              inf_greatest
        by blast
      hence "a = \<bottom>"
        by (simp add: le_bot)
      thus "False"
        using \<open>a \<in> \<J>\<close>
        unfolding join_primes_def
                  join_prime_def
        by fast
    qed
  }
  ultimately show ?thesis
    by (simp add: antisym)
qed

lemma (in finite_boolean_algebra) join_prime_embedding_sup_ident:
  assumes "S \<subseteq> \<J>"
  shows "S = \<lbrace> \<Squnion> S \<rbrace>"
proof -
  have "\<forall> s \<in> S. s \<in> \<J> \<and> s \<le> \<Squnion> S"
    using \<open>S \<subseteq> \<J>\<close> Sup_upper by auto
  hence "S \<subseteq> \<lbrace> \<Squnion> S \<rbrace>"
    unfolding join_prime_embedding_def
    by blast
  moreover
  {
    fix x
    assume "x \<in> \<J>"
           "x \<le> \<Squnion> S"
    have "\<exists> s \<in> S. x \<le> s"
    proof (rule ccontr)
      assume "\<not> (\<exists> s \<in> S. x \<le> s)"
      hence "\<forall> s \<in> S. x \<sqinter> s \<noteq> x"
        using inf.order_iff
        by auto
      moreover
      have "\<forall> s \<in> S. x \<sqinter> s \<le> x"
        by simp
      hence "\<forall> s \<in> S. x \<sqinter> s = \<bottom> \<or> x \<sqinter> s = x"
        using \<open>x \<in> \<J>\<close>
        unfolding join_primes_def
                  join_prime_alt_def
        by blast
      ultimately have "\<forall> s \<in> S. x \<sqinter> s = \<bottom>" by blast
      hence "x \<sqinter> \<Squnion> S = \<bottom>"
        by (simp add: inf_Sup)
      hence "x = \<bottom>"
        using \<open>x \<le> \<Squnion>S\<close> inf.order_iff by blast
      thus "False"
        using \<open>x \<in> \<J>\<close>
        unfolding join_primes_def
                  join_prime_alt_def
        by auto
    qed
    hence "\<exists> s \<in> S. x = s"
      using \<open>x \<in> \<J>\<close>
            \<open>S \<subseteq> \<J>\<close>
      unfolding join_primes_def
                join_prime_alt_def
      by auto
    hence "x \<in> S" by auto
  }
  hence "\<lbrace> \<Squnion> S \<rbrace> \<subseteq> S"
    unfolding join_prime_embedding_def
    by blast
  ultimately show ?thesis by auto
qed

lemma (in finite_boolean_algebra) join_prime_embedding_bij_betw:
  "bij_betw (\<lambda> x. \<lbrace> x \<rbrace>) UNIV (Pow \<J>)"
  unfolding bij_betw_def
proof
  {
    fix x y
    assume "\<lbrace> x \<rbrace> = \<lbrace> y \<rbrace>"
    hence "\<Squnion> \<lbrace> x \<rbrace> = \<Squnion> \<lbrace> y \<rbrace>"
      by simp
    hence "x = y"
      using sup_join_prime_embedding_ident
      by auto
  }
  thus "inj (\<lambda> x. \<lbrace> x \<rbrace>)"
    unfolding inj_def
    by auto
next
  show "range (\<lambda> x. \<lbrace> x \<rbrace>) = Pow \<J>"
  proof (intro equalityI subsetI)
    fix S
    assume "S \<in> range (\<lambda> x. \<lbrace> x \<rbrace>)"
    thus "S \<in> Pow \<J>"
      unfolding join_prime_embedding_def
                Pow_def
      by auto
  next
    fix S
    assume "S \<in> Pow \<J>"
    hence "\<exists> x. \<lbrace> x \<rbrace> = S"
      using join_prime_embedding_sup_ident
      by blast
    thus "S \<in> range (\<lambda> x. \<lbrace> x \<rbrace>)"
      by blast
  qed
qed

lemma (in finite_boolean_algebra) UNIV_card:
  "card (UNIV::'a set) = card (Pow \<J>)"
  using bij_betw_same_card [where f="\<lambda>x. \<lbrace> x \<rbrace>"]
        join_prime_embedding_bij_betw
  by blast

lemma finite_Pow_card:
  assumes "finite X"
  shows "card (Pow X) = 2 powr (card X)"
  using assms
proof (induct X rule: finite_induct)
  case empty
  then show ?case by fastforce
next
  case (insert x X)
  have "0 \<le> (2 :: real)" by auto
  hence two_powr_one: "(2 :: real) = 2 powr 1" by fastforce
  have "bij_betw (\<lambda> x. fst x \<union> snd x) ({{},{x}} \<times> Pow X) (Pow (insert x X))"
    unfolding bij_betw_def
  proof
    {
      fix y z
      assume "y \<in> {{}, {x}} \<times> Pow X"
             "z \<in> {{}, {x}} \<times> Pow X"
             "fst y \<union> snd y = fst z \<union> snd z"
             (is "?Uy = ?Uz")
      hence "x \<notin> snd y"
            "x \<notin> snd z"
            "fst y = {x} \<or> fst y = {}"
            "fst z = {x} \<or> fst z = {}"
        using insert.hyps(2) by auto
      hence "x \<in> ?Uy \<longleftrightarrow> fst y = {x}"
            "x \<in> ?Uz \<longleftrightarrow> fst z = {x}"
            "x \<notin> ?Uy \<longleftrightarrow> fst y = {}"
            "x \<notin> ?Uz \<longleftrightarrow> fst z = {}"
            "snd y = ?Uy - {x}"
            "snd z = ?Uz - {x}"
        by auto
      hence "x \<in> ?Uy \<longleftrightarrow> y = ({x}, ?Uy - {x})"
            "x \<in> ?Uz \<longleftrightarrow> z = ({x}, ?Uz - {x})"
            "x \<notin> ?Uy \<longleftrightarrow> y = ({}, ?Uy - {x})"
            "x \<notin> ?Uz \<longleftrightarrow> z = ({}, ?Uz - {x})"
        by (metis fst_conv prod.collapse)+
      hence "y = z"
        using \<open>?Uy = ?Uz\<close>
        by metis
    }
    thus "inj_on (\<lambda>x. fst x \<union> snd x) ({{}, {x}} \<times> Pow X)"
      unfolding inj_on_def
      by auto
  next
    show "(\<lambda>x. fst x \<union> snd x) ` ({{}, {x}} \<times> Pow X) = Pow (insert x X)"
    proof (intro equalityI subsetI)
      fix y
      assume "y \<in> (\<lambda>x. fst x \<union> snd x) ` ({{}, {x}} \<times> Pow X)"
      from this obtain z where
        "z \<in> ({{}, {x}} \<times> Pow X)"
        "y = fst z \<union> snd z"
        by auto
      hence "snd z \<subseteq> X"
            "fst z \<subseteq> insert x X"
        using SigmaE by auto
      thus "y \<in> Pow (insert x X)"
        using \<open>y = fst z \<union> snd z\<close> by blast
    next
      fix y
      assume "y \<in> Pow (insert x X)"
      let ?z = "(if x \<in> y then {x} else {}, y - {x})"
      have "?z \<in> ({{}, {x}} \<times> Pow X)"
        using \<open>y \<in> Pow (insert x X)\<close> by auto
      moreover have "(\<lambda>x. fst x \<union> snd x) ?z = y"
        by auto
      ultimately show "y \<in> (\<lambda>x. fst x \<union> snd x) ` ({{}, {x}} \<times> Pow X)"
        by blast
    qed
  qed
  hence "card (Pow (insert x X)) = card ({{},{x}} \<times> Pow X)"
    using bij_betw_same_card by fastforce
  also have "\<dots> = 2 * card (Pow X)"
    by (simp add: insert.hyps(1))
  also have "\<dots> = 2 * (2 powr (card X))"
    by (simp add: insert.hyps(3))
  also have "\<dots> = (2 powr 1) * 2 powr (card X)"
    using two_powr_one
    by fastforce
  also have "\<dots> = 2 powr (1 + card X)"
    by (simp add: powr_add)
  also have "\<dots> = 2 powr (card (insert x X))"
    by (simp add: insert.hyps(1) insert.hyps(2))
  finally show ?case .
qed

lemma (in finite_boolean_algebra) UNIV_card_powr_2:
  "card (UNIV::'a set) = 2 powr (card \<J>)"
  using finite [of \<J>]
        finite_Pow_card [of \<J>]
        UNIV_card
  by linarith

lemma (in finite_boolean_algebra) join_primes_card_log_2:
  "card \<J> = log 2 (card (UNIV :: 'a set))"
proof (cases "card (UNIV :: 'a set) = 1")
  case True
  hence "\<exists> x :: 'a. UNIV = {x}"
    using card_1_singletonE by blast
  hence "\<forall> x y :: 'a. x \<in> UNIV \<longrightarrow> y \<in> UNIV \<longrightarrow> x = y"
    by (metis (mono_tags) singletonD)
  hence "\<forall> x y :: 'a. x = y"
    by blast
  hence "\<forall> x. x = \<bottom>"
    by blast
  hence "\<J> = {}"
    unfolding join_primes_def
              join_prime_def
    by blast
  hence "card \<J> = (0 :: real)"
    by simp
  moreover
  have "log 2 (card (UNIV :: 'a set)) = 0"
    by (simp add: True)
  ultimately show ?thesis by auto
next
  case False
  hence "0 < 2 powr (card \<J>)" "2 powr (card \<J>) \<noteq> 1"
    using finite_UNIV_card_ge_0 finite UNIV_card_powr_2
    by (simp, linarith)
  hence "log 2 (2 powr (card \<J>)) = card \<J>"
    by simp
  then show ?thesis
    using UNIV_card_powr_2
    by simp
qed

end
