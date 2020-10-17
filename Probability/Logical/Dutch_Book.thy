chapter \<open>Dutch Book Theorem\<close>

theory Dutch_Book
  imports "../../Logic/Classical/Classical_Connectives"
          "Logical_Probability_Completeness"
          "~~/src/HOL/Real"
begin

record 'p bet_offer =
  bet :: 'p
  amount :: real

record 'p book =
  buys :: "('p bet_offer) list"
  sells ::  "('p bet_offer) list"

definition payoff :: "('p \<Rightarrow> bool) \<Rightarrow> 'p book \<Rightarrow> real" ("\<pi>") where
  [simp]: "\<pi> s b \<equiv>  (\<Sum> i \<leftarrow> sells b. (if s (bet i) then 1 else 0) - amount i)
                   + (\<Sum> i \<leftarrow> buys b. amount i - (if s (bet i) then 1 else 0))"


definition settle_bet :: "('p \<Rightarrow> bool) \<Rightarrow> 'p \<Rightarrow> real" where
  "settle_bet s \<phi> \<equiv> if (s \<phi>) then 1 else 0"

lemma payoff_alt_def1:
  "\<pi> s book =   (\<Sum> i \<leftarrow> sells book. settle_bet s (bet i) - amount i)
              + (\<Sum> i \<leftarrow> buys book. amount i - settle_bet s (bet i))"
  unfolding settle_bet_def
  by simp

definition settle :: "('p \<Rightarrow> bool) \<Rightarrow> 'p bet_offer list \<Rightarrow> real" where
  "settle s bets \<equiv> \<Sum> b \<leftarrow> bets. settle_bet s (bet b)"

definition total_amount :: "('p bet_offer) list \<Rightarrow> real" where
  "total_amount offers \<equiv> \<Sum> i \<leftarrow> offers. amount i"

lemma payoff_alt_def2:
  "\<pi> s book =   settle s (sells book)
              - settle s (buys book)
              + total_amount (buys book)
              - total_amount (sells book)"
  unfolding payoff_alt_def1 total_amount_def settle_def
  by (simp add: sum_list_subtractf)

(* TODO: Cite Lehman *)

definition (in Classical_Logic) possibility :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where
  [simp]: "possibility p \<equiv>    \<not> (p \<bottom>)
                           \<and> (\<forall> \<phi>. \<turnstile> \<phi> \<longrightarrow> p \<phi>)
                           \<and> (\<forall> \<phi> \<psi> . p (\<phi> \<rightarrow> \<psi>) \<longrightarrow> p \<phi> \<longrightarrow> p \<psi>)
                           \<and> (\<forall> \<phi> . p \<phi> \<or> p (\<phi> \<rightarrow> \<bottom>))"

definition (in Classical_Logic) possibilities :: "('a \<Rightarrow> bool) set" where
  [simp]: "possibilities = {p. possibility p}"

lemma (in Classical_Logic) possibility_negation:
  assumes "possibility p"
  shows "p (\<phi> \<rightarrow> \<bottom>) = (\<not> p \<phi>)"
proof
  assume "p (\<phi> \<rightarrow> \<bottom>)"
  show "\<not> p \<phi>"
  proof
    assume "p \<phi>"
    have "\<turnstile> \<phi> \<rightarrow> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>"
      by (simp add: Double_Negation_converse)
    hence "p ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>)"
      using \<open>p \<phi>\<close> \<open>possibility p\<close> by auto
    thus "False" using \<open>p (\<phi> \<rightarrow> \<bottom>)\<close> \<open>possibility p\<close> by auto
  qed
next
  show "\<not> p \<phi> \<Longrightarrow> p (\<phi> \<rightarrow> \<bottom>)" using \<open>possibility p\<close> by fastforce
qed

lemma (in Classical_Logic) possibilities_logical_closure:
  assumes "possibility p"
      and "{x. p x} \<tturnstile> \<phi>"
    shows "p \<phi>"
proof -
  {
    fix \<Gamma>
    assume "set \<Gamma> \<subseteq> Collect p"
    hence "\<forall> \<phi>. \<Gamma> :\<turnstile> \<phi> \<longrightarrow> p \<phi>"
    proof (induct \<Gamma>)
      case Nil
      have "\<forall>\<phi>. \<turnstile> \<phi> \<longrightarrow> p \<phi>"
        using \<open>possibility p\<close> by auto
      then show ?case
        using list_deduction_base_theory by blast
    next
      case (Cons \<gamma> \<Gamma>)
      hence "p \<gamma>"
        by simp
      have "\<forall> \<phi>. \<Gamma> :\<turnstile> \<gamma> \<rightarrow> \<phi> \<longrightarrow> p (\<gamma> \<rightarrow> \<phi>)"
        using Cons.hyps Cons.prems by auto
      then show ?case
        by (meson \<open>p \<gamma>\<close> \<open>possibility p\<close> list_deduction_theorem possibility_def)
    qed
  }
  thus ?thesis
    using \<open>Collect p \<tturnstile> \<phi>\<close> set_deduction_def by auto
qed

lemma (in Classical_Logic) possibilities_are_MCS:
  assumes "possibility p"
  shows "MCS {x. p x}"
  using assms
  by (metis (mono_tags, lifting)
            Formula_Consistent_def
            Formula_Maximally_Consistent_Set_def
            Maximally_Consistent_Set_def
            possibilities_logical_closure
            possibility_def
            mem_Collect_eq)

lemma (in Classical_Logic) MCSs_are_possibilities:
  assumes "MCS s"
  shows "possibility (\<lambda> x. x \<in> s)"
proof -
  have "\<bottom> \<notin> s"
    using \<open>MCS s\<close>
          Formula_Consistent_def
          Formula_Maximally_Consistent_Set_def
          Maximally_Consistent_Set_def
          set_deduction_reflection
    by blast
  moreover have "\<forall> \<phi>. \<turnstile> \<phi> \<longrightarrow> \<phi> \<in> s"
    using \<open>MCS s\<close>
          Formula_Maximally_Consistent_Set_reflection
          Maximally_Consistent_Set_def
          set_deduction_weaken
    by blast
  moreover have "\<forall> \<phi> \<psi>. (\<phi> \<rightarrow> \<psi>) \<in> s \<longrightarrow> \<phi> \<in> s \<longrightarrow> \<psi> \<in> s"
    using \<open>MCS s\<close>
          Formula_Maximal_Consistency
          Formula_Maximally_Consistent_Set_implication
    by blast
  moreover have "\<forall> \<phi>. \<phi> \<in> s \<or> (\<phi> \<rightarrow> \<bottom>) \<in> s"
    using assms
          Formula_Maximally_Consistent_Set_implication
          Maximally_Consistent_Set_def
    by blast
  ultimately show ?thesis by simp
qed

definition (in Classical_Logic) negate_bets ("_\<^sup>\<sim>") where
  "bets\<^sup>\<sim> = [b \<lparr> bet := \<sim> (bet b) \<rparr>. b \<leftarrow> bets]"

lemma (in Classical_Logic) possibility_payoff:
  assumes "possibility p"
  shows   "  \<pi> p \<lparr> buys = buys', sells = sells' \<rparr>
           = settle p (buys'\<^sup>\<sim> @ sells') + total_amount buys' - total_amount sells' - length buys'"
proof (induct buys')
  case Nil
  then show ?case
    unfolding payoff_alt_def2
              negate_bets_def
              total_amount_def
              settle_def
              settle_bet_def
    by simp
next
  case (Cons b buys')
  have "p (\<sim> (bet b)) = (\<not> (p (bet b)))" using assms negation_def by auto
  moreover have "  total_amount ((b # buys') @ sells')
                 = amount b + total_amount buys' + total_amount sells'"
    unfolding total_amount_def
    by (induct buys', induct sells', auto)
  ultimately show ?case
    using Cons
    unfolding payoff_alt_def2 negate_bets_def settle_def settle_bet_def
    by simp
qed

lemma (in Consistent_Classical_Logic) minimum_payoff_existence:
  "\<exists>! x. (\<exists> p \<in> possibilities. \<pi> p bets = x) \<and> (\<forall> q \<in> possibilities. x \<le> \<pi> q bets)"
proof (rule ex_ex1I)
  show "\<exists>x. (\<exists>p\<in>possibilities. \<pi> p bets = x) \<and> (\<forall>q\<in>possibilities. x \<le> \<pi> q bets)"
  proof (rule ccontr)
    obtain buys' sells' where "bets = \<lparr> buys = buys', sells = sells' \<rparr>"
      by (metis book.cases)
    assume "\<nexists>x. (\<exists> p \<in> possibilities. \<pi> p bets = x) \<and> (\<forall> q \<in> possibilities. x \<le> \<pi> q bets)"
    hence "\<forall>x. (\<exists> p \<in> possibilities. \<pi> p bets = x) \<longrightarrow> (\<exists> q \<in> possibilities. \<pi> q bets < x)"
      by (meson le_less_linear)
    hence \<star>: "\<forall>p \<in> possibilities. \<exists> q \<in> possibilities. \<pi> q bets < \<pi> p bets"
      by blast
    have \<lozenge>: "\<forall> p \<in> possibilities. \<exists> q \<in> possibilities.
                    settle q (buys'\<^sup>\<sim> @ sells') < settle p (buys'\<^sup>\<sim> @ sells')"
    proof
      fix p
      assume "p \<in> possibilities"
      from this obtain q where "q \<in> possibilities" and "\<pi> q bets < \<pi> p bets"
        using \<star> by blast
      hence
        "  settle q (buys'\<^sup>\<sim> @ sells') + total_amount buys' - total_amount sells' - length buys'
         < settle p (buys'\<^sup>\<sim> @ sells') + total_amount buys' - total_amount sells' - length buys'"
        by (metis \<open>\<pi> q bets < \<pi> p bets\<close>
                  \<open>bets = \<lparr>buys = buys', sells = sells'\<rparr>\<close>
                  \<open>p \<in> possibilities\<close>
                  possibilities_def
                  possibility_payoff
                  mem_Collect_eq)
      hence "settle q (buys'\<^sup>\<sim> @ sells') < settle p (buys'\<^sup>\<sim> @ sells')"
        by simp
      thus "\<exists>q\<in>possibilities. settle q (buys'\<^sup>\<sim> @ sells') < settle p (buys'\<^sup>\<sim> @ sells')"
        using \<open>q \<in> possibilities\<close> by blast
    qed
    {
      fix bets :: "('a bet_offer) list"
      fix s :: "'a \<Rightarrow> bool"
      have "\<exists> n \<in> \<nat>. settle s bets = real n"
        unfolding settle_def settle_bet_def
        by (induct bets, auto, metis Nats_1 Nats_add Suc_eq_plus1_left of_nat_Suc)
    } note \<dagger> = this
    {
      fix n :: "nat"
      have "    (\<exists> p \<in> possibilities. settle p (buys'\<^sup>\<sim> @ sells') \<le> n)
            \<longrightarrow> (\<exists> q \<in> possibilities. settle q (buys'\<^sup>\<sim> @ sells') < 0)" (is "_ \<longrightarrow> ?consequent")
      proof (induct n)
        case 0
        {
          fix p :: "'a \<Rightarrow> bool"
          assume"p \<in> possibilities" and "settle p (buys'\<^sup>\<sim> @ sells') \<le> 0"
          from this obtain q where
            "q \<in> possibilities"
            "settle q (buys'\<^sup>\<sim> @ sells') < settle p (buys'\<^sup>\<sim> @ sells')"
            using \<lozenge> by blast
          hence ?consequent
            by (metis "\<dagger>" \<open>settle p (buys'\<^sup>\<sim> @ sells') \<le> 0\<close> of_nat_0_eq_iff of_nat_le_0_iff)
        }
        then show ?case by auto
      next
        case (Suc n)
        {
          fix p :: "'a \<Rightarrow> bool"
          assume"p \<in> possibilities" and "settle p (buys'\<^sup>\<sim> @ sells') \<le> Suc n"
          from this obtain q\<^sub>1 where
            "q\<^sub>1 \<in> possibilities"
            "settle q\<^sub>1 (buys'\<^sup>\<sim> @ sells') < Suc n"
            by (metis \<lozenge> antisym_conv not_less)
          from this obtain q\<^sub>2 where
            "q\<^sub>2 \<in> possibilities"
            "settle q\<^sub>2 (buys'\<^sup>\<sim> @ sells') < n"
            using \<lozenge>
            by (metis \<dagger> add.commute nat_le_real_less nat_less_le of_nat_Suc of_nat_less_iff)
          hence ?consequent
            by (metis \<dagger> Suc.hyps nat_less_le of_nat_le_iff of_nat_less_iff)
        }
        then show ?case by auto
      qed
    }
    hence "\<nexists> p. p \<in> possibilities"
      by (metis \<dagger> not_less0 of_nat_0 of_nat_less_iff order_refl)
    moreover
    have "\<not> {} \<tturnstile> \<bottom>"
      using consistency set_deduction_base_theory by auto
    from this obtain \<Gamma> where "MCS \<Gamma>"
      by (meson Formula_Consistent_def
                Formula_Maximal_Consistency
                Formula_Maximally_Consistent_Extension)
    hence "(\<lambda> \<gamma>. \<gamma> \<in> \<Gamma>) \<in> possibilities"
      using MCSs_are_possibilities possibilities_def by blast
    ultimately show False
      by blast
  qed
next
  fix x y
  assume A: "(\<exists>p \<in> possibilities. \<pi> p bets = x) \<and> (\<forall>q \<in> possibilities. x \<le> \<pi> q bets)"
  and B: "(\<exists>p \<in> possibilities. \<pi> p bets = y) \<and> (\<forall>q \<in> possibilities. y \<le> \<pi> q bets)"
  from this obtain p\<^sub>x p\<^sub>y where
    "p\<^sub>x \<in> possibilities"
    "p\<^sub>y \<in> possibilities"
    "\<pi> p\<^sub>x bets = x"
    "\<pi> p\<^sub>y bets = y"
    by blast
  with A B have "x \<le> y" "y \<le> x"
    by blast+
  thus "x = y" by linarith
qed

definition (in Consistent_Classical_Logic)
  minimum_payoff :: "'a book \<Rightarrow> real" ("\<pi>\<^sub>m\<^sub>i\<^sub>n") where
  "\<pi>\<^sub>m\<^sub>i\<^sub>n b \<equiv> THE x. (\<exists> p \<in> possibilities. \<pi> p b = x) \<and> (\<forall> q \<in> possibilities. x \<le> \<pi> q b)"

lemma (in Classical_Logic) possibility_payoff_dual:
  assumes "possibility p"
  shows   "  \<pi> p \<lparr> buys = buys', sells = sells' \<rparr>
           = - settle p (sells'\<^sup>\<sim> @ buys')
             + total_amount buys' + length sells' - total_amount sells'"
proof (induct sells')
  case Nil
  then show ?case
    unfolding payoff_alt_def2
              negate_bets_def
              total_amount_def
              settle_def
    by simp
next
  case (Cons sell' sells')
  have "p (\<sim> (bet sell')) = (\<not> (p (bet sell')))" using assms negation_def by auto
  moreover have "total_amount ((sell' # sells') @ buys')
                 = amount sell' + total_amount sells' + total_amount buys'"
    unfolding total_amount_def
    by (induct buys', induct sells', auto)
  ultimately show ?case
    using Cons
    unfolding payoff_alt_def2 negate_bets_def settle_def settle_bet_def
    by simp
qed

lemma settle_alt_def: "settle q bets = length [\<phi> \<leftarrow> [ bet b . b \<leftarrow> bets ] . q \<phi>]"
  unfolding settle_def settle_bet_def
  by (induct bets, simp+)

section \<open> Market Dutch Book Theorems \label{sec:dutch-book-theorem} \<close>

subsection \<open> MaxSat Reduction \label{subsec:dutch-book-maxsat-reduction} \<close>

theorem (in Consistent_Classical_Logic) dutch_book_maxsat:
  "  (k \<le> \<pi>\<^sub>m\<^sub>i\<^sub>n \<lparr> buys = buys', sells = sells' \<rparr>)
   = (  MaxSat [bet b . b \<leftarrow> sells'\<^sup>\<sim> @ buys'] + (k :: real)
      \<le> total_amount buys' + length sells' - total_amount sells')"
  (is "(k \<le> \<pi>\<^sub>m\<^sub>i\<^sub>n ?bets) = (MaxSat ?props + k \<le> total_amount _ + _ - _)")
proof
  assume "k \<le> \<pi>\<^sub>m\<^sub>i\<^sub>n ?bets"
  let ?P = "\<lambda> x . (\<exists> p \<in> possibilities. \<pi> p ?bets = x) \<and> (\<forall> q \<in> possibilities. x \<le> \<pi> q ?bets)"
  obtain p where "possibility p" and "\<forall> q \<in> possibilities. \<pi> p ?bets \<le> \<pi> q ?bets"
    using \<open>k \<le> \<pi>\<^sub>m\<^sub>i\<^sub>n ?bets\<close>
          minimum_payoff_existence [of ?bets]
    by (metis possibilities_def mem_Collect_eq)
  hence "?P (\<pi> p ?bets)"
    using possibilities_def by blast
  hence "\<pi>\<^sub>m\<^sub>i\<^sub>n ?bets = \<pi> p ?bets"
    unfolding minimum_payoff_def
    using minimum_payoff_existence [of ?bets]
          the1_equality [where P = ?P and a = "\<pi> p ?bets"]
    by blast

  let ?\<Phi> = "[\<phi> \<leftarrow> ?props. p \<phi>]"

  have "mset ?\<Phi> \<subseteq># mset ?props"
    by(induct ?props,
       auto,
       simp add: subset_mset.add_mono)
  moreover
  have "\<not> (?\<Phi> :\<turnstile> \<bottom>)"
  proof -
    have "set ?\<Phi> \<subseteq> {x. p x}"
      by auto
    hence "\<not> (set ?\<Phi> \<tturnstile> \<bottom>)"
      by (meson \<open>possibility p\<close>
                possibilities_are_MCS [of p]
                Formula_Consistent_def
                Formula_Maximally_Consistent_Set_def
                Maximally_Consistent_Set_def
                list_deduction_monotonic
                set_deduction_def)
    thus ?thesis
      using set_deduction_def by blast
  qed
  moreover
  {
    fix \<Psi>
    assume "mset \<Psi> \<subseteq># mset ?props" and "\<not> \<Psi> :\<turnstile> \<bottom>"
    from this obtain \<Omega>\<^sub>\<Psi> where "MCS \<Omega>\<^sub>\<Psi>" and "set \<Psi> \<subseteq> \<Omega>\<^sub>\<Psi>"
      by (meson Formula_Consistent_def
                Formula_Maximal_Consistency
                Formula_Maximally_Consistent_Extension
                list_deduction_monotonic
                set_deduction_def)
    let ?q = "\<lambda>\<phi> . \<phi> \<in> \<Omega>\<^sub>\<Psi>"
    have "possibility ?q"
      using \<open>MCS \<Omega>\<^sub>\<Psi>\<close> MCSs_are_possibilities by blast
    hence "\<pi> p ?bets \<le> \<pi> ?q ?bets"
      using \<open>\<forall>q\<in>possibilities. \<pi> p ?bets \<le> \<pi> q ?bets\<close>
            possibilities_def
      by blast
    let ?c = "total_amount buys' + length sells' - total_amount sells'"
    have "- settle p (sells'\<^sup>\<sim> @ buys') + ?c \<le> - settle ?q (sells'\<^sup>\<sim> @ buys') + ?c"
      using \<open>\<pi> p ?bets \<le> \<pi> ?q ?bets\<close>
            \<open>possibility p\<close>
            possibility_payoff_dual [of p buys' sells']
            \<open>possibility ?q\<close>
            possibility_payoff_dual [of ?q buys' sells']
      by linarith
    hence "settle ?q (sells'\<^sup>\<sim> @ buys') \<le> settle p (sells'\<^sup>\<sim> @ buys')"
      by linarith
    let ?\<Psi>' = "[\<phi> \<leftarrow> ?props. ?q \<phi>]"
    have "length ?\<Psi>' \<le> length ?\<Phi>"
      using \<open>settle ?q (sells'\<^sup>\<sim> @ buys') \<le> settle p (sells'\<^sup>\<sim> @ buys')\<close>
      unfolding settle_alt_def
      by simp
    moreover
    have "length \<Psi> \<le> length ?\<Psi>'"
    proof -
      have "mset [\<psi> \<leftarrow> \<Psi>. ?q \<psi>] \<subseteq># mset ?\<Psi>'"
      proof -
        {
          fix props :: "'a list"
          have "\<forall> \<Psi>. \<forall> \<Omega>. mset \<Psi> \<subseteq># mset props \<longrightarrow>
                            mset [\<psi> \<leftarrow> \<Psi>. \<psi> \<in> \<Omega>] \<subseteq># mset [\<phi> \<leftarrow> props. \<phi> \<in> \<Omega>]"
            by (simp add: multiset_filter_mono)
        }
        thus ?thesis
          using \<open>mset \<Psi> \<subseteq># mset ?props\<close> by blast
      qed
      hence "length [\<psi> \<leftarrow> \<Psi>. ?q \<psi>] \<le> length ?\<Psi>'"
        by (metis (no_types, lifting) length_sub_mset mset_eq_length nat_less_le not_le)
      moreover have "length \<Psi> = length [\<psi> \<leftarrow> \<Psi>. ?q \<psi>]"
        using \<open>set \<Psi> \<subseteq> \<Omega>\<^sub>\<Psi>\<close>
        by (induct \<Psi>, simp+)
      ultimately show ?thesis by linarith
    qed
    ultimately have "length \<Psi> \<le> length ?\<Phi>" by linarith
  }
  ultimately have "?\<Phi> \<in> \<C> ?props \<bottom>"
    unfolding unproving_core_def
    by blast
  hence "MaxSat ?props = length ?\<Phi>"
    using core_size_intro by presburger
  hence "MaxSat ?props = settle p (sells'\<^sup>\<sim> @ buys')"
    unfolding settle_alt_def
    by simp
  thus "MaxSat ?props + k \<le> total_amount buys' + length sells' - total_amount sells'"
    using possibility_payoff_dual [of p buys' sells']
          \<open>k \<le> \<pi>\<^sub>m\<^sub>i\<^sub>n ?bets\<close>
          \<open>\<pi>\<^sub>m\<^sub>i\<^sub>n ?bets = \<pi> p ?bets\<close>
          \<open>possibility p\<close>
    by linarith
next
  let ?c = "total_amount buys' + length sells' - total_amount sells'"
  assume "MaxSat ?props + k \<le> ?c"
  from this obtain \<Phi> where "\<Phi> \<in> \<C> ?props \<bottom>" and "length \<Phi> + k \<le> ?c"
    using consistency core_size_intro unproving_core_existence by fastforce
  hence "\<not> \<Phi> :\<turnstile> \<bottom>"
    using unproving_core_def by blast
  from this obtain \<Omega>\<^sub>\<Phi> where "MCS \<Omega>\<^sub>\<Phi>" and "set \<Phi> \<subseteq> \<Omega>\<^sub>\<Phi>"
    by (meson Formula_Consistent_def
              Formula_Maximal_Consistency
              Formula_Maximally_Consistent_Extension
              list_deduction_monotonic
              set_deduction_def)
  let ?p = "\<lambda>\<phi> . \<phi> \<in> \<Omega>\<^sub>\<Phi>"
  have "possibility ?p"
    using \<open>MCS \<Omega>\<^sub>\<Phi>\<close> MCSs_are_possibilities by blast
  have "mset \<Phi> \<subseteq># mset ?props"
    using \<open>\<Phi> \<in> \<C> ?props \<bottom>\<close> unproving_core_def by blast
  have "mset \<Phi> \<subseteq># mset [ b \<leftarrow> ?props. ?p b]"
    by (metis \<open>mset \<Phi> \<subseteq># mset ?props\<close>
              \<open>set \<Phi> \<subseteq> \<Omega>\<^sub>\<Phi>\<close>
              filter_True
              mset_filter
              multiset_filter_mono
              subset_code(1))
  have "mset \<Phi> = mset [ b \<leftarrow> ?props. ?p b]"
  proof (rule ccontr)
    assume "mset \<Phi> \<noteq> mset [ b \<leftarrow> ?props. ?p b]"
    hence "length \<Phi> < length [ b \<leftarrow> ?props. ?p b]"
      using \<open>mset \<Phi> \<subseteq># mset [ b \<leftarrow> ?props. ?p b]\<close> length_sub_mset not_less by blast
    moreover
    have "\<not> [ b \<leftarrow> ?props. ?p b] :\<turnstile> \<bottom>"
      by (metis IntE
                \<open>MCS \<Omega>\<^sub>\<Phi>\<close>
                inter_set_filter
                Formula_Consistent_def
                Formula_Maximally_Consistent_Set_def
                Maximally_Consistent_Set_def
                set_deduction_def
                subsetI)
    hence "length [ b \<leftarrow> ?props. ?p b] \<le> length \<Phi>"
      by (metis (mono_tags, lifting)
                \<open>\<Phi> \<in> \<C> ?props \<bottom>\<close>
                unproving_core_def [of ?props \<bottom>]
                mem_Collect_eq
                mset_filter
                multiset_filter_subset)
    ultimately show "False"
      using not_le by blast
  qed
  hence "length \<Phi> = settle ?p (sells'\<^sup>\<sim> @ buys')"
    unfolding settle_alt_def
    using mset_eq_length by fastforce
  hence "k \<le> settle ?p (sells'\<^sup>\<sim> @ buys')
             + total_amount buys' + length sells' - total_amount sells'"
    using \<open>length \<Phi> + k \<le> ?c\<close> by linarith
  hence "k \<le> \<pi> ?p ?bets"
    using \<open>possibility ?p\<close>
          possibility_payoff_dual [of ?p buys' sells']
          \<open>length \<Phi> + k \<le> ?c\<close>
          \<open>length \<Phi> = settle ?p (sells'\<^sup>\<sim> @ buys')\<close>
    by linarith
  have "\<forall> q \<in> possibilities. \<pi> ?p ?bets \<le> \<pi> q ?bets"
  proof
    fix q
    assume "q \<in> possibilities"
    hence "\<not> [ b \<leftarrow> ?props. q b] :\<turnstile> \<bottom>"
      unfolding possibilities_def
      by (metis filter_set
                possibilities_logical_closure
                possibility_def
                set_deduction_def
                mem_Collect_eq
                member_filter
                subsetI)
    hence "length [ b \<leftarrow> ?props. q b] \<le> length \<Phi>"
      by (metis (mono_tags, lifting)
                \<open>\<Phi> \<in> \<C> ?props \<bottom>\<close>
                unproving_core_def
                mem_Collect_eq
                mset_filter
                multiset_filter_subset)
    hence
      "  - settle ?p (sells'\<^sup>\<sim> @ buys') + total_amount buys' + length sells' - total_amount sells'
       \<le> - settle q (sells'\<^sup>\<sim> @ buys') + total_amount buys' + length sells' - total_amount sells'"
      using \<open>length \<Phi> = settle ?p (sells'\<^sup>\<sim> @ buys')\<close>
            settle_alt_def [of q "sells'\<^sup>\<sim> @ buys'"]
      by linarith
    thus "\<pi> ?p ?bets \<le> \<pi> q ?bets"
      using possibility_payoff_dual [of ?p buys' sells']
            possibility_payoff_dual [of q buys' sells']
            \<open>possibility ?p\<close>
            \<open>q \<in> possibilities\<close>
      unfolding possibilities_def
      by (metis mem_Collect_eq)
  qed
  have "\<pi>\<^sub>m\<^sub>i\<^sub>n ?bets = \<pi> ?p ?bets"
    unfolding minimum_payoff_def
  proof
    show "(\<exists>p\<in>possibilities. \<pi> p ?bets = \<pi> ?p ?bets) \<and> (\<forall>q\<in>possibilities. \<pi> ?p ?bets \<le> \<pi> q ?bets)"
      using \<open>\<forall> q \<in> possibilities. \<pi> ?p ?bets \<le> \<pi> q ?bets\<close>
            \<open>possibility ?p\<close>
      unfolding possibilities_def
      by blast
  next
    fix n
    assume \<star>: "(\<exists>p\<in>possibilities. \<pi> p ?bets = n) \<and> (\<forall>q\<in>possibilities. n \<le> \<pi> q ?bets)"
    from this obtain p where "\<pi> p ?bets = n" and "possibility p"
      using possibilities_def by blast
    hence "\<pi> p ?bets \<le> \<pi> ?p ?bets"
      using \<star> \<open>possibility ?p\<close>
      unfolding possibilities_def
      by blast
    moreover have "\<pi> ?p ?bets \<le> \<pi> p ?bets"
      using \<open>\<forall> q \<in> possibilities. \<pi> ?p ?bets \<le> \<pi> q ?bets\<close>
            \<open>possibility p\<close>
      unfolding possibilities_def
      by blast
    ultimately show "n = \<pi> ?p ?bets" using \<open>\<pi> p ?bets = n\<close> by linarith
  qed
  thus "k \<le> \<pi>\<^sub>m\<^sub>i\<^sub>n ?bets"
    using \<open>k \<le> \<pi> ?p ?bets\<close>
    by auto
qed

lemma (in Consistent_Classical_Logic) nonstrict_dutch_book:
  "  (k \<le> \<pi>\<^sub>m\<^sub>i\<^sub>n \<lparr> buys = buys', sells = sells' \<rparr>)
   = (\<forall> Pr \<in> Logical_Probabilities.
         (\<Sum>b\<leftarrow>buys'. Pr (bet b)) + total_amount sells' + k
       \<le> (\<Sum>s\<leftarrow>sells'. Pr (bet s)) + total_amount buys')"
  (is "?lhs = _")
proof -
  let ?tot_ss = "total_amount sells'" and ?tot_bs = "total_amount buys'"
  have "[bet b . b \<leftarrow> sells'\<^sup>\<sim> @ buys'] = \<^bold>\<sim> [bet s. s \<leftarrow> sells'] @ [bet b. b \<leftarrow> buys']"
    (is "_ = \<^bold>\<sim> ?sell_\<phi>s @ ?buy_\<phi>s")
    unfolding negate_bets_def
    by (induct sells', simp+)
  hence "?lhs = (MaxSat (\<^bold>\<sim> ?sell_\<phi>s @ ?buy_\<phi>s) + k \<le> ?tot_bs + length sells' - ?tot_ss)"
    using dutch_book_maxsat [of k buys' sells'] by auto
  also have "\<dots> = (MaxSat (\<^bold>\<sim> ?sell_\<phi>s @ ?buy_\<phi>s) + (?tot_ss - ?tot_bs + k) \<le> length sells')"
    by linarith
  also have "\<dots> = (MaxSat (\<^bold>\<sim> ?sell_\<phi>s @ ?buy_\<phi>s) + (?tot_ss - ?tot_bs + k) \<le> length ?sell_\<phi>s)"
    by simp
  finally have I: "?lhs = (\<forall> Pr \<in> Dirac_Measures.
    (\<Sum>\<phi>\<leftarrow>?buy_\<phi>s. Pr \<phi>) + (?tot_ss - ?tot_bs + k) \<le> (\<Sum>\<gamma>\<leftarrow>?sell_\<phi>s. Pr \<gamma>))"
    using binary_inequality_equiv [of ?buy_\<phi>s "?tot_ss - ?tot_bs + k" ?sell_\<phi>s]
    by blast
  moreover
  {
    fix Pr :: "'a \<Rightarrow> real"
    have "(\<Sum>\<phi>\<leftarrow>?buy_\<phi>s. Pr \<phi>) = (\<Sum>b\<leftarrow>buys'. Pr (bet b))"
         "(\<Sum>\<gamma>\<leftarrow>?sell_\<phi>s. Pr \<gamma>) = (\<Sum>s\<leftarrow>sells'. Pr (bet s))"
      by (simp add: comp_def)+
    hence "  ((\<Sum>\<phi>\<leftarrow>?buy_\<phi>s. Pr \<phi>) + (?tot_ss - ?tot_bs + k) \<le> (\<Sum>\<gamma>\<leftarrow>?sell_\<phi>s. Pr \<gamma>))
           = ((\<Sum>b\<leftarrow>buys'. Pr (bet b)) + ?tot_ss + k \<le> (\<Sum>s\<leftarrow>sells'. Pr (bet s)) + ?tot_bs)"
      by linarith
  }
  ultimately show ?thesis
    by (meson Dirac_Measures_subset dirac_ceiling dirac_collapse subset_eq)
qed

lemma (in Consistent_Classical_Logic) strict_dutch_book:
  "  (k < \<pi>\<^sub>m\<^sub>i\<^sub>n \<lparr> buys = buys', sells = sells' \<rparr>)
   = (\<forall> Pr \<in> Logical_Probabilities.
         (\<Sum>b\<leftarrow>buys'. Pr (bet b)) + total_amount sells' + k
       < (\<Sum>s\<leftarrow>sells'. Pr (bet s)) + total_amount buys')"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  from this obtain \<epsilon> where "0 < \<epsilon>" "k + \<epsilon> \<le> \<pi>\<^sub>m\<^sub>i\<^sub>n \<lparr>buys = buys', sells = sells'\<rparr>"
    using less_diff_eq by fastforce
  hence "\<forall>Pr \<in> Logical_Probabilities.
            (\<Sum>b\<leftarrow>buys'. Pr (bet b)) + total_amount sells' + (k + \<epsilon>)
          \<le> (\<Sum>s\<leftarrow>sells'. Pr (bet s)) + total_amount buys'"
    using nonstrict_dutch_book [of "k + \<epsilon>" buys' sells'] by auto
  thus ?rhs
    using \<open>0 < \<epsilon>\<close> by auto
next
  have "[bet b . b \<leftarrow> sells'\<^sup>\<sim> @ buys'] = \<^bold>\<sim> [bet s. s \<leftarrow> sells'] @ [bet b. b \<leftarrow> buys']"
    (is "_ = \<^bold>\<sim> ?sell_\<phi>s @ ?buy_\<phi>s")
    unfolding negate_bets_def
    by (induct sells', simp+)
  {
    fix Pr :: "'a \<Rightarrow> real"
    have "(\<Sum>b\<leftarrow>buys'. Pr (bet b)) = (\<Sum>\<phi>\<leftarrow>?buy_\<phi>s. Pr \<phi>)"
         "(\<Sum>b\<leftarrow>sells'. Pr (bet b)) = (\<Sum>\<phi>\<leftarrow>?sell_\<phi>s. Pr \<phi>)"
      by (induct buys', auto, induct sells', auto)
  }
  note \<star> =  this
  let ?tot_ss = "total_amount sells'" and ?tot_bs = "total_amount buys'"
  let ?c = "?tot_ss + k - ?tot_bs"
  assume ?rhs
  have "\<forall> Pr \<in> Logical_Probabilities. (\<Sum>b\<leftarrow>buys'. Pr (bet b)) + ?c < (\<Sum>s\<leftarrow>sells'. Pr (bet s))"
    using \<open>?rhs\<close> by fastforce
  hence "\<forall> Pr \<in> Logical_Probabilities. (\<Sum>\<phi>\<leftarrow>?buy_\<phi>s. Pr \<phi>) + ?c < (\<Sum>\<phi>\<leftarrow>?sell_\<phi>s. Pr \<phi>)"
    using \<star> by auto
  hence "\<forall> Pr \<in> Dirac_Measures. (\<Sum>\<phi>\<leftarrow>?buy_\<phi>s. Pr \<phi>) + (\<lfloor>?c\<rfloor> + 1) \<le> (\<Sum>\<phi>\<leftarrow>?sell_\<phi>s. Pr \<phi>)"
    using strict_dirac_collapse [of ?buy_\<phi>s ?c ?sell_\<phi>s]
    by auto
  hence "MaxSat (\<^bold>\<sim> ?sell_\<phi>s @ ?buy_\<phi>s) + (\<lfloor>?c\<rfloor> + 1) \<le> length ?sell_\<phi>s"
    by (metis floor_add_int floor_mono floor_of_nat binary_inequality_equiv)
  hence "MaxSat (\<^bold>\<sim> ?sell_\<phi>s @ ?buy_\<phi>s) + ?c < length ?sell_\<phi>s"
    by linarith
  from this obtain \<epsilon> :: real where
    "0 < \<epsilon>"
    "MaxSat (\<^bold>\<sim> ?sell_\<phi>s @ ?buy_\<phi>s) + (k + \<epsilon>) \<le> ?tot_bs + length sells' - ?tot_ss"
    using less_diff_eq by fastforce
  hence "k + \<epsilon> \<le> \<pi>\<^sub>m\<^sub>i\<^sub>n \<lparr>buys = buys', sells = sells'\<rparr>"
    using \<open>[bet b . b \<leftarrow> sells'\<^sup>\<sim> @ buys'] = \<^bold>\<sim> ?sell_\<phi>s @ ?buy_\<phi>s\<close>
          dutch_book_maxsat [of "k + \<epsilon>" buys' sells']
    by simp
  thus ?lhs
    using \<open>0 < \<epsilon>\<close> by linarith
qed

theorem (in Consistent_Classical_Logic) dutch_book:
  "  (0 < \<pi>\<^sub>m\<^sub>i\<^sub>n \<lparr> buys = buys', sells = sells' \<rparr>)
   = (\<forall> Pr \<in> Logical_Probabilities.
         (\<Sum>b\<leftarrow>buys'. Pr (bet b)) + total_amount sells'
       < (\<Sum>s\<leftarrow>sells'. Pr (bet s)) + total_amount buys')"
  by (simp add: strict_dutch_book)

end