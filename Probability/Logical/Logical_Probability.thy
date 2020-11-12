(*:maxLineLen=78:*)

chapter \<open> Probability Logic \label{chapter:probability} \<close>

theory Logical_Probability
  imports
    "../../Logic/Classical/Classical_Connectives"
    HOL.Real
begin

sledgehammer_params [smt_proofs = false]

section \<open> Definition of Probability Logic \label{sec:definition-of-probability-logic} \<close>

text \<open> Probability logic is defined in terms of an operator over
       classical logic obeying certain postulates. Scholars often credit
       George Boole for first conceiving this kind of formulation @{cite booleChapterXVITheory1853}.
       Theodore Hailperin in particular has written extensively on this subject
       @{cite hailperinProbabilityLogic1984
         and hailperinBooleLogicProbability1986
         and hailperinSententialProbabilityLogic1996}. \<close>

text \<open> The presentation below roughly follows Kolmogorov's axiomatization
       @{cite kolmogoroffChapterElementareWahrscheinlichkeitsrechnung1933}.
       A key difference is that we only require \<^emph>\<open>finite additivity\<close>, rather
       than \<^emph>\<open>countable additivity\<close>. Finite additivity is also defined in
       terms of \<^term>\<open>(\<rightarrow>)\<close>. This formulation is required so that
       probability logic may be extended to Boolean algebra in \S\ref{subsec:boolean-algebra-probability}. \<close>

class probability_logic = classical_logic +
  fixes Pr :: "'a \<Rightarrow> real"
  assumes probability_non_negative: "Pr \<phi> \<ge> 0"
  assumes probability_unity: "\<turnstile> \<phi> \<Longrightarrow> Pr \<phi> = 1"
  assumes probability_implicational_additivity:
    "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom> \<Longrightarrow> Pr ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>) = Pr \<phi> + Pr \<psi>"

text \<open> A similar axiomatization may be credited to
       Rescher @{cite \<open>pg. 185\<close> rescherManyvaluedLogic1969}.
       However, our formulation has fewer axioms.
       While Rescher assumes \<^term>\<open>\<turnstile> \<phi> \<leftrightarrow> \<psi> \<Longrightarrow> Pr \<phi> = Pr \<psi>\<close>, we
       provide it as a lemma in \S\ref{subsec:prob-logic-alt-def}. \<close>

subsection \<open> Why Finite Additivity? \<close>

text \<open> In this section we briefly touch on why we have chosen to
       employ finite additivity in our axiomatization of
       @{class probability_logic} and deviate from conventional
       probability theory. The argument here is essentially due to
       Giaangiacomo Gerla @{cite \<open>Section 3\<close> gerlaInferencesProbabilityLogic1994}. \<close>

text \<open> Conventional probability obeys an axiom known as \<^emph>\<open>countable additivity\<close>.
       Roughly, it states if \<open>?S\<close> is a countable set of sets which are
       pairwise disjoint, then the limit \<open>\<Sum> s \<in> ?S. Pr s\<close> exists and
       \<open>Pr (\<Union> ?S) = (\<Sum> s \<in> ?S. Pr s)\<close>. This is more powerful than our
       finite additivity axiom
       @{lemma \<open>\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom> \<Longrightarrow> Pr ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>) = Pr \<phi> + Pr \<psi>\<close>
          by (metis probability_implicational_additivity) }. \<close>

text \<open> Requiring an analogue of countable additivity in
       @{class probability_logic} would prevent us from establishing
       the Dutch book theorem from Chapter \ref{chap:dutch-book-theorem}
       in certain practical settings. \<close>

text \<open> The reason boils down to a theorem of Horn and Tarski,
       which establishes that there can be no \<open>\<sigma>\<close>-measure over a countable
       atomless Boolean algebra @{cite \<open>Theorem 3.2\<close> hornMeasuresBooleanAlgebras1948}. \<close>

text \<open> In particular, this means the type @{typ "'a classical_propositional_formula"}
       does not have a corresponding \<open>\<sigma>\<close>-measure in general. Specifically,
       the quotient type of @{typ "'a classical_propositional_formula"}
       under @{term "\<lambda> \<phi> \<psi> . \<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<leftrightarrow> \<psi>"} is an atomless Boolean algebra,
       known as the \<^emph>\<open>Lindenbaum algebra\<close>.  In the case of
       @{typ "nat classical_propositional_formula"} this algebra is countable,
       and hence has no \<open>\<sigma>\<close>-measure. \<close>

text \<open> But a software trading system might use data structures
       like @{typ "'a classical_propositional_formula"} when analyzing
       fixed odds gambling markets. We go into detail regarding this in
       \S\ref{sec:fixed-odds-markets}.  Both \<^emph>\<open>Haskell\<close> and
       \<^emph>\<open>Rust\<close> allow for declaring data types like @{typ "'a classical_propositional_formula"}.
       These languages share a heritage from ML languages just like
       Isabelle/HOL. Certain implementations might even model markets
       using data types with countable inhabitants. \<close>

text \<open> Hence, if we insist on countably additivity then the Dutch Book theorem
       presented in \S\ref{subsec:probability-dutch-book} cannot be obtained
       for certain programs we may reasonably wish to write. Not only
       is our formulation in @{class probability_logic} suitable for
       obtaining the Dutch book theorem, it is not obvious what more we can
       demand and still obtain our result. \<close>

text \<open> The above argument is not intended as a refutation of conventional
       probability theory. It is simply an impossibility result with respect
       to our Dutch book theorem. Plenty of classic results in probability
       rely on countable additivity. A nice example recently formalized in
       Isabelle/HOL is Bouffon's needle @{cite eberlBuffonNeedleProblem2017}. \<close>

subsection \<open> Basic Properties of Probability Logic \<close>

lemma (in probability_logic) probability_additivity:
  assumes "\<turnstile> \<sim> (\<phi> \<sqinter> \<psi>)"
  shows "Pr (\<phi> \<squnion> \<psi>) = Pr \<phi> + Pr \<psi>"
  using
    assms
  unfolding
    conjunction_def
    disjunction_def
    negation_def
  by (simp add: probability_implicational_additivity)

lemma (in probability_logic) probability_alternate_additivity:
  assumes "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom>"
  shows "Pr (\<phi> \<squnion> \<psi>) = Pr \<phi> + Pr \<psi>"
  using assms
  by (metis
        probability_additivity
        double_negation_converse
        modus_ponens
        conjunction_def
        negation_def)

lemma (in probability_logic) complementation:
  "Pr (\<sim> \<phi>) = 1 - Pr \<phi>"
  by (metis
        probability_alternate_additivity
        probability_unity
        bivalence
        negation_elimination
        add.commute
        add_diff_cancel_left')

lemma (in probability_logic) unity_upper_bound:
  "Pr \<phi> \<le> 1"
  by (metis
        (no_types)
        diff_ge_0_iff_ge
        probability_non_negative
        complementation)

subsection \<open> Alternate Definition of Probability Logic \label{subsec:prob-logic-alt-def} \<close>

text \<open> There is an alternate axiomatization of logical probability,
       due to Brian Gaines @{cite \<open>pg. 159, postulates P7, P8, and P8\<close> gainesFuzzyProbabilityUncertainty1978}
       and independently formulated by Brian Weatherson @{cite weathersonClassicalIntuitionisticProbability2003}.
       As Weatherson notes, this axiomatization is suited to formulating
       \<^emph>\<open>intuitionistic\<close> probability logic. In the case where the underlying
       logic is classical this is simply equivalent to the traditional
       axiomatization in \S\ref{sec:definition-of-probability-logic}. \<close>

class weatherson_probability = classical_logic +
  fixes Pr :: "'a \<Rightarrow> real"
  assumes weatherson_thesis: "Pr \<top> = 1"
  assumes weatherson_antithesis: "Pr \<bottom> = 0"
  assumes weatherson_monotonicity: "\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> Pr \<phi> \<le> Pr \<psi>"
  assumes weatherson_sum_rule: "Pr \<phi> + Pr \<psi> = Pr (\<phi> \<sqinter> \<psi>) + Pr (\<phi> \<squnion> \<psi>)"

sublocale weatherson_probability \<subseteq> probability_logic
proof
  fix \<phi>
  have "\<turnstile> \<bottom> \<rightarrow> \<phi>"
    by (simp add: ex_falso_quodlibet)
  thus "0 \<le> Pr \<phi>"
    using weatherson_antithesis weatherson_monotonicity by fastforce
next
  fix \<phi>
  assume "\<turnstile> \<phi>"
  thus "Pr \<phi> = 1"
    by (metis
          weatherson_thesis
          weatherson_monotonicity
          eq_iff
          axiom_k
          ex_falso_quodlibet
          modus_ponens
          verum_def)
next
  fix \<phi> \<psi>
  assume "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom>"
  hence "\<turnstile> \<sim> (\<phi> \<sqinter> \<psi>)"
    by (simp add: conjunction_def negation_def)
  thus "Pr ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>) = Pr \<phi> + Pr \<psi>"
    by (metis
          add.commute
          add.right_neutral
          eq_iff
          disjunction_def
          ex_falso_quodlibet
          negation_def
          weatherson_antithesis
          weatherson_monotonicity
          weatherson_sum_rule)
qed

lemma (in probability_logic) monotonicity:
  "\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> Pr \<phi> \<le> Pr \<psi>"
proof -
  assume "\<turnstile> \<phi> \<rightarrow> \<psi>"
  hence "\<turnstile> \<sim> (\<phi> \<sqinter> \<sim> \<psi>)"
    unfolding negation_def conjunction_def
    by (metis
          conjunction_def
          exclusion_contrapositive_equivalence
          negation_def
          weak_biconditional_weaken)
  hence "Pr (\<phi> \<squnion> \<sim> \<psi>) = Pr \<phi> + Pr (\<sim> \<psi>)"
    by (simp add: probability_additivity)
  hence "Pr \<phi> + Pr (\<sim> \<psi>) \<le> 1"
    by (metis unity_upper_bound)
  hence "Pr \<phi> + 1 - Pr \<psi> \<le> 1"
    by (simp add: complementation)
  thus ?thesis by linarith
qed

lemma (in probability_logic) biconditional_equivalence:
  "\<turnstile> \<phi> \<leftrightarrow> \<psi> \<Longrightarrow> Pr \<phi> = Pr \<psi>"
  by (meson
        eq_iff
        modus_ponens
        biconditional_left_elimination
        biconditional_right_elimination
        monotonicity)

lemma (in probability_logic) sum_rule:
  "Pr (\<phi> \<squnion> \<psi>) + Pr (\<phi> \<sqinter> \<psi>) = Pr \<phi> + Pr \<psi>"
proof -
  have "\<turnstile> (\<phi> \<squnion> \<psi>) \<leftrightarrow> (\<phi> \<squnion> \<psi> \<setminus> (\<phi> \<sqinter> \<psi>))"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>))"
      unfolding
        classical_logic_class.subtraction_def
        classical_logic_class.negation_def
        classical_logic_class.biconditional_def
        classical_logic_class.conjunction_def
        classical_logic_class.disjunction_def
      by simp
    hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
      using propositional_semantics by blast
    thus ?thesis by simp
  qed
  moreover have "\<turnstile> \<phi> \<rightarrow> (\<psi> \<setminus> (\<phi> \<sqinter> \<psi>)) \<rightarrow> \<bottom>"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<rightarrow> \<bottom>"
      unfolding
        classical_logic_class.subtraction_def
        classical_logic_class.negation_def
        classical_logic_class.biconditional_def
        classical_logic_class.conjunction_def
        classical_logic_class.disjunction_def
      by simp
    hence "\<turnstile> \<^bold>\<lparr> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<rightarrow> \<bottom> \<^bold>\<rparr>"
      using propositional_semantics by blast
    thus ?thesis by simp
  qed
  hence "Pr (\<phi> \<squnion> \<psi>) = Pr \<phi> + Pr (\<psi> \<setminus> (\<phi> \<sqinter> \<psi>))"
    using
      probability_alternate_additivity
      biconditional_equivalence
      calculation
    by auto
  moreover have "\<turnstile> \<psi> \<leftrightarrow> (\<psi> \<setminus> (\<phi> \<sqinter> \<psi>) \<squnion> (\<phi> \<sqinter> \<psi>))"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>))"
      unfolding
        classical_logic_class.subtraction_def
        classical_logic_class.negation_def
        classical_logic_class.biconditional_def
        classical_logic_class.conjunction_def
        classical_logic_class.disjunction_def
      by auto
    hence "\<turnstile> \<^bold>\<lparr> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
      using propositional_semantics by
      blast
    thus ?thesis by simp
  qed
  moreover have "\<turnstile> (\<psi> \<setminus> (\<phi> \<sqinter> \<psi>)) \<rightarrow> (\<phi> \<sqinter> \<psi>) \<rightarrow> \<bottom>"
    unfolding subtraction_def negation_def conjunction_def
    using conjunction_def conjunction_right_elimination by auto
  hence "Pr \<psi> = Pr (\<psi> \<setminus> (\<phi> \<sqinter> \<psi>)) + Pr (\<phi> \<sqinter> \<psi>)"
    using
      probability_alternate_additivity
      biconditional_equivalence
      calculation
    by auto
  ultimately show ?thesis
    by simp
qed

sublocale probability_logic \<subseteq> weatherson_probability
proof
  show "Pr \<top> = 1"
    by (simp add: probability_unity)
next
  show "Pr \<bottom> = 0"
    by (metis
          add_cancel_left_right
          probability_additivity
          ex_falso_quodlibet
          probability_unity
          bivalence
          conjunction_right_elimination
          negation_def)
next
  fix \<phi> \<psi>
  assume "\<turnstile> \<phi> \<rightarrow> \<psi>"
  thus "Pr \<phi> \<le> Pr \<psi>"
    using monotonicity
    by auto
next
  fix \<phi> \<psi>
  show "Pr \<phi> + Pr \<psi> = Pr (\<phi> \<sqinter> \<psi>) + Pr (\<phi> \<squnion> \<psi>)"
    by (metis sum_rule add.commute)
qed

sublocale probability_logic \<subseteq> consistent_classical_logic
proof
  show "\<not> \<turnstile> \<bottom>" using probability_unity weatherson_antithesis by auto
qed

lemma (in probability_logic) subtraction_identity:
  "Pr (\<phi> \<setminus> \<psi>) = Pr \<phi> - Pr (\<phi> \<sqinter> \<psi>)"
proof -
  have "\<turnstile> \<phi> \<leftrightarrow> ((\<phi> \<setminus> \<psi>) \<squnion> (\<phi> \<sqinter> \<psi>))"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<setminus> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>))"
      unfolding
        classical_logic_class.subtraction_def
        classical_logic_class.negation_def
        classical_logic_class.biconditional_def
        classical_logic_class.conjunction_def
        classical_logic_class.disjunction_def
      by (simp, blast)
    hence "\<turnstile> \<^bold>\<lparr> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<setminus> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
      using propositional_semantics by blast
    thus ?thesis by simp
  qed
  hence "Pr \<phi>  = Pr ((\<phi> \<setminus> \<psi>) \<squnion> (\<phi> \<sqinter> \<psi>))"
    using biconditional_equivalence
    by simp
  moreover have "\<turnstile> \<sim>((\<phi> \<setminus> \<psi>) \<sqinter> (\<phi> \<sqinter> \<psi>))"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<sim>((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<setminus> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>))"
      unfolding
        classical_logic_class.subtraction_def
        classical_logic_class.negation_def
        classical_logic_class.conjunction_def
        classical_logic_class.disjunction_def
      by simp
    hence "\<turnstile> \<^bold>\<lparr> \<sim>((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<setminus> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
      using propositional_semantics by blast
    thus ?thesis by simp
  qed
  ultimately show ?thesis
    using probability_additivity
    by auto
qed

subsection \<open> Basic Probability Logic Inequality Results \<close>

(* TODO: Move to Suppes' theorem *)

lemma (in probability_logic) disjunction_sum_inequality:
  "Pr (\<phi> \<squnion> \<psi>) \<le> Pr \<phi> + Pr \<psi>"
proof -
  have "Pr (\<phi> \<squnion> \<psi>) + Pr (\<phi> \<sqinter> \<psi>) = Pr \<phi> + Pr \<psi>"
       "0 \<le> Pr (\<phi> \<sqinter> \<psi>)"
    by (simp add: sum_rule, simp add: probability_non_negative)
  thus ?thesis by linarith
qed

lemma (in probability_logic)
  arbitrary_disjunction_list_summation_inequality:
  "Pr (\<Squnion> \<Phi>) \<le> (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>)"
proof (induct \<Phi>)
  case Nil
  then show ?case by (simp add: weatherson_antithesis)
next
  case (Cons \<phi> \<Phi>)
  have "Pr (\<Squnion> (\<phi> # \<Phi>)) \<le> Pr \<phi> + Pr (\<Squnion> \<Phi>)"
    using disjunction_sum_inequality
    by simp
  with Cons have "Pr (\<Squnion> (\<phi> # \<Phi>)) \<le> Pr \<phi> + (\<Sum>\<phi>\<leftarrow>\<Phi>. Pr \<phi>)" by linarith
  then show ?case by simp
qed

lemma (in probability_logic) implication_list_summation_inequality:
  assumes "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
  shows "Pr \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. Pr \<psi>)"
  using
    assms
    arbitrary_disjunction_list_summation_inequality
    monotonicity
    order_trans
  by blast

lemma (in probability_logic)
  arbitrary_disjunction_set_summation_inequality:
  "Pr (\<Squnion> \<Phi>) \<le> (\<Sum>\<phi> \<in> set \<Phi>. Pr \<phi>)"
  by (metis
        arbitrary_disjunction_list_summation_inequality
        arbitrary_disjunction_remdups
        biconditional_equivalence
        sum.set_conv_list)

lemma (in probability_logic) implication_set_summation_inequality:
  assumes "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
  shows "Pr \<phi> \<le> (\<Sum>\<psi> \<in> set \<Psi>. Pr \<psi>)"
  using
    assms
    arbitrary_disjunction_set_summation_inequality
    monotonicity
    order_trans
  by blast

subsection \<open> Basic Probability Logic Inequality Results \<close>

definition (in classical_logic) logical_probabilities :: "('a \<Rightarrow> real) set"
  where "logical_probabilities =
         {Pr. class.probability_logic (\<lambda> \<phi>. \<turnstile> \<phi>) (\<rightarrow>) \<bottom> Pr }"

definition (in classical_logic) dirac_measures :: "('a \<Rightarrow> real) set"
  where "dirac_measures =
         { Pr. class.probability_logic (\<lambda> \<phi>. \<turnstile> \<phi>) (\<rightarrow>) \<bottom> Pr
               \<and> (\<forall>x. Pr x = 0 \<or> Pr x = 1) }"

lemma (in classical_logic) dirac_measures_subset:
  "dirac_measures \<subseteq> logical_probabilities"
  unfolding
    logical_probabilities_def
    dirac_measures_def
  by fastforce

lemma (in classical_logic) MCS_Dirac_measure:
  assumes "MCS \<Omega>"
    shows "(\<lambda> \<chi>. if \<chi>\<in>\<Omega> then (1 :: real) else 0) \<in> dirac_measures"
      (is "?Pr \<in> dirac_measures")
proof -
  have "class.probability_logic (\<lambda> \<phi>. \<turnstile> \<phi>) (\<rightarrow>) \<bottom> ?Pr"
  proof (standard, simp,
         meson
           assms
           formula_maximally_consistent_set_def_reflection
           maximally_consistent_set_def
           set_deduction_weaken)
    fix \<phi> \<psi>
    assume "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom>"
    hence "\<phi> \<sqinter> \<psi> \<notin> \<Omega>"
      by (metis
            assms
            formula_consistent_def
            formula_maximally_consistent_set_def_def
            maximally_consistent_set_def
            conjunction_def
            set_deduction_modus_ponens
            set_deduction_reflection
            set_deduction_weaken)
    hence "\<phi> \<notin> \<Omega> \<or> \<psi> \<notin> \<Omega>"
      using
        assms
        formula_maximally_consistent_set_def_reflection
        maximally_consistent_set_def
        conjunction_set_deduction_equivalence
      by meson

    have "\<phi> \<squnion> \<psi> \<in> \<Omega> = (\<phi> \<in> \<Omega> \<or> \<psi> \<in> \<Omega>)"
      by (metis
            \<open>\<phi> \<sqinter> \<psi> \<notin> \<Omega>\<close>
            assms
            formula_maximally_consistent_set_def_implication
            maximally_consistent_set_def
            conjunction_def
            disjunction_def)
    have "?Pr (\<phi> \<squnion> \<psi>) = ?Pr \<phi> + ?Pr \<psi>"
    proof (cases "\<phi> \<squnion> \<psi> \<in> \<Omega>")
      case True
      hence \<diamondsuit>: "1 = ?Pr (\<phi> \<squnion> \<psi>)" by simp
      show ?thesis
      proof (cases "\<phi> \<in> \<Omega>")
        case True
        hence "\<psi> \<notin> \<Omega>"
          using \<open>\<phi> \<notin> \<Omega> \<or> \<psi> \<notin> \<Omega>\<close>
          by blast
        have "?Pr (\<phi> \<squnion> \<psi>) = (1::real)" using \<diamondsuit> by simp
        also have "... = 1 + (0::real)" by linarith
        also have "... = ?Pr \<phi> + ?Pr \<psi>"
          using \<open>\<psi> \<notin> \<Omega>\<close> \<open>\<phi> \<in> \<Omega>\<close> by simp
        finally show ?thesis .
      next
        case False
        hence "\<psi> \<in> \<Omega>"
          using \<open>\<phi> \<squnion> \<psi> \<in> \<Omega>\<close> \<open>(\<phi> \<squnion> \<psi> \<in> \<Omega>) = (\<phi> \<in> \<Omega> \<or> \<psi> \<in> \<Omega>)\<close>
          by blast
        have "?Pr (\<phi> \<squnion> \<psi>) = (1::real)" using \<diamondsuit> by simp
        also have "... = (0::real) + 1" by linarith
        also have "... = ?Pr \<phi> + ?Pr \<psi>"
          using \<open>\<psi> \<in> \<Omega>\<close> \<open>\<phi> \<notin> \<Omega>\<close> by simp
        finally show ?thesis .
      qed
    next
      case False
      moreover from this have "\<phi> \<notin> \<Omega>" "\<psi> \<notin> \<Omega>"
        using \<open>(\<phi> \<squnion> \<psi> \<in> \<Omega>) = (\<phi> \<in> \<Omega> \<or> \<psi> \<in> \<Omega>)\<close> by blast+
      ultimately show ?thesis by simp
    qed
    thus "?Pr ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>) = ?Pr \<phi> + ?Pr \<psi>"
      unfolding disjunction_def .
  qed
  thus ?thesis
    unfolding dirac_measures_def
    by simp
qed

end
