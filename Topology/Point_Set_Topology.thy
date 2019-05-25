theory Point_Set_Topology
  imports Main
begin

sledgehammer_params [smt_proofs = false]

named_theorems point_set_continuous_intros "structural introduction rules for continuity"

(* TODO: Cite Munkres *)

class \<Omega> =
  fixes \<Omega> :: "'a set"

class \<tau> =
  fixes \<tau> :: "'a set set"

class point_set_topology = \<Omega> + \<tau> +
  assumes space_subset_relative_universe: "\<tau> \<subseteq> Pow \<Omega>"
  assumes relative_universe_topological_membership [simp, intro]: "\<Omega> \<in> \<tau>"
  assumes Int_topological_closure [intro]: "S \<in> \<tau> \<Longrightarrow> T \<in> \<tau> \<Longrightarrow> S \<inter> T \<in> \<tau>"
  assumes Union_topological_closure [intro]: "K \<subseteq> \<tau> \<Longrightarrow> (\<Union> K) \<in> \<tau>"

begin

definition "open" :: "'a set \<Rightarrow> bool"
  where "open S \<longleftrightarrow> S \<in> \<tau>"

lemma open_relative_universe [simp, intro]: "open \<Omega>"
  unfolding open_def
  by fastforce

lemma open_Int [intro]: "open S \<Longrightarrow> open T \<Longrightarrow> open (S \<inter> T)"
  unfolding open_def
  by fastforce

lemma open_Union [intro]: "\<forall>S\<in>K. open S \<Longrightarrow> open (\<Union>K)"
  unfolding open_def
  by blast

lemma open_empty [point_set_continuous_intros, intro, simp]: "open {}"
  using open_Union [of "{}"] by simp

lemma open_Un [point_set_continuous_intros, intro]: "open S \<Longrightarrow> open T \<Longrightarrow> open (S \<union> T)"
  using open_Union [of "{S, T}"] by simp

lemma open_UN [point_set_continuous_intros, intro]: "\<forall>x\<in>A. open (B x) \<Longrightarrow> open (\<Union>x\<in>A. B x)"
  using open_Union [of "B ` A"] by simp

lemma open_Inter [point_set_continuous_intros, intro]: 
  "finite S \<Longrightarrow> \<forall>T\<in>S. open T \<Longrightarrow> open (\<Omega> \<inter> \<Inter> S)"
  by (induct set: finite, simp, simp add: inf_left_commute open_Int)

lemma open_INT [point_set_continuous_intros, intro]:
  "finite A \<Longrightarrow> \<forall>x\<in>A. open (B x) \<Longrightarrow> open (\<Omega> \<inter> (\<Inter>x\<in> A. B x))"
  using open_Inter [of "B ` A"] by simp

lemma openI:
  assumes "\<And>x. x \<in> S \<Longrightarrow> \<exists>T. open T \<and> x \<in> T \<and> T \<subseteq> S"
  shows "open S"
proof -
  have "open (\<Union>{T. open T \<and> T \<subseteq> S})" by auto
  moreover have "\<Union>{T. open T \<and> T \<subseteq> S} = S" by (auto dest!: assms)
  ultimately show "open S" by simp
qed

definition closed :: "'a set \<Rightarrow> bool"
  where "closed S \<longleftrightarrow> S \<subseteq> \<Omega> \<and> open (\<Omega> - S)"

lemma closed_empty [point_set_continuous_intros, intro, simp]: "closed {}"
  unfolding closed_def by auto 

lemma closed_Un [point_set_continuous_intros, intro]: "closed S \<Longrightarrow> closed T \<Longrightarrow> closed (S \<union> T)"
  unfolding closed_def
  by (simp add: Diff_Un open_Int)

lemma closed_relative_universe [point_set_continuous_intros, intro, simp]: "closed \<Omega>"
  unfolding closed_def
  by simp

lemma closed_Int [point_set_continuous_intros, intro]: 
  "closed S \<Longrightarrow> closed T \<Longrightarrow> closed (S \<inter> T)"
  unfolding closed_def by (simp add: Diff_Int inf.coboundedI1 open_Un)

lemma closed_INT [point_set_continuous_intros, intro]: 
  "\<forall>x\<in>A. closed (B x) \<Longrightarrow> closed (\<Omega> \<inter> (\<Inter> x\<in>A. B x))"
  unfolding closed_def
  by (metis (no_types, lifting) Diff_Int 
                                Diff_cancel 
                                IntE 
                                UN_simps(7) 
                                inf_commute 
                                open_UN 
                                subsetI 
                                sup_bot.comm_neutral)

lemma closed_Inter [point_set_continuous_intros, intro]: "\<forall>S\<in>K. closed S \<Longrightarrow> closed (\<Omega> \<inter> \<Inter> K)"
  using closed_INT [where ?B="\<lambda> x. x"]
  by auto

lemma closed_Union [point_set_continuous_intros, intro]: 
  "finite S \<Longrightarrow> \<forall>T\<in>S. closed T \<Longrightarrow> closed (\<Union>S)"
  by (induct set: finite) auto

lemma closed_UN [point_set_continuous_intros, intro]:
  "finite A \<Longrightarrow> \<forall>x\<in>A. closed (B x) \<Longrightarrow> closed (\<Union>x\<in>A. B x)"
  using closed_Union [of "B ` A"] by simp

lemma open_closed: "open S \<longleftrightarrow> S \<subseteq> \<Omega> \<and> closed (\<Omega> - S)"
proof
  assume "open S"
  hence "S \<subseteq> \<Omega>"
    unfolding open_def
    using space_subset_relative_universe
    by blast
  hence "\<Omega> - S \<subseteq> \<Omega>" "\<Omega> - (\<Omega> - S) = S"
    by auto
  with \<open>open S\<close> \<open>S \<subseteq> \<Omega>\<close> show "S \<subseteq> \<Omega> \<and> closed (\<Omega> - S)"
    unfolding closed_def
    by auto
next
  assume "S \<subseteq> \<Omega> \<and> closed (\<Omega> - S)"
  hence "\<Omega> - (\<Omega> - S) = S" "closed (\<Omega> - S)"
    by blast+
  thus "open S"
    unfolding closed_def
    by simp
qed

lemma closed_open: "closed S \<longleftrightarrow> S \<subseteq> \<Omega> \<and> open (\<Omega> - S)"
  by (rule closed_def)

lemma open_Diff [point_set_continuous_intros, intro]: "open S \<Longrightarrow> closed T \<Longrightarrow> open (S - T)"
  by (metis Int_Diff Int_absorb2 closed_open open_Int open_closed)
  
lemma closed_Diff [point_set_continuous_intros, intro]: "closed S \<Longrightarrow> open T \<Longrightarrow> closed (S - T)"
  by (metis Int_Diff Int_absorb2 closed_Int closed_open open_closed)

lemma open_Compl [point_set_continuous_intros, intro]: "closed S \<Longrightarrow> open (\<Omega> - S)"
  by blast

lemma closed_Compl [point_set_continuous_intros, intro]: "open S \<Longrightarrow> closed (\<Omega> - S)"
  by blast

lemma open_Collect_neg: "closed {x. P x} \<Longrightarrow> open {x \<in> \<Omega>. \<not> P x}"
proof -
  assume "closed {x. P x}"
  hence "closed {x \<in> \<Omega>. P x}"
    by (simp add: Collect_conj_eq closed_Int)
  hence "open (\<Omega> - {x \<in> \<Omega>. P x})" "\<Omega> - {x \<in> \<Omega>. P x} = {x \<in> \<Omega>. \<not> P x}"
    unfolding closed_def
    by blast+
  thus "open {x \<in> \<Omega>. \<not> P x}" by auto
qed

lemma closed_Collect_neg: "open {x. P x} \<Longrightarrow> closed {x \<in> \<Omega>. \<not> P x}"
proof -
  assume "open {x. P x}"
  hence "open {x \<in> \<Omega>. P x}"
    by (simp add: Collect_conj_eq open_Int)
  hence "closed (\<Omega> - {x \<in> \<Omega>. P x})" "\<Omega> - {x \<in> \<Omega>. P x} = {x \<in> \<Omega>. \<not> P x}"
    unfolding open_closed
    by blast+
  thus "closed {x \<in> \<Omega>. \<not> P x}" by auto
qed

lemma open_Collect_neg_eq:
  "open {x \<in> \<Omega>. P x} \<longleftrightarrow> closed {x \<in> \<Omega>. \<not> P x}"
proof
  assume "open {x \<in> \<Omega>. P x}"
  hence "open {x. x \<in> \<Omega> \<and> P x}"
    by auto
  hence "closed {x \<in> \<Omega>. \<not> x \<in> \<Omega> \<or> \<not> P x}"
    using closed_Collect_neg by force
  thus "closed {x \<in> \<Omega>. \<not> P x}"
    by (metis (mono_tags, lifting) Collect_cong)
next
  assume "closed {x \<in> \<Omega>. \<not> P x}"
  hence "closed {x. x \<in> \<Omega> \<and> \<not> P x}"
    by auto
  hence "open {x \<in> \<Omega>. \<not> x \<in> \<Omega> \<or> P x}"
    using open_Collect_neg by force
  thus "open {x \<in> \<Omega>. P x}"
    by (metis (mono_tags, lifting) Collect_cong)
qed

lemma open_Collect_conj:
  assumes "open {x. P x}" "open {x. Q x}"
  shows "open {x. P x \<and> Q x}"
  using open_Int[OF assms] by (simp add: Int_def)

lemma open_Collect_disj:
  assumes "open {x. P x}" "open {x. Q x}"
  shows "open {x. P x \<or> Q x}"
  using open_Un[OF assms] by (simp add: Un_def)

lemma open_Collect_ex: "(\<And>i. open {x. P i x}) \<Longrightarrow> open {x. \<exists>i. P i x}"
  using open_UN[of UNIV "\<lambda>i. {x. P i x}"] unfolding Collect_ex_eq by simp

lemma weakend_open_Collect_ex: 
  assumes "\<And>i. open {x \<in> \<Omega>. P i x}"
  shows "open {x \<in> \<Omega>. \<exists>i. P i x}"
proof -
  have "open {x. \<exists>i. x \<in> \<Omega> \<and> P i x}"
    using assms open_Collect_ex [where ?P="\<lambda> i x. x \<in> \<Omega> \<and> P i x"]
    by blast
  moreover have "{x. \<exists>i. x \<in> \<Omega> \<and> P i x} = {x \<in> \<Omega>. \<exists>i. P i x}"
    by blast
  ultimately show ?thesis by simp
qed

lemma open_Collect_imp: 
  assumes "open {x. \<not> P x}" "open {x. Q x}"
  shows "open {x. P x \<longrightarrow> Q x}"
proof -
  from assms have "open {x. \<not> P x \<or> Q x}"
    using open_Collect_disj by blast
  thus ?thesis
    by linarith
qed    

lemma open_Collect_const: "open {x \<in> \<Omega>. P}"
  by (cases P) auto

lemma closed_Collect_conj:
  assumes "closed {x. P x}" "closed {x. Q x}"
  shows "closed {x. P x \<and> Q x}"
  using closed_Int[OF assms] by (simp add: Int_def)

lemma closed_Collect_disj:
  assumes "closed {x. P x}" "closed {x. Q x}"
  shows "closed {x. P x \<or> Q x}"
  using closed_Un[OF assms] by (simp add: Un_def)

lemma closed_Collect_imp: "closed {x. \<not> P x} \<Longrightarrow> closed {x. Q x} \<Longrightarrow> closed {x. P x \<longrightarrow> Q x}"
  unfolding imp_conv_disj
  using closed_Collect_disj
  by blast

lemma closed_Collect_all:
  assumes "\<And>i. closed {x. P i x}"
  shows "closed {x . \<forall>i. P i x}"
proof -
  from assms have "\<forall>i . {x. P i x} = {x \<in> \<Omega>. P i x}"
    unfolding closed_def
    by blast
  with assms have "\<And>i. closed {x \<in> \<Omega>. P i x}"
    by simp
  hence "\<And>i. open {x \<in> \<Omega>. \<not> P i x}"
    by (simp add: assms open_Collect_neg)
  hence "closed {x \<in> \<Omega>. \<forall> i. P i x}"
    using weakend_open_Collect_ex [where ?P="\<lambda> i x. \<not> P i x"]
          open_Collect_neg_eq
    by fastforce
  moreover from assms have "{x \<in> \<Omega>. \<forall> i. P i x} = {x . \<forall> i. P i x}"
    unfolding closed_def
    by blast
  ultimately show ?thesis by auto
qed

lemma weakend_closed_Collect_all:
  assumes "\<And>i. closed {x \<in> \<Omega>. P i x}"
  shows "closed {x \<in> \<Omega>. \<forall>i. P i x}"
proof -
  from assms have "closed {x . \<forall>i. x \<in> \<Omega> \<and> P i x}"
    using closed_Collect_all [where ?P="\<lambda> i x. x \<in> \<Omega> \<and> P i x"]
    by blast
  moreover have "{x . \<forall>i. x \<in> \<Omega> \<and> P i x} = {x \<in> \<Omega> . \<forall>i. P i x}"
    by auto
  ultimately show ?thesis by simp
qed
    
lemma closed_Collect_const: "closed {x \<in> \<Omega>. P}"
  by (cases P) auto

end

class t0_topology = point_set_topology +
  assumes t0_topology: "x \<in> \<Omega> \<Longrightarrow> y \<in> \<Omega> \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<exists>U \<in> \<tau>. \<not> (x \<in> U \<longleftrightarrow> y \<in> U)"

lemma (in t0_topology) t0_space:
  "x \<in> \<Omega> \<Longrightarrow> y \<in> \<Omega> \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<exists>U. open U \<and> \<not> (x \<in> U \<longleftrightarrow> y \<in> U)"
  unfolding open_def
  using t0_topology by auto

class t1_topology = point_set_topology +
  assumes t1_topology: "x \<in> \<Omega> \<Longrightarrow> y \<in> \<Omega> \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<exists>U \<in> \<tau>. x \<in> U \<and> y \<notin> U"

instance t1_topology \<subseteq> t0_topology
  by standard (metis t1_topology)

context t1_topology begin

lemma t1_space: "x \<in> \<Omega> \<Longrightarrow> y \<in> \<Omega> \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<exists>U. open U \<and> x \<in> U \<and> y \<notin> U"
  by (meson open_def t1_topology)

lemma separation_t1: "x \<in> \<Omega> \<Longrightarrow> y \<in> \<Omega> \<Longrightarrow> x \<noteq> y \<longleftrightarrow> (\<exists>U. open U \<and> x \<in> U \<and> y \<notin> U)"
  using t1_space[of x y] by blast

lemma closed_singleton: 
  assumes "a \<in> \<Omega>" 
  shows "closed {a}"
proof -
  let ?T = "\<Union>{S. open S \<and> a \<notin> S}"
  have "open ?T"
    by (simp add: open_Union)
  moreover have "?T = \<Omega> - {a}"
    using t1_space 
    by (auto, fastforce simp add: open_closed)
  ultimately show ?thesis
    using \<open>a \<in> \<Omega>\<close>
    unfolding closed_def
    by auto
qed

lemma closed_insert [point_set_continuous_intros, simp]:
  assumes "a \<in> \<Omega>"
      and "closed S" 
    shows "closed (insert a S)"
proof -
  from closed_singleton assms have "closed ({a} \<union> S)"
    by blast
  then show "closed (insert a S)"
    by simp
qed

lemma finite_imp_closed: 
  assumes "finite S"
      and "S \<subseteq> \<Omega>"
    shows "closed S"
  using assms
  by (induct pred: finite) simp_all

end

text \<open>T2 spaces are also known as Hausdorff spaces.\<close>

class t2_topology = point_set_topology +
  assumes hausdorff: 
    "x \<in> \<Omega> \<Longrightarrow> y \<in> \<Omega> \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<exists>U V. U \<in> \<tau> \<and> V \<in> \<tau> \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"

instance t2_topology \<subseteq> t1_topology
  by standard (metis IntI empty_iff hausdorff)
  
lemma (in t2_topology) separation_t2:
  assumes "x \<in> \<Omega>"
      and "y \<in> \<Omega>"
    shows "x \<noteq> y \<longleftrightarrow> (\<exists>U V. U \<in> \<tau> \<and> V \<in> \<tau> \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {})"
  using assms hausdorff [of x y]
  by blast

lemma (in t0_topology) separation_t0:
  assumes "x \<in> \<Omega>"
      and "y \<in> \<Omega>"
    shows "x \<noteq> y \<longleftrightarrow> (\<exists>U \<in> \<tau>. \<not> (x \<in> U \<longleftrightarrow> y \<in> U))"
  using assms t0_topology [of x y]
  by blast

text \<open>A classical separation axiom for topological space, the T3 axiom -- also called regularity:
if a point is not in a closed set, then there are open sets separating them.\<close>

class t3_topology = t2_topology +
  assumes t3_topology: 
    "y \<in> \<Omega> \<Longrightarrow>
     S \<subseteq> \<Omega> \<Longrightarrow>
     \<Omega> - S \<in> \<tau> \<Longrightarrow>
     y \<notin> S \<Longrightarrow>
     \<exists>U V. U \<in> \<tau> \<and> V \<in> \<tau> \<and> y \<in> U \<and> S \<subseteq> V \<and> U \<inter> V = {}"

text \<open>A classical separation axiom for topological space, the T4 axiom -- also called normality:
if two closed sets are disjoint, then there are open sets separating them.\<close>

class t4_topology = t2_topology +
  assumes t4_topology:
    "S \<subseteq> \<Omega> \<Longrightarrow>
     T \<subseteq> \<Omega> \<Longrightarrow>
     \<Omega> - S \<in> \<tau> \<Longrightarrow>
     \<Omega> - T \<in> \<tau> \<Longrightarrow>
     S \<inter> T = {} \<Longrightarrow>
     \<exists>U V. U \<in> \<tau> \<and> V \<in> \<tau> \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> U \<inter> V = {}"

text \<open>T4 is stronger than T3, and weaker than metric.\<close>

instance t4_topology \<subseteq> t3_topology
proof
  fix S and y::'a assume "y \<in> \<Omega>" "S \<subseteq> \<Omega>" "\<Omega> - S \<in> \<tau>" "y \<notin> S"
  then show "\<exists>U V. U \<in> \<tau> \<and> V \<in> \<tau> \<and> y \<in> U \<and> S \<subseteq> V \<and> U \<inter> V = {}"
    using t4_topology[of "{y}" S]
    by (metis (no_types, lifting)
              Diff_disjoint 
              Diff_insert_absorb
              closed_empty
              closed_insert
              closed_open
              open_def
              singletonI subsetCE) 
qed

text \<open>A perfect space is a topological space with no isolated points.\<close>

class perfect_topology = point_set_topology +
  assumes not_open_singleton: "x \<in> \<Omega> \<Longrightarrow> {x} \<notin> \<tau>"

lemma (in perfect_topology) UNIV_not_singleton: "\<Omega> \<noteq> {x}"
  for x::'a
  using not_open_singleton
        relative_universe_topological_membership
  by blast


subsection \<open>Generators for toplogies\<close>

inductive generate_topology :: "'a set set \<Rightarrow> 'a set \<Rightarrow> bool" for S :: "'a set set"
  where
    Int: "generate_topology S a \<Longrightarrow> generate_topology S b \<Longrightarrow> generate_topology S (a \<inter> b)"
  | UN: "generate_topology S (\<Union>K)" if "(\<And>k. k \<in> K \<Longrightarrow> generate_topology S k)"
  | Basis: "generate_topology S s" if "s \<in> S"

hide_fact (open) Int UN Basis

lemma generate_topology_Union:
  "(\<And>k. k \<in> I \<Longrightarrow> generate_topology S (K k)) \<Longrightarrow> generate_topology S (\<Union>k\<in>I. K k)"
  using generate_topology.UN [of "K ` I"] by auto

lemma generate_topology_\<Omega>: "generate_topology S (\<Union>S)"
  by (simp add: generate_topology.Basis generate_topology.UN)

lemma generate_topology_Collect_Pow:
  "Collect (generate_topology S) \<subseteq> Pow (\<Union>S)"
proof -
  {
    fix x
    assume "generate_topology S x"
    hence "x \<in> Pow (\<Union>S)"
      by (induct x, blast+)
  }
  thus ?thesis
    by blast
qed

lemma topological_space_generate_topology: 
  "class.point_set_topology (\<Union>S) (Collect (generate_topology S))"
  by (standard, 
      simp add: generate_topology_Collect_Pow,
      simp add: generate_topology_\<Omega>,
      simp add: generate_topology.Int,
      metis Ball_Collect generate_topology.UN mem_Collect_eq)

subsection \<open>Order topologies\<close>

class order_topology = order + \<Omega> + \<tau> +
  assumes open_generated_order: 
    "\<tau> = Collect (generate_topology (range (\<lambda>a. {..< a}) \<union> range (\<lambda>a. {a <..})))"
  assumes \<Omega>_union_\<tau>: "\<Omega> = \<Union>\<tau>"
begin

subclass point_set_topology
  unfolding open_generated_order \<Omega>_union_\<tau>
  by (standard, 
      blast, 
      force intro: generate_topology.UN, 
      simp add: generate_topology.Int, 
      metis Ball_Collect CollectI generate_topology.UN)

lemma open_greaterThan [point_set_continuous_intros, simp]: "open {a <..}"
  unfolding open_generated_order
  by (metis CollectI 
            IntD2 
            generate_topology.Basis 
            inf_sup_absorb 
            open_def 
            open_generated_order 
            range_eqI
            sup_commute)

lemma open_lessThan [point_set_continuous_intros, simp]: "open {..< a}"
  unfolding open_generated_order
  by (metis (no_types, lifting) 
            Un_def
            generate_topology.Basis
            open_def
            open_generated_order
            mem_Collect_eq rangeI)

lemma open_greaterThanLessThan [point_set_continuous_intros, simp]: "open {a <..< b}"
   unfolding greaterThanLessThan_eq by (simp add: open_Int)
end

class nonempty_topology = point_set_topology +
  assumes nonempty_\<Omega>: "\<Omega> \<noteq> {}"

class linorder_topology = linorder + order_topology + nonempty_topology

begin

lemma \<Omega>_UNIV: "\<Omega> = UNIV"
proof -
  from nonempty_\<Omega> obtain a S where "a \<in> \<Omega>" "S \<in> \<tau>" "a \<in> S"
    by blast
  have "UNIV = {..< a} \<union> S \<union> {a <..}"
    using UnI1 \<open>a \<in> S\<close> not_less_iff_gr_or_eq by auto
  thus ?thesis
    by (metis UNIV_I UNIV_eq_I UnionI \<Omega>_union_\<tau>
              \<open>S \<in> \<tau>\<close> open_Un open_def 
              open_greaterThan open_lessThan)
qed

lemma open_closed: "open S = closed (- S)"
  by (metis Compl_eq_Diff_UNIV \<Omega>_UNIV double_compl closed_Compl open_Compl)

lemma closed_open: "closed S = open (- S)"
  by (simp add: open_closed)

end

lemma closed_atMost [point_set_continuous_intros, simp]: "closed {..a}"
  for a :: "'a::linorder_topology"
  by (simp add: closed_open)

lemma closed_atLeast [point_set_continuous_intros, simp]: "closed {a..}"
  for a :: "'a::linorder_topology"
  by (simp add: closed_open)

lemma closed_atLeastAtMost [point_set_continuous_intros, simp]: "closed {a..b}"
  for a b :: "'a::linorder_topology"
proof -
  have "{a .. b} = {a ..} \<inter> {.. b}"
    by auto
  then show ?thesis
    by (simp add: closed_Int)
qed

lemma (in linorder) less_separate:
  assumes "x < y"
  shows "\<exists>a b. x \<in> {..< a} \<and> y \<in> {b <..} \<and> {..< a} \<inter> {b <..} = {}"
proof (cases "\<exists>z. x < z \<and> z < y")
  case True
  then obtain z where "x < z \<and> z < y" ..
  then have "x \<in> {..< z} \<and> y \<in> {z <..} \<and> {z <..} \<inter> {..< z} = {}"
    by auto
  then show ?thesis by blast
next
  case False
  with \<open>x < y\<close> have "x \<in> {..< y}" "y \<in> {x <..}" "{x <..} \<inter> {..< y} = {}"
    by auto
  then show ?thesis by blast
qed

instance linorder_topology \<subseteq> t2_topology
proof
  fix x y :: 'a
  show "    x \<in> \<Omega> 
        \<Longrightarrow> y \<in> \<Omega> 
        \<Longrightarrow> x \<noteq> y 
        \<Longrightarrow> \<exists>U V. U \<in> \<tau> \<and> V \<in> \<tau> \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"
    using less_separate [of x y] less_separate [of y x]
    by (metis inf_commute linorder_cases open_def open_greaterThan open_lessThan)
qed

lemma (in linorder_topology) open_right:
  assumes "open S" "x \<in> S"
      and gt_ex: "x < y"
    shows "\<exists>b>x. {x ..< b} \<subseteq> S"
    using assms unfolding open_generated_order
proof -
  from \<open>open S\<close> 
  have "generate_topology (range (\<lambda>a. {..< a}) \<union> range (\<lambda>a. {a <..})) S"


end