section \<open>The Untyped \<lambda>-Calculus With de Bruijn Indices\<close>

(*:maxLineLen=80:*)

theory DeBruijn
  imports Main
begin

declare [[syntax_ambiguity_warning = false]]

subsection \<open>Grammar\<close>

datatype dB =
    Variable    nat   ("\<langle>_\<rangle>" [100] 100)
  | Application dB dB (infixl "\<cdot>" 200)
  | Abstraction dB    ("\<^bold>\<lambda>")

subsection \<open>Substitution\<close>

primrec
  lift :: "dB \<Rightarrow> nat \<Rightarrow> dB"
where
    "lift (\<langle>i\<rangle>) k = (if i < k then \<langle>i\<rangle> else \<langle>(i + 1)\<rangle>)"
  | "lift (s \<cdot> t) k = lift s k \<cdot> lift t k"
  | "lift (\<^bold>\<lambda> s) k = \<^bold>\<lambda> (lift s (k + 1))"

primrec
  subst :: "dB \<Rightarrow> nat \<Rightarrow> dB \<Rightarrow> dB"  ("_[_ '\<^bold>\<mapsto> _]" [300, 0, 0] 300)
  where
    subst_Var: "(\<langle>i\<rangle>)[k \<^bold>\<mapsto> s] =
      (if k < i then \<langle>(i - 1)\<rangle> else if i = k then s else \<langle>i\<rangle>)"
  | subst_App: "(t \<cdot> u)[k \<^bold>\<mapsto> s] = t[k \<^bold>\<mapsto> s] \<cdot> u[k \<^bold>\<mapsto> s]"
  | subst_Abs: "(\<^bold>\<lambda> t)[k \<^bold>\<mapsto> s] = \<^bold>\<lambda> (t [k + 1 \<^bold>\<mapsto> lift s 0])"

declare subst_Var [simp del]
declare if_not_P [simp] not_less_eq [simp]

subsection \<open>Derived Substitution Rules\<close>

lemma subst_eq [simp]: "(\<langle>k\<rangle>)[k \<^bold>\<mapsto> u] = u"
  by (simp add: subst_Var)

lemma subst_gt [simp]: "i < j \<Longrightarrow> (\<langle>j\<rangle>)[i \<^bold>\<mapsto> u] = \<langle>(j - 1)\<rangle>"
  by (simp add: subst_Var)

lemma subst_lt [simp]: "j < i \<Longrightarrow> (\<langle>j\<rangle>)[i \<^bold>\<mapsto> u] = \<langle>j\<rangle>"
  by (simp add: subst_Var)

lemma lift_lift:
    "i < k + 1 \<Longrightarrow> lift (lift t i) (Suc k) = lift (lift t k) i"
  by (induct t arbitrary: i k) auto

lemma lift_subst [simp]:
    "j < i + 1 \<Longrightarrow> lift (t[j \<^bold>\<mapsto> s]) i = (lift t (i + 1))[j \<^bold>\<mapsto> lift s i]"
  by (induct t arbitrary: i j s)
    (simp_all add: diff_Suc subst_Var lift_lift split: nat.split)

lemma lift_subst_lt:
    "i < j + 1 \<Longrightarrow> lift (t[j \<^bold>\<mapsto> s]) i = (lift t i)[j+1 \<^bold>\<mapsto> lift s i]"
  by (induct t arbitrary: i j s) (simp_all add: subst_Var lift_lift)

lemma subst_lift [simp]:
    "(lift t k)[k \<^bold>\<mapsto> s] = t"
  by (induct t arbitrary: k s) simp_all

lemma subst_subst:
    "i < j + 1 \<Longrightarrow> t[j+1 \<^bold>\<mapsto> lift v i][i \<^bold>\<mapsto> u[j \<^bold>\<mapsto> v]] = t[i \<^bold>\<mapsto> u][j \<^bold>\<mapsto> v]"
  by (induct t arbitrary: i j u v)
    (simp_all 
      add: diff_Suc subst_Var lift_lift [symmetric] lift_subst_lt
      split: nat.split)

subsection \<open>Small Step \<beta>-Reduction\<close>

inductive beta :: "dB \<Rightarrow> dB \<Rightarrow> bool"  (infixl "\<rightarrow>\<^sub>\<beta>" 50)
  where
    beta [simp, intro!]: "\<^bold>\<lambda> s \<cdot> t \<rightarrow>\<^sub>\<beta> s[0 \<^bold>\<mapsto> t]"
  | appL [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> s \<cdot> u \<rightarrow>\<^sub>\<beta> t \<cdot> u"
  | appR [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> u \<cdot> s \<rightarrow>\<^sub>\<beta> u \<cdot> t"
  | abs [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> \<^bold>\<lambda> s \<rightarrow>\<^sub>\<beta> \<^bold>\<lambda> t"

inductive_cases beta_cases [elim!]:
  "Var i \<rightarrow>\<^sub>\<beta> t"
  "\<^bold>\<lambda> r \<rightarrow>\<^sub>\<beta> s"
  "s \<cdot> t \<rightarrow>\<^sub>\<beta> u"

subsection \<open>Derived Small Step \<beta>-Reduction Rules\<close>

theorem lift_preserves_beta [simp]:
    "r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> lift r i \<rightarrow>\<^sub>\<beta> lift s i"
  by (induct arbitrary: i set: beta) auto

theorem subst_preserves_beta [simp, intro!]:
    "r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> r[i \<^bold>\<mapsto> t] \<rightarrow>\<^sub>\<beta> s[i \<^bold>\<mapsto> t]"
  by (induct arbitrary: t i set: beta)
     (simp_all add: subst_subst [symmetric])

subsection \<open>Transitive \<beta>-Reduction\<close>

abbreviation
  beta_reds :: "dB \<Rightarrow> dB \<Rightarrow> bool"  (infixl "\<rightarrow>\<^sub>\<beta>\<^sup>*" 50) where
  "s \<rightarrow>\<^sub>\<beta>\<^sup>* t == beta\<^sup>*\<^sup>* s t"

subsection \<open>Transitive \<beta>-Reduction Rules\<close>

lemma rtrancl_beta_Abs [intro!]:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<Longrightarrow> \<^bold>\<lambda> s \<rightarrow>\<^sub>\<beta>\<^sup>* \<^bold>\<lambda> s'"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_AppL:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<Longrightarrow> s \<cdot> t \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<cdot> t"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_AppR:
    "t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> s \<cdot> t \<rightarrow>\<^sub>\<beta>\<^sup>* s \<cdot> t'"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_App [intro]:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<Longrightarrow> t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> s \<cdot> t \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<cdot> t'"
  by (blast intro!: rtrancl_beta_AppL rtrancl_beta_AppR intro: rtranclp_trans)

theorem rtancl_lift_preserves_beta: 
    "r \<rightarrow>\<^sub>\<beta>\<^sup>* s \<Longrightarrow> lift r i \<rightarrow>\<^sub>\<beta>\<^sup>* lift s i"
  by (induct rule: rtranclp.induct,
      blast, 
      simp add: rtranclp.rtrancl_into_rtrancl)

theorem rtrancl_subst_preserves_beta: 
    "r \<rightarrow>\<^sub>\<beta>\<^sup>* s \<Longrightarrow> r[i \<^bold>\<mapsto> t] \<rightarrow>\<^sub>\<beta>\<^sup>* s[i \<^bold>\<mapsto> t]"
  by (induct rule: rtranclp.induct, 
      blast, 
      meson rtranclp.simps subst_preserves_beta)

theorem rtancl_subst_preserves_beta_inner: 
    "r \<rightarrow>\<^sub>\<beta>\<^sup>* s \<Longrightarrow> t[i \<^bold>\<mapsto> r] \<rightarrow>\<^sub>\<beta>\<^sup>* t[i \<^bold>\<mapsto> s]"
proof -
  {
    fix r s t
    have "r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> t[i \<^bold>\<mapsto> r] \<rightarrow>\<^sub>\<beta>\<^sup>* t[i \<^bold>\<mapsto> s]"
      by (induct t arbitrary: r s i,
          simp add: subst_Var r_into_rtranclp,
          simp add: rtrancl_beta_App, 
          simp add: rtrancl_beta_Abs)
  } note \<dagger> = this
  show "r \<rightarrow>\<^sub>\<beta>\<^sup>* s \<Longrightarrow> t[i \<^bold>\<mapsto> r] \<rightarrow>\<^sub>\<beta>\<^sup>* t[i \<^bold>\<mapsto> s]"
    by (induct rule: rtranclp.induct, 
        blast,
        metis \<dagger> rtranclp.rtrancl_into_rtrancl rtranclp_idemp)
qed

end
