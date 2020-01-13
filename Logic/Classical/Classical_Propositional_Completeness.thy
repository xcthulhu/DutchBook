section \<open> Classical Propositional Calculus Soundness And Completeness \<close>

theory Classical_Propositional_Completeness
  imports Classical_Propositional_Logic
begin

subsection \<open> Syntax \<close>

datatype 'a Classical_Propositional_Formula =
      Falsum                                                                  ("\<^bold>\<bottom>")
    | Proposition 'a                                                          ("\<^bold>\<langle> _ \<^bold>\<rangle>" [45])
    | Implication "'a Classical_Propositional_Formula"
                  "'a Classical_Propositional_Formula"                          (infixr "\<^bold>\<rightarrow>" 70)

subsection \<open> Propositional Calculus \<close>

named_theorems Classical_Propositional_Calculus "Rules for the Propositional Calculus"

inductive Classical_Propositional_Calculus ::
  "'a Classical_Propositional_Formula \<Rightarrow> bool"                                  ("\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p _" [60] 55)
  where
       Axiom_1 [Classical_Propositional_Calculus]: "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<^bold>\<rightarrow> \<psi> \<^bold>\<rightarrow> \<phi>"
    |  Axiom_2 [Classical_Propositional_Calculus]: "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<phi> \<^bold>\<rightarrow> \<psi> \<^bold>\<rightarrow> \<chi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> \<phi> \<^bold>\<rightarrow> \<chi>"
    |  Double_Negation [Classical_Propositional_Calculus]: "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ((\<phi> \<^bold>\<rightarrow> \<^bold>\<bottom>) \<^bold>\<rightarrow> \<^bold>\<bottom>) \<^bold>\<rightarrow> \<phi>"
    |  Modus_Ponens [Classical_Propositional_Calculus]: "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<^bold>\<rightarrow> \<psi> \<Longrightarrow> \<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<Longrightarrow> \<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<psi>"

instantiation Classical_Propositional_Formula :: (type) Classical_Propositional_Logic
begin
definition [simp]: "\<bottom> = \<^bold>\<bottom>"
definition [simp]: "\<turnstile> \<phi> = \<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
definition [simp]: "\<phi> \<rightarrow> \<psi> = \<phi> \<^bold>\<rightarrow> \<psi>"
instance by standard (simp add: Classical_Propositional_Calculus)+
end

subsection \<open> Propositional Semantics \<close>

primrec Classical_Propositional_Semantics ::
  "'a set \<Rightarrow> 'a Classical_Propositional_Formula \<Rightarrow> bool"
  (infix "\<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p" 65)
  where
       "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p Proposition p = (p \<in> \<MM>)"
    |  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<^bold>\<rightarrow> \<psi> = (\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<longrightarrow> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<psi>)"
    |  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<^bold>\<bottom> = False"

theorem Classical_Propositional_Calculus_Soundness:
  "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<Longrightarrow> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
  by (induct rule: Classical_Propositional_Calculus.induct, simp+)

subsection \<open> Propositional Soundness and Completeness \<close>

definition Strong_Classical_Propositional_Deduction ::
  "'a Classical_Propositional_Formula set \<Rightarrow> 'a Classical_Propositional_Formula \<Rightarrow> bool"
  (infix "\<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p" 65)
  where
    [simp]: "\<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<equiv> \<Gamma> \<tturnstile> \<phi>"

definition Strong_Classical_Propositional_Models ::
  "'a Classical_Propositional_Formula set \<Rightarrow> 'a Classical_Propositional_Formula \<Rightarrow> bool"
  (infix "\<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p" 65)
  where
    [simp]: "\<Gamma> \<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<equiv> \<forall> \<MM>.(\<forall> \<gamma> \<in> \<Gamma>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<gamma>) \<longrightarrow> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"

definition Theory_Propositions ::
  "'a Classical_Propositional_Formula set \<Rightarrow> 'a set"                            ("\<^bold>\<lbrace> _ \<^bold>\<rbrace>" [50])
  where
    [simp]: "\<^bold>\<lbrace> \<Gamma> \<^bold>\<rbrace> = {p . \<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p Proposition p}"

lemma Truth_Lemma:
  assumes "MCS \<Gamma>"
  shows "\<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<equiv> \<^bold>\<lbrace> \<Gamma> \<^bold>\<rbrace> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
proof (induct \<phi>)
  case Falsum
  then show ?case using assms by auto
next
  case (Proposition x)
  then show ?case by simp
next
  case (Implication \<psi> \<chi>)
  thus ?case
    unfolding Strong_Classical_Propositional_Deduction_def
    by (metis assms
              Maximally_Consistent_Set_def
              Formula_Maximally_Consistent_Set_implication
              Classical_Propositional_Semantics.simps(2)
              implication_Classical_Propositional_Formula_def
              set_deduction_modus_ponens
              set_deduction_reflection)
qed

theorem Classical_Propositional_Calculus_Strong_Soundness_And_Completeness:
  "\<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<equiv> \<Gamma> \<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
proof -
  have soundness: "\<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<Longrightarrow> \<Gamma> \<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
  proof -
    assume "\<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
    from this obtain \<Gamma>' where \<Gamma>': "set \<Gamma>' \<subseteq> \<Gamma>" "\<Gamma>' :\<turnstile> \<phi>" by (simp add: set_deduction_def, blast)
    {
      fix \<MM>
      assume "\<forall> \<gamma> \<in> \<Gamma>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<gamma>"
      hence "\<forall> \<gamma> \<in> set \<Gamma>'. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<gamma>" using \<Gamma>'(1) by auto
      hence "\<forall> \<phi>. \<Gamma>' :\<turnstile> \<phi> \<longrightarrow> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
      proof (induct \<Gamma>')
        case Nil
        then show ?case
          by (simp add: Classical_Propositional_Calculus_Soundness
                        list_deduction_def)
      next
        case (Cons \<psi> \<Gamma>')
        thus ?case using list_deduction_theorem by fastforce
      qed
      with \<Gamma>'(2) have "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>" by blast
    }
    thus "\<Gamma> \<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
      using Strong_Classical_Propositional_Models_def by blast
  qed
  have completeness: "\<Gamma> \<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<Longrightarrow> \<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
  proof (erule contrapos_pp)
    assume "~ \<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
    hence "\<exists> \<MM>. (\<forall> \<gamma> \<in> \<Gamma>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<gamma>) \<and> ~ \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
    proof -
      from \<open>~ \<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>\<close> obtain \<Omega> where \<Omega>: "\<Gamma> \<subseteq> \<Omega>" "\<phi>-MCS \<Omega>"
        by (meson Formula_Consistent_def
                  Formula_Maximally_Consistent_Extension
                  Strong_Classical_Propositional_Deduction_def)
      hence "(\<phi> \<rightarrow> \<bottom>) \<in> \<Omega>"
        using Formula_Maximal_Consistent_Set_negation by blast
      hence "~ \<^bold>\<lbrace> \<Omega> \<^bold>\<rbrace> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
        using \<Omega>
              Formula_Consistent_def
              Formula_Maximal_Consistency
              Formula_Maximally_Consistent_Set_def
              Truth_Lemma
        unfolding Strong_Classical_Propositional_Deduction_def
        by blast
      moreover have "\<forall> \<gamma> \<in> \<Gamma>. \<^bold>\<lbrace> \<Omega> \<^bold>\<rbrace> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<gamma>"
        using Formula_Maximal_Consistency Truth_Lemma \<Omega> set_deduction_reflection
        unfolding Strong_Classical_Propositional_Deduction_def
        by blast
      ultimately show ?thesis by auto
    qed
    thus "~ \<Gamma> \<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
      unfolding Strong_Classical_Propositional_Models_def
      by simp
  qed
  from soundness completeness show "\<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<equiv> \<Gamma> \<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
    by linarith
qed

theorem Classical_Propositional_Calculus_Soundness_And_Completeness:
  "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> = (\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>)"
  using Classical_Propositional_Calculus_Soundness [where \<phi>="\<phi>"]
        Classical_Propositional_Calculus_Strong_Soundness_And_Completeness [where \<phi>="\<phi>"
                                                                              and \<Gamma>="{}"]
        Strong_Classical_Propositional_Deduction_def [where \<phi>="\<phi>" and \<Gamma>="{}"]
        Strong_Classical_Propositional_Models_def [where \<phi>="\<phi>" and \<Gamma>="{}"]
        deduction_Classical_Propositional_Formula_def [where \<phi>="\<phi>"]
        set_deduction_base_theory [where \<phi>="\<phi>"]
  by metis

instantiation Classical_Propositional_Formula :: (type) Consistent_Classical_Logic
begin
instance by standard (simp add: Classical_Propositional_Calculus_Soundness_And_Completeness)
end

primrec (in Classical_Propositional_Logic) Classical_Propositional_Formula_embedding
                           :: "'a Classical_Propositional_Formula \<Rightarrow> 'a" ("\<^bold>\<lparr> _ \<^bold>\<rparr>" [50]) where
     "\<^bold>\<lparr> \<^bold>\<langle> p \<^bold>\<rangle> \<^bold>\<rparr> = p"
   | "\<^bold>\<lparr> \<phi> \<^bold>\<rightarrow> \<psi> \<^bold>\<rparr> = \<^bold>\<lparr> \<phi> \<^bold>\<rparr> \<rightarrow> \<^bold>\<lparr> \<psi> \<^bold>\<rparr>"
   | "\<^bold>\<lparr> \<^bold>\<bottom> \<^bold>\<rparr> = \<bottom>"

theorem (in Classical_Propositional_Logic) propositional_calculus:
  "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<Longrightarrow> \<turnstile> \<^bold>\<lparr> \<phi> \<^bold>\<rparr>"
  by (induct rule: Classical_Propositional_Calculus.induct,
      (simp add: Axiom_1 Axiom_2 Double_Negation Modus_Ponens)+)

theorem (in Classical_Propositional_Logic) propositional_semantics:
  "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<Longrightarrow> \<turnstile> \<^bold>\<lparr> \<phi> \<^bold>\<rparr>"
  by (simp add: Classical_Propositional_Calculus_Soundness_And_Completeness propositional_calculus)

end
