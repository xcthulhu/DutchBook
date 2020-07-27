section \<open> Classical Propositional Logic \<close>

theory Classical_Propositional_Logic
  imports "../Intuitionistic/Implicational/Implicational_Intuitionistic_Logic"
begin

(*:maxLineLen=80:*)

sledgehammer_params [smt_proofs = false]

text \<open> This theory presents \<^emph>\<open>classical propositional logic\<close>, which is
        a classical logic without quantifiers. \<close>

subsection \<open> Axiomatization \<close>

text \<open> Classical propositional logic is given by the following
       Hilbert-style axiom system: \<close>

class Classical_Propositional_Logic = Minimal_Logic_With_Falsum +
  assumes Double_Negation: "\<turnstile> ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>) \<rightarrow> \<phi>"

text \<open> In some cases it is useful to assume consistency as an axiom: \<close>

class Consistent_Classical_Logic = Classical_Propositional_Logic +
  assumes consistency: "\<not> \<turnstile> \<bottom>"

subsection \<open> Common Rules \<close>

lemma (in Classical_Propositional_Logic) Ex_Falso_Quodlibet: "\<turnstile> \<bottom> \<rightarrow> \<phi>"
  using Axiom_1 Double_Negation Modus_Ponens hypothetical_syllogism
  by blast

lemma (in Classical_Propositional_Logic) Contraposition:
  "\<turnstile> ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> (\<psi> \<rightarrow> \<bottom>)) \<rightarrow> \<psi> \<rightarrow> \<phi>"
proof -
  have "[\<phi> \<rightarrow> \<bottom>, \<psi>, (\<phi> \<rightarrow> \<bottom>) \<rightarrow> (\<psi> \<rightarrow> \<bottom>)] :\<turnstile> \<bottom>"
    using flip_implication list_deduction_theorem list_implication.simps(1)
    unfolding list_deduction_def
    by presburger
  hence "[\<psi>, (\<phi> \<rightarrow> \<bottom>) \<rightarrow> (\<psi> \<rightarrow> \<bottom>)] :\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>"
    using list_deduction_theorem by blast
  hence "[\<psi>, (\<phi> \<rightarrow> \<bottom>) \<rightarrow> (\<psi> \<rightarrow> \<bottom>)] :\<turnstile> \<phi>"
    using Double_Negation list_deduction_weaken list_deduction_modus_ponens
    by blast
  thus ?thesis
    using list_deduction_base_theory list_deduction_theorem by blast
qed

lemma (in Classical_Propositional_Logic) Double_Negation_converse:
  "\<turnstile> \<phi> \<rightarrow> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>"
  by (meson Axiom_1 Modus_Ponens flip_implication)

lemma (in Classical_Propositional_Logic) The_Principle_of_Pseudo_Scotus:
  "\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<phi> \<rightarrow> \<psi>"
  using Ex_Falso_Quodlibet Modus_Ponens hypothetical_syllogism by blast

lemma (in Classical_Propositional_Logic) Peirces_law:
  "\<turnstile> ((\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>) \<rightarrow> \<phi>"
proof -
  have "[\<phi> \<rightarrow> \<bottom>, (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>] :\<turnstile> \<phi> \<rightarrow> \<psi>"
    using The_Principle_of_Pseudo_Scotus
          list_deduction_theorem
          list_deduction_weaken
    by blast
  hence "[\<phi> \<rightarrow> \<bottom>, (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>] :\<turnstile> \<phi>"
    by (meson list.set_intros(1)
              list_deduction_reflection
              list_deduction_modus_ponens
              set_subset_Cons
              subsetCE)
  hence "[\<phi> \<rightarrow> \<bottom>, (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>] :\<turnstile> \<bottom>"
    by (meson list.set_intros(1)
              list_deduction_modus_ponens
              list_deduction_reflection)
  hence "[(\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>] :\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>"
    using list_deduction_theorem by blast
  hence "[(\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>] :\<turnstile> \<phi>"
    using Double_Negation
          list_deduction_modus_ponens
          list_deduction_weaken
    by blast
  thus ?thesis
    using list_deduction_def
    by auto
qed

lemma (in Classical_Propositional_Logic) excluded_middle_elimination:
  "\<turnstile> (\<phi> \<rightarrow> \<psi>) \<rightarrow> ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>) \<rightarrow> \<psi>"
proof -
  let ?\<Gamma> = "[\<psi> \<rightarrow> \<bottom>, \<phi> \<rightarrow> \<psi>, (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>]"
  have "?\<Gamma> :\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>"
       "?\<Gamma> :\<turnstile> \<psi> \<rightarrow> \<bottom>"
    by (simp add: list_deduction_reflection)+
  hence "?\<Gamma> :\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>"
    by (meson flip_hypothetical_syllogism
              list_deduction_base_theory
              list_deduction_monotonic
              list_deduction_theorem
              set_subset_Cons)
  hence "?\<Gamma> :\<turnstile> \<phi>"
    using Double_Negation
          list_deduction_modus_ponens
          list_deduction_weaken
    by blast
  hence "?\<Gamma> :\<turnstile> \<psi>"
    by (meson list.set_intros(1)
              list_deduction_modus_ponens
              list_deduction_reflection
              set_subset_Cons subsetCE)
  hence "[\<phi> \<rightarrow> \<psi>, (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>] :\<turnstile> \<psi>"
    using Peirces_law
          list_deduction_modus_ponens
          list_deduction_theorem
          list_deduction_weaken
    by blast
  thus ?thesis
    unfolding list_deduction_def
    by simp
qed

subsection \<open> Maximally Consistent Sets For Classical Logic\<close>

definition (in Classical_Propositional_Logic)
  Consistent :: "'a set \<Rightarrow> bool" where
    [simp]: "Consistent \<Gamma> \<equiv> \<bottom>-Consistent \<Gamma>"

definition (in Classical_Propositional_Logic)
  Maximally_Consistent_Set :: "'a set \<Rightarrow> bool" ("MCS") where
    [simp]: "MCS \<Gamma> \<equiv> \<bottom>-MCS \<Gamma>"

lemma (in Classical_Propositional_Logic)
  Formula_Maximal_Consistent_Set_negation: "\<phi>-MCS \<Gamma> \<Longrightarrow> \<phi> \<rightarrow> \<bottom> \<in> \<Gamma>"
proof -
  assume "\<phi>-MCS \<Gamma>"
  {
    assume "\<phi> \<rightarrow> \<bottom> \<notin> \<Gamma>"
    hence "(\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<phi> \<in> \<Gamma>"
      using \<open>\<phi>-MCS \<Gamma>\<close>
      unfolding Formula_Maximally_Consistent_Set_def
      by blast
    hence "\<Gamma> \<tturnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<phi>"
      using set_deduction_reflection
      by simp
    hence "\<Gamma> \<tturnstile> \<phi>"
      using Peirces_law
            set_deduction_modus_ponens
            set_deduction_weaken
         by metis
    hence "False"
      using \<open>\<phi>-MCS \<Gamma>\<close>
      unfolding Formula_Maximally_Consistent_Set_def
                Formula_Consistent_def
      by simp
  }
  thus ?thesis by blast
qed

lemma (in Classical_Propositional_Logic) Formula_Maximal_Consistency:
  "(\<exists>\<phi>. \<phi>-MCS \<Gamma>) = MCS \<Gamma>"
proof -
  {
    fix \<phi>
    have "\<phi>-MCS \<Gamma> \<Longrightarrow> MCS \<Gamma>"
    proof -
      assume "\<phi>-MCS \<Gamma>"
      have "Consistent \<Gamma>"
        using \<open>\<phi>-MCS \<Gamma>\<close>
              Ex_Falso_Quodlibet [where \<phi>="\<phi>"]
              set_deduction_weaken [where \<Gamma>="\<Gamma>"]
              set_deduction_modus_ponens
        unfolding Formula_Maximally_Consistent_Set_def
                  Consistent_def
                  Formula_Consistent_def
        by metis
      moreover {
        fix \<psi>
        have "\<psi> \<rightarrow> \<bottom> \<notin> \<Gamma> \<Longrightarrow> \<psi> \<in> \<Gamma>"
        proof -
          assume "\<psi> \<rightarrow> \<bottom> \<notin> \<Gamma>"
          hence "(\<psi> \<rightarrow> \<bottom>) \<rightarrow> \<phi> \<in> \<Gamma>"
            using \<open>\<phi>-MCS \<Gamma>\<close>
            unfolding Formula_Maximally_Consistent_Set_def
            by blast
          hence "\<Gamma> \<tturnstile> (\<psi> \<rightarrow> \<bottom>) \<rightarrow> \<phi>"
            using set_deduction_reflection
            by simp
          also have "\<Gamma> \<tturnstile> \<phi> \<rightarrow> \<bottom>"
            using \<open>\<phi>-MCS \<Gamma>\<close>
                  Formula_Maximal_Consistent_Set_negation
                  set_deduction_reflection
            by simp
          hence "\<Gamma> \<tturnstile> (\<psi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>"
            using calculation
                  hypothetical_syllogism
                    [where \<phi>="\<psi> \<rightarrow> \<bottom>" and \<psi>="\<phi>" and \<chi>="\<bottom>"]
                  set_deduction_weaken
                    [where \<Gamma>="\<Gamma>"]
                  set_deduction_modus_ponens
            by metis
          hence "\<Gamma> \<tturnstile> \<psi>"
            using Double_Negation
                    [where \<phi>="\<psi>"]
                  set_deduction_weaken
                    [where \<Gamma>="\<Gamma>"]
                  set_deduction_modus_ponens
            by metis
          thus ?thesis
            using \<open>\<phi>-MCS \<Gamma>\<close>
                  Formula_Maximally_Consistent_Set_reflection
            by blast
       qed
      }
      ultimately show ?thesis
        unfolding Maximally_Consistent_Set_def
                  Formula_Maximally_Consistent_Set_def
                  Formula_Consistent_def
                  Consistent_def
        by blast
    qed
  }
  thus ?thesis
    unfolding Maximally_Consistent_Set_def
    by metis
qed

lemma (in Classical_Propositional_Logic)
  Formula_Maximally_Consistent_Set_implication:
  assumes "\<phi>-MCS \<Gamma>"
  shows "\<psi> \<rightarrow> \<chi> \<in> \<Gamma> = (\<psi> \<in> \<Gamma> \<longrightarrow> \<chi> \<in> \<Gamma>)"
proof -
  {
    assume hypothesis: "\<psi> \<in> \<Gamma> \<longrightarrow> \<chi> \<in> \<Gamma>"
    {
      assume "\<psi> \<notin> \<Gamma>"
      have "\<forall>\<psi>. \<phi> \<rightarrow> \<psi> \<in> \<Gamma>"
        by (meson assms
                  Formula_Maximal_Consistent_Set_negation
                  Formula_Maximally_Consistent_Set_implication_elimination
                  Formula_Maximally_Consistent_Set_reflection
                  The_Principle_of_Pseudo_Scotus set_deduction_weaken)
      then have "\<forall>\<chi> \<psi>. insert \<chi> \<Gamma> \<tturnstile> \<psi> \<or> \<chi> \<rightarrow> \<phi> \<notin> \<Gamma>"
        by (meson assms
                  Axiom_1
                  Formula_Maximally_Consistent_Set_reflection
                  set_deduction_modus_ponens
                  set_deduction_theorem
                  set_deduction_weaken)
      hence "\<psi> \<rightarrow> \<chi> \<in> \<Gamma>"
        by (meson \<open>\<psi> \<notin> \<Gamma>\<close>
                  assms
                  Formula_Maximally_Consistent_Set_def
                  Formula_Maximally_Consistent_Set_reflection
                  set_deduction_theorem)
    }
    moreover {
      assume "\<chi> \<in> \<Gamma>"
      hence "\<psi> \<rightarrow> \<chi> \<in> \<Gamma>"
        by (metis assms
                  calculation
                  insert_absorb
                  Formula_Maximally_Consistent_Set_reflection
                  set_deduction_theorem)
    }
    ultimately have  "\<psi> \<rightarrow> \<chi> \<in> \<Gamma>" using hypothesis by blast
  }
  thus ?thesis
    using assms
          Formula_Maximally_Consistent_Set_implication_elimination
    by metis
qed

end
