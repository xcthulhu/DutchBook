(*:maxLineLen=80:*)

section \<open> Classical Logic Connectives \label{sec:logical-connectives}\<close>

theory Classical_Connectives
  imports Classical_Logic_Completeness
          "../../Utilities/List_Utilities"
begin

sledgehammer_params [smt_proofs = false]

subsection \<open> Verum \<close>

definition (in Classical_Logic) verum :: "'a" ("\<top>")
  where
    "\<top> = \<bottom> \<rightarrow> \<bottom>"

lemma (in Classical_Logic) verum_tautology [simp]: "\<turnstile> \<top>"
  by (metis list_implication.simps(1) list_implication_Axiom_K verum_def)

lemma verum_semantics [simp]:
  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<top>"
  unfolding verum_def by simp

lemma (in Classical_Logic) verum_embedding [simp]:
  "\<^bold>\<lparr> \<top> \<^bold>\<rparr> = \<top>"
  by (simp add: Classical_Logic_class.verum_def verum_def)
  

subsection \<open> Conjunction \<close>

definition (in Classical_Logic) 
  conjunction :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<sqinter>" 67)
  where
    "\<phi> \<sqinter> \<psi> = (\<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>"

primrec (in Classical_Logic) 
  Arbitrary_Conjunction :: "'a list \<Rightarrow> 'a" ("\<Sqinter>")
  where
     "\<Sqinter> [] = \<top>"
  |  "\<Sqinter> (\<phi> # \<Phi>) = \<phi> \<sqinter> \<Sqinter> \<Phi>"

lemma (in Classical_Logic) conjunction_introduction:
  "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> (\<phi> \<sqinter> \<psi>)"
  by (metis 
        Modus_Ponens
        conjunction_def
        list_flip_implication1
        list_implication.simps(1)
        list_implication.simps(2))

lemma (in Classical_Logic) conjunction_left_elimination:
  "\<turnstile> (\<phi> \<sqinter> \<psi>) \<rightarrow> \<phi>"
  by (metis (full_types) 
        Peirces_law
        The_Principle_of_Pseudo_Scotus
        conjunction_def
        list_deduction_base_theory
        list_deduction_modus_ponens
        list_deduction_theorem
        list_deduction_weaken)

lemma (in Classical_Logic) conjunction_right_elimination:
  "\<turnstile> (\<phi> \<sqinter> \<psi>) \<rightarrow> \<psi>"
  by (metis (full_types) Axiom_K
                         Contraposition
                         Modus_Ponens
                         conjunction_def
                         flip_hypothetical_syllogism
                         flip_implication)

lemma (in Classical_Logic) conjunction_embedding [simp]:
  "\<^bold>\<lparr> \<phi> \<sqinter> \<psi> \<^bold>\<rparr> = \<^bold>\<lparr> \<phi> \<^bold>\<rparr> \<sqinter> \<^bold>\<lparr> \<psi> \<^bold>\<rparr>"
  unfolding conjunction_def Classical_Logic_class.conjunction_def
  by simp

lemma conjunction_semantics [simp]:
  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<sqinter> \<psi> = (\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<and> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<psi>)"
  unfolding conjunction_def by simp

subsection \<open> Biconditional \<close>

definition (in Classical_Logic) biconditional :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixr "\<leftrightarrow>" 75)
  where
    "\<phi> \<leftrightarrow> \<psi> = (\<phi> \<rightarrow> \<psi>) \<sqinter> (\<psi> \<rightarrow> \<phi>)"

lemma (in Classical_Logic) biconditional_introduction:
  "\<turnstile> (\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<psi> \<rightarrow> \<phi>) \<rightarrow> (\<phi> \<leftrightarrow> \<psi>)"
  by (simp add: biconditional_def conjunction_introduction)

lemma (in Classical_Logic) biconditional_left_elimination:
  "\<turnstile> (\<phi> \<leftrightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<psi>"
  by (simp add: biconditional_def conjunction_left_elimination)

lemma (in Classical_Logic) biconditional_right_elimination:
  "\<turnstile> (\<phi> \<leftrightarrow> \<psi>) \<rightarrow> \<psi> \<rightarrow> \<phi>"
  by (simp add: biconditional_def conjunction_right_elimination)

lemma (in Classical_Logic) biconditional_embedding [simp]:
  "\<^bold>\<lparr> \<phi> \<leftrightarrow> \<psi> \<^bold>\<rparr> = \<^bold>\<lparr> \<phi> \<^bold>\<rparr> \<leftrightarrow> \<^bold>\<lparr> \<psi> \<^bold>\<rparr>"
  unfolding biconditional_def Classical_Logic_class.biconditional_def
  by simp

lemma biconditional_semantics [simp]:
  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<leftrightarrow> \<psi> = (\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<longleftrightarrow> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<psi>)"
  unfolding biconditional_def
  by (simp, blast)

subsection \<open> Negation \<close>

definition (in Classical_Logic) negation :: "'a \<Rightarrow> 'a"  ("\<sim>")
  where
    "\<sim> \<phi> = \<phi> \<rightarrow> \<bottom>"

lemma (in Classical_Logic) negation_introduction:
  "\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<sim> \<phi>"
  unfolding negation_def
  by (metis Axiom_K Modus_Ponens implication_absorption)

lemma (in Classical_Logic) negation_elimination:
  "\<turnstile> \<sim> \<phi> \<rightarrow> (\<phi> \<rightarrow> \<bottom>)"
  unfolding negation_def
  by (metis Axiom_K Modus_Ponens implication_absorption)

lemma (in Classical_Logic) negation_embedding [simp]:
  "\<^bold>\<lparr> \<sim> \<phi> \<^bold>\<rparr> = \<sim> \<^bold>\<lparr> \<phi> \<^bold>\<rparr>"
  by (simp add: 
        Classical_Logic_class.negation_def 
        negation_def)

lemma negation_semantics [simp]:
  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<sim> \<phi> = (\<not> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>)"
  unfolding negation_def
  by simp

subsection \<open> Disjunction \<close>

definition (in Classical_Logic) disjunction :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixr "\<squnion>" 67)
  where
    "\<phi> \<squnion> \<psi> = (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>"

primrec (in Classical_Logic) Arbitrary_Disjunction :: "'a list \<Rightarrow> 'a" ("\<Squnion>")
  where
     "\<Squnion> [] = \<bottom>"
  |  "\<Squnion> (\<phi> # \<Phi>) = \<phi> \<squnion> \<Squnion> \<Phi>"

lemma (in Classical_Logic) disjunction_elimination:
  "\<turnstile> (\<phi> \<rightarrow> \<chi>) \<rightarrow> (\<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<squnion> \<psi>) \<rightarrow> \<chi>"
proof -
  let ?\<Gamma> = "[\<phi> \<rightarrow> \<chi>, \<psi> \<rightarrow> \<chi>, \<phi> \<squnion> \<psi>]"
  have "?\<Gamma> :\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<chi>"
    unfolding disjunction_def
    by (metis hypothetical_syllogism
              list_deduction_def
              list_implication.simps(1)
              list_implication.simps(2)
              set_deduction_base_theory
              set_deduction_theorem
              set_deduction_weaken)
  hence "?\<Gamma> :\<turnstile> \<chi>"
    using excluded_middle_elimination
          list_deduction_modus_ponens
          list_deduction_theorem
          list_deduction_weaken
    by blast
  thus ?thesis
    unfolding list_deduction_def
    by simp
qed

lemma (in Classical_Logic) disjunction_left_introduction:
  "\<turnstile> \<phi> \<rightarrow> (\<phi> \<squnion> \<psi>)"
  unfolding disjunction_def
  by (metis Modus_Ponens
            The_Principle_of_Pseudo_Scotus
            flip_implication)

lemma (in Classical_Logic) disjunction_right_introduction:
  "\<turnstile> \<psi> \<rightarrow> (\<phi> \<squnion> \<psi>)"
  unfolding disjunction_def
  using Axiom_K
  by simp

lemma (in Classical_Logic) disjunction_embedding [simp]:
  "\<^bold>\<lparr> \<phi> \<squnion> \<psi> \<^bold>\<rparr> = \<^bold>\<lparr> \<phi> \<^bold>\<rparr> \<squnion> \<^bold>\<lparr> \<psi> \<^bold>\<rparr>"
  unfolding disjunction_def Classical_Logic_class.disjunction_def
  by simp

lemma disjunction_semantics [simp]:
  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<squnion> \<psi> = (\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<or> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<psi>)"
  unfolding disjunction_def
  by (simp, blast)

subsection \<open> Mutual Exclusion \<close>

primrec (in Classical_Logic) exclusive :: "'a list \<Rightarrow> 'a" ("\<Coprod>")
  where
      "\<Coprod> [] = \<top>"
    | "\<Coprod> (\<phi> # \<Phi>) = \<sim> (\<phi> \<sqinter> \<Squnion> \<Phi>) \<sqinter> \<Coprod> \<Phi>"

subsection \<open> Subtraction \<close>

definition (in Classical_Logic) subtraction :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixl "\<setminus>" 69)
  where
    "\<phi> \<setminus> \<psi> = \<phi> \<sqinter> \<sim> \<psi>"

lemma (in Classical_Logic) subtraction_embedding [simp]:
  "\<^bold>\<lparr> \<phi> \<setminus> \<psi> \<^bold>\<rparr> = \<^bold>\<lparr> \<phi> \<^bold>\<rparr> \<setminus> \<^bold>\<lparr> \<psi> \<^bold>\<rparr>"
  unfolding subtraction_def Classical_Logic_class.subtraction_def
  by simp

subsection \<open> Common Rules \<close>

subsubsection \<open> Biconditional Equivalence Relation \<close>

lemma (in Classical_Logic) biconditional_reflection:
  "\<turnstile> \<phi> \<leftrightarrow> \<phi>"
  by (meson Axiom_K Modus_Ponens biconditional_introduction implication_absorption)

lemma (in Classical_Logic) biconditional_symmetry:
  "\<turnstile> (\<phi> \<leftrightarrow> \<psi>) \<leftrightarrow> (\<psi> \<leftrightarrow> \<phi>)"
  by (metis (full_types) Modus_Ponens
                         biconditional_def
                         conjunction_def
                         flip_hypothetical_syllogism
                         flip_implication)

lemma (in Classical_Logic) biconditional_symmetry_rule:
  "\<turnstile> \<phi> \<leftrightarrow> \<psi> \<Longrightarrow> \<turnstile> \<psi> \<leftrightarrow> \<phi>"
  by (meson Modus_Ponens
            biconditional_introduction
            biconditional_left_elimination
            biconditional_right_elimination)

lemma (in Classical_Logic) biconditional_transitivity:
    "\<turnstile> (\<phi> \<leftrightarrow> \<psi>) \<rightarrow> (\<psi> \<leftrightarrow> \<chi>) \<rightarrow> (\<phi> \<leftrightarrow> \<chi>)"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)"
    by simp
  hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<^bold>\<rparr>"
    using propositional_semantics by blast
 thus ?thesis by simp
qed

lemma (in Classical_Logic) biconditional_transitivity_rule:
  "\<turnstile> \<phi> \<leftrightarrow> \<psi> \<Longrightarrow> \<turnstile> \<psi> \<leftrightarrow> \<chi> \<Longrightarrow> \<turnstile> \<phi> \<leftrightarrow> \<chi>"
  using Modus_Ponens biconditional_transitivity by blast

subsubsection \<open> Biconditional Weakening \<close>

lemma (in Classical_Logic) biconditional_weaken:
  assumes "\<Gamma> \<tturnstile> \<phi> \<leftrightarrow> \<psi>"
  shows "\<Gamma> \<tturnstile> \<phi> = \<Gamma> \<tturnstile> \<psi>"
  by (metis assms
            biconditional_left_elimination
            biconditional_right_elimination
            set_deduction_modus_ponens
            set_deduction_weaken)

lemma (in Classical_Logic) list_biconditional_weaken:
  assumes "\<Gamma> :\<turnstile> \<phi> \<leftrightarrow> \<psi>"
  shows "\<Gamma> :\<turnstile> \<phi> = \<Gamma> :\<turnstile> \<psi>"
  by (metis assms
            biconditional_left_elimination
            biconditional_right_elimination
            list_deduction_modus_ponens
            list_deduction_weaken)

lemma (in Classical_Logic) weak_biconditional_weaken:
  assumes "\<turnstile> \<phi> \<leftrightarrow> \<psi>"
  shows "\<turnstile> \<phi> = \<turnstile> \<psi>"
  by (metis assms
            biconditional_left_elimination
            biconditional_right_elimination
            Modus_Ponens)

subsubsection \<open> Conjunction Identities \<close>

lemma (in Classical_Logic) conjunction_negation_identity:
  "\<turnstile> \<sim> (\<phi> \<sqinter> \<psi>) \<leftrightarrow> (\<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom>)"
  by (metis Contraposition
            Double_Negation_converse
            Modus_Ponens
            biconditional_introduction
            conjunction_def
            negation_def)

lemma (in Classical_Logic) conjunction_set_deduction_equivalence [simp]:
  "\<Gamma> \<tturnstile> \<phi> \<sqinter> \<psi> = (\<Gamma> \<tturnstile> \<phi> \<and> \<Gamma> \<tturnstile> \<psi>)"
  by (metis set_deduction_weaken [where \<Gamma>="\<Gamma>"]
            set_deduction_modus_ponens [where \<Gamma>="\<Gamma>"]
            conjunction_introduction
            conjunction_left_elimination
            conjunction_right_elimination)

lemma (in Classical_Logic) conjunction_list_deduction_equivalence [simp]:
  "\<Gamma> :\<turnstile> \<phi> \<sqinter> \<psi> = (\<Gamma> :\<turnstile> \<phi> \<and> \<Gamma> :\<turnstile> \<psi>)"
  by (metis list_deduction_weaken [where \<Gamma>="\<Gamma>"]
            list_deduction_modus_ponens [where \<Gamma>="\<Gamma>"]
            conjunction_introduction
            conjunction_left_elimination
            conjunction_right_elimination)

lemma (in Classical_Logic) weak_conjunction_deduction_equivalence [simp]:
  "\<turnstile> \<phi> \<sqinter> \<psi> = (\<turnstile> \<phi> \<and> \<turnstile> \<psi>)"
  by (metis conjunction_set_deduction_equivalence set_deduction_base_theory)

lemma (in Classical_Logic) conjunction_set_deduction_arbitrary_equivalence [simp]:
  "\<Gamma> \<tturnstile> \<Sqinter> \<Phi> = (\<forall> \<phi> \<in> set \<Phi>. \<Gamma> \<tturnstile> \<phi>)"
  by (induct \<Phi>, simp add: set_deduction_weaken, simp)

lemma (in Classical_Logic) conjunction_list_deduction_arbitrary_equivalence [simp]:
  "\<Gamma> :\<turnstile> \<Sqinter> \<Phi> = (\<forall> \<phi> \<in> set \<Phi>. \<Gamma> :\<turnstile> \<phi>)"
  by (induct \<Phi>, simp add: list_deduction_weaken, simp)

lemma (in Classical_Logic) weak_conjunction_deduction_arbitrary_equivalence [simp]:
  "\<turnstile> \<Sqinter> \<Phi> = (\<forall> \<phi> \<in> set \<Phi>. \<turnstile> \<phi>)"
  by (induct \<Phi>, simp+)

lemma (in Classical_Logic) conjunction_commutativity:
  "\<turnstile> (\<psi> \<sqinter> \<phi>) \<leftrightarrow> (\<phi> \<sqinter> \<psi>)"
  by (metis (full_types) Modus_Ponens
                         biconditional_introduction
                         conjunction_def
                         flip_hypothetical_syllogism
                         flip_implication)

lemma (in Classical_Logic) conjunction_associativity:
  "\<turnstile> ((\<phi> \<sqinter> \<psi>) \<sqinter> \<chi>) \<leftrightarrow> (\<phi> \<sqinter> (\<psi> \<sqinter> \<chi>))"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>))"
    by simp
  hence "\<turnstile> \<^bold>\<lparr> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
    using propositional_semantics by blast
  thus ?thesis by simp
qed

lemma (in Classical_Logic) arbitrary_conjunction_antitone:
  "set \<Phi> \<subseteq> set \<Psi> \<Longrightarrow> \<turnstile> \<Sqinter> \<Psi> \<rightarrow> \<Sqinter> \<Phi>"
proof -
  have "\<forall> \<Phi>. set \<Phi> \<subseteq> set \<Psi> \<longrightarrow> \<turnstile> \<Sqinter> \<Psi> \<rightarrow> \<Sqinter> \<Phi>"
  proof (induct \<Psi>)
    case Nil
    then show ?case
      by (simp add: The_Principle_of_Pseudo_Scotus verum_def)
  next
    case (Cons \<psi> \<Psi>)
    {
      fix \<Phi>
      assume "set \<Phi> \<subseteq> set (\<psi> # \<Psi>)"
      have "\<turnstile> \<Sqinter> (\<psi> # \<Psi>) \<rightarrow> \<Sqinter> \<Phi>"
      proof (cases "\<psi> \<in> set \<Phi>")
        assume "\<psi> \<in> set \<Phi>"
                have "\<forall> \<phi> \<in> set \<Phi>. \<turnstile> \<Sqinter> \<Phi> \<leftrightarrow> (\<phi> \<sqinter> \<Sqinter> (removeAll \<phi> \<Phi>))"
        proof (induct \<Phi>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<chi> \<Phi>)
          {
            fix \<phi>
            assume "\<phi> \<in> set (\<chi> # \<Phi>)"
            have "\<turnstile> \<Sqinter> (\<chi> # \<Phi>) \<leftrightarrow> (\<phi> \<sqinter> \<Sqinter> (removeAll \<phi> (\<chi> # \<Phi>)))"
            proof cases
              assume "\<phi> \<in> set \<Phi>"
              hence "\<turnstile> \<Sqinter> \<Phi> \<leftrightarrow> (\<phi> \<sqinter> \<Sqinter> (removeAll \<phi> \<Phi>))"
                using Cons.hyps \<open>\<phi> \<in> set \<Phi>\<close>
                by auto
              moreover
              have "\<turnstile> (\<Sqinter> \<Phi> \<leftrightarrow> (\<phi> \<sqinter> \<Sqinter> (removeAll \<phi> \<Phi>))) \<rightarrow>
                      (\<chi> \<sqinter> \<Sqinter> \<Phi>) \<leftrightarrow> (\<phi> \<sqinter> \<chi> \<sqinter> \<Sqinter> (removeAll \<phi> \<Phi>))"
              proof -
                have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<Sqinter> \<Phi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> (removeAll \<phi> \<Phi>)\<^bold>\<rangle>)) \<rightarrow>
                                     (\<^bold>\<langle>\<chi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> \<Phi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> (removeAll \<phi> \<Phi>)\<^bold>\<rangle>)"
                    by auto
                hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<Sqinter> \<Phi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> (removeAll \<phi> \<Phi>)\<^bold>\<rangle>)) \<rightarrow>
                           (\<^bold>\<langle>\<chi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> \<Phi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> (removeAll \<phi> \<Phi>)\<^bold>\<rangle>) \<^bold>\<rparr>"
                  using propositional_semantics by blast
                thus ?thesis by simp
              qed
              ultimately have "\<turnstile> \<Sqinter> (\<chi> # \<Phi>) \<leftrightarrow> (\<phi> \<sqinter> \<chi> \<sqinter> \<Sqinter> (removeAll \<phi> \<Phi>))"
                using Modus_Ponens by auto
              show ?thesis
              proof cases
                assume "\<phi> = \<chi>"
                moreover
                {
                  fix \<phi>
                  have "\<turnstile> (\<chi> \<sqinter> \<phi>) \<rightarrow> (\<chi> \<sqinter> \<chi> \<sqinter> \<phi>)"
                    unfolding conjunction_def
                    by (meson Axiom_S
                              Double_Negation
                              Modus_Ponens
                              flip_hypothetical_syllogism
                              flip_implication)
                } note tautology = this
                from \<open>\<turnstile> \<Sqinter> (\<chi> # \<Phi>) \<leftrightarrow> (\<phi> \<sqinter> \<chi> \<sqinter> \<Sqinter> (removeAll \<phi> \<Phi>))\<close>
                     \<open>\<phi> = \<chi>\<close>
                have "\<turnstile> (\<chi> \<sqinter> \<Sqinter> (removeAll \<chi> \<Phi>)) \<rightarrow> (\<chi> \<sqinter> \<Sqinter> \<Phi>)"
                  unfolding biconditional_def
                  by (simp, metis tautology hypothetical_syllogism Modus_Ponens)
                moreover
                from \<open>\<turnstile> \<Sqinter> (\<chi> # \<Phi>) \<leftrightarrow> (\<phi> \<sqinter> \<chi> \<sqinter> \<Sqinter> (removeAll \<phi> \<Phi>))\<close>
                     \<open>\<phi> = \<chi>\<close>
                have "\<turnstile> (\<chi> \<sqinter> \<Sqinter> \<Phi>) \<rightarrow> (\<chi> \<sqinter> \<Sqinter> (removeAll \<chi> \<Phi>))"
                  unfolding biconditional_def
                  by (simp,
                      metis conjunction_right_elimination
                            hypothetical_syllogism
                            Modus_Ponens)
                ultimately show ?thesis
                  unfolding biconditional_def
                  by simp
              next
                assume "\<phi> \<noteq> \<chi>"
                then show ?thesis
                  using \<open>\<turnstile> \<Sqinter> (\<chi> # \<Phi>) \<leftrightarrow> (\<phi> \<sqinter> \<chi> \<sqinter> \<Sqinter> (removeAll \<phi> \<Phi>))\<close>
                  by simp
              qed
            next
              assume "\<phi> \<notin> set \<Phi>"
              hence "\<phi> = \<chi>" "\<chi> \<notin> set \<Phi>"
                using \<open>\<phi> \<in> set (\<chi> # \<Phi>)\<close> by auto
              then show ?thesis
                using biconditional_reflection
                by simp
            qed
          }
          thus ?case by blast
        qed
        hence "\<turnstile> (\<psi> \<sqinter> \<Sqinter> (removeAll \<psi> \<Phi>)) \<rightarrow> \<Sqinter> \<Phi>"
          using Modus_Ponens biconditional_right_elimination \<open>\<psi> \<in> set \<Phi>\<close>
          by blast
        moreover
        from \<open>\<psi> \<in> set \<Phi>\<close> \<open>set \<Phi> \<subseteq> set (\<psi> # \<Psi>)\<close> Cons.hyps
        have "\<turnstile> \<Sqinter> \<Psi> \<rightarrow> \<Sqinter> (removeAll \<psi> \<Phi>)"
          by (simp add: subset_insert_iff insert_absorb)
        hence "\<turnstile> \<Sqinter> (\<psi> # \<Psi>) \<rightarrow> (\<psi> \<sqinter> \<Sqinter> (removeAll \<psi> \<Phi>))"
          apply simp
          unfolding conjunction_def
          using Modus_Ponens hypothetical_syllogism flip_hypothetical_syllogism
          by meson
        ultimately show ?thesis
          apply simp
          using Modus_Ponens hypothetical_syllogism
          by blast
      next
        assume "\<psi> \<notin> set \<Phi>"
        hence "\<turnstile> \<Sqinter> \<Psi> \<rightarrow> \<Sqinter> \<Phi>"
          using Cons.hyps \<open>set \<Phi> \<subseteq> set (\<psi> # \<Psi>)\<close>
          by auto
        then show ?thesis
          apply simp
          unfolding conjunction_def
          by (metis Modus_Ponens
                    conjunction_def
                    conjunction_right_elimination
                    hypothetical_syllogism)
      qed
    }
    thus ?case by blast
  qed
  thus "set \<Phi> \<subseteq> set \<Psi> \<Longrightarrow> \<turnstile> \<Sqinter> \<Psi> \<rightarrow> \<Sqinter> \<Phi>" by blast
qed

lemma (in Classical_Logic) arbitrary_conjunction_remdups:
  "\<turnstile> (\<Sqinter> \<Phi>) \<leftrightarrow> \<Sqinter> (remdups \<Phi>)"
  by (simp add: arbitrary_conjunction_antitone biconditional_def)

lemma (in Classical_Logic) curry_uncurry:
  "\<turnstile> (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<leftrightarrow> ((\<phi> \<sqinter> \<psi>) \<rightarrow> \<chi>)"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)"
      by auto
  hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<^bold>\<rparr>"
    using propositional_semantics by blast
  thus ?thesis by simp
qed

lemma (in Classical_Logic) list_curry_uncurry:
  "\<turnstile> (\<Phi> :\<rightarrow> \<chi>) \<leftrightarrow> (\<Sqinter> \<Phi> \<rightarrow> \<chi>)"
proof (induct \<Phi>)
  case Nil
  have "\<turnstile> \<chi> \<leftrightarrow> (\<top> \<rightarrow> \<chi>)"
    unfolding biconditional_def
              conjunction_def
              verum_def
    using 
      Axiom_K
      Ex_Falso_Quodlibet
      Modus_Ponens
      conjunction_def
      excluded_middle_elimination
      set_deduction_base_theory
      conjunction_set_deduction_equivalence
    by metis
  with Nil show ?case
    by simp
next
  case (Cons \<phi> \<Phi>)
  have "\<turnstile> ((\<phi> # \<Phi>) :\<rightarrow> \<chi>) \<leftrightarrow> (\<phi> \<rightarrow> (\<Phi> :\<rightarrow> \<chi>))"
    by (simp add: biconditional_reflection)
  with Cons have "\<turnstile> ((\<phi> # \<Phi>) :\<rightarrow> \<chi>) \<leftrightarrow> (\<phi> \<rightarrow> \<Sqinter> \<Phi> \<rightarrow> \<chi>)"
    by (metis Modus_Ponens
              biconditional_def
              hypothetical_syllogism
              list_implication.simps(2)
              weak_conjunction_deduction_equivalence)
  with curry_uncurry [where ?\<phi>="\<phi>"
                        and ?\<psi>="\<Sqinter> \<Phi>"
                        and ?\<chi>="\<chi>"]
  show ?case
    unfolding biconditional_def
    by (simp, metis Modus_Ponens hypothetical_syllogism)
qed

subsubsection \<open> Disjunction Identities \<close>

lemma (in Classical_Logic) bivalence:
  "\<turnstile> \<sim> \<phi> \<squnion> \<phi>"
  by (simp add: Double_Negation disjunction_def negation_def)

lemma (in Classical_Logic) implication_equivalence:
  "\<turnstile> (\<sim> \<phi> \<squnion> \<psi>) \<leftrightarrow> (\<phi> \<rightarrow> \<psi>)"
  by (metis Double_Negation_converse
            Modus_Ponens
            biconditional_introduction
            bivalence
            disjunction_def
            flip_hypothetical_syllogism
            negation_def)

lemma (in Classical_Logic) disjunction_commutativity:
  "\<turnstile> (\<psi> \<squnion> \<phi>) \<leftrightarrow> (\<phi> \<squnion> \<psi>)"
  by (meson Modus_Ponens
            biconditional_introduction
            disjunction_elimination
            disjunction_left_introduction
            disjunction_right_introduction)

lemma (in Classical_Logic) disjunction_associativity:
  "\<turnstile> ((\<phi> \<squnion> \<psi>) \<squnion> \<chi>) \<leftrightarrow> (\<phi> \<squnion> (\<psi> \<squnion> \<chi>))"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>))"
    by simp
  hence "\<turnstile> \<^bold>\<lparr> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
    using propositional_semantics by blast
  thus ?thesis by simp
qed

lemma (in Classical_Logic) arbitrary_disjunction_monotone:
  "set \<Phi> \<subseteq> set \<Psi> \<Longrightarrow> \<turnstile> \<Squnion> \<Phi> \<rightarrow> \<Squnion> \<Psi>"
proof -
  have "\<forall> \<Phi>. set \<Phi> \<subseteq> set \<Psi> \<longrightarrow> \<turnstile> \<Squnion> \<Phi> \<rightarrow> \<Squnion> \<Psi>"
  proof (induct \<Psi>)
    case Nil
    then show ?case using verum_def verum_tautology by auto
  next
    case (Cons \<psi> \<Psi>)
    {
      fix \<Phi>
      assume "set \<Phi> \<subseteq> set (\<psi> # \<Psi>)"
      have "\<turnstile> \<Squnion> \<Phi> \<rightarrow> \<Squnion> (\<psi> # \<Psi>)"
      proof cases
        assume "\<psi> \<in> set \<Phi>"
        have "\<forall> \<phi> \<in> set \<Phi>. \<turnstile> \<Squnion> \<Phi> \<leftrightarrow> (\<phi> \<squnion> \<Squnion> (removeAll \<phi> \<Phi>))"
        proof (induct \<Phi>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<chi> \<Phi>)
          {
            fix \<phi>
            assume "\<phi> \<in> set (\<chi> # \<Phi>)"
            have "\<turnstile> \<Squnion> (\<chi> # \<Phi>) \<leftrightarrow> (\<phi> \<squnion> \<Squnion> (removeAll \<phi> (\<chi> # \<Phi>)))"
            proof cases
              assume "\<phi> \<in> set \<Phi>"
              hence "\<turnstile> \<Squnion> \<Phi> \<leftrightarrow> (\<phi> \<squnion> \<Squnion> (removeAll \<phi> \<Phi>))"
                using Cons.hyps \<open>\<phi> \<in> set \<Phi>\<close>
                by auto
              moreover
              have "\<turnstile> (\<Squnion> \<Phi> \<leftrightarrow> (\<phi> \<squnion> \<Squnion> (removeAll \<phi> \<Phi>))) \<rightarrow>
                      (\<chi> \<squnion> \<Squnion> \<Phi>) \<leftrightarrow> (\<phi> \<squnion> \<chi> \<squnion> \<Squnion> (removeAll \<phi> \<Phi>))"
              proof -
                have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (removeAll \<phi> \<Phi>)\<^bold>\<rangle>)) \<rightarrow>
                                     (\<^bold>\<langle>\<chi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (removeAll \<phi> \<Phi>)\<^bold>\<rangle>)"
                    by auto
                  hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (removeAll \<phi> \<Phi>)\<^bold>\<rangle>)) \<rightarrow>
                             (\<^bold>\<langle>\<chi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (removeAll \<phi> \<Phi>)\<^bold>\<rangle>) \<^bold>\<rparr>"
                    using propositional_semantics by blast
                  thus ?thesis by simp
              qed
              ultimately have "\<turnstile> \<Squnion> (\<chi> # \<Phi>) \<leftrightarrow> (\<phi> \<squnion> \<chi> \<squnion> \<Squnion> (removeAll \<phi> \<Phi>))"
                using Modus_Ponens by auto
              show ?thesis
              proof cases
                assume "\<phi> = \<chi>"
                then show ?thesis
                  using \<open>\<turnstile> \<Squnion> (\<chi> # \<Phi>) \<leftrightarrow> (\<phi> \<squnion> \<chi> \<squnion> \<Squnion> (removeAll \<phi> \<Phi>))\<close>
                  unfolding biconditional_def
                  by (simp add: disjunction_def,
                      meson Axiom_K Modus_Ponens flip_hypothetical_syllogism implication_absorption)
              next
                assume "\<phi> \<noteq> \<chi>"
                then show ?thesis
                  using \<open>\<turnstile> \<Squnion> (\<chi> # \<Phi>) \<leftrightarrow> (\<phi> \<squnion> \<chi> \<squnion> \<Squnion> (removeAll \<phi> \<Phi>))\<close>
                  by simp
              qed
            next
              assume "\<phi> \<notin> set \<Phi>"
              hence "\<phi> = \<chi>" "\<chi> \<notin> set \<Phi>"
                using \<open>\<phi> \<in> set (\<chi> # \<Phi>)\<close> by auto
              then show ?thesis
                using biconditional_reflection
                by simp
            qed
          }
          thus ?case by blast
        qed
        hence "\<turnstile> \<Squnion> \<Phi> \<rightarrow> (\<psi> \<squnion> \<Squnion> (removeAll \<psi> \<Phi>))"
          using Modus_Ponens biconditional_left_elimination \<open>\<psi> \<in> set \<Phi>\<close> by blast
        moreover
        from \<open>\<psi> \<in> set \<Phi>\<close> \<open>set \<Phi> \<subseteq> set (\<psi> # \<Psi>)\<close> Cons.hyps
        have "\<turnstile> \<Squnion> (removeAll \<psi> \<Phi>) \<rightarrow> \<Squnion> \<Psi>"
          by (simp add: subset_insert_iff insert_absorb)
        hence "\<turnstile> (\<psi> \<squnion> \<Squnion> (removeAll \<psi> \<Phi>)) \<rightarrow> \<Squnion> (\<psi> # \<Psi>)"
          using 
            Modus_Ponens 
            disjunction_def 
            hypothetical_syllogism 
          by fastforce
        ultimately show ?thesis
          by (simp, metis Modus_Ponens hypothetical_syllogism)
      next
        assume "\<psi> \<notin> set \<Phi>"
        hence "\<turnstile> \<Squnion> \<Phi> \<rightarrow> \<Squnion> \<Psi>"
          using Cons.hyps \<open>set \<Phi> \<subseteq> set (\<psi> # \<Psi>)\<close>
          by auto
        then show ?thesis
          apply simp
          unfolding disjunction_def
          using Axiom_K Modus_Ponens flip_implication by blast
      qed
    }
    then show ?case by blast
  qed
  thus "set \<Phi> \<subseteq> set \<Psi> \<Longrightarrow> \<turnstile> \<Squnion> \<Phi> \<rightarrow> \<Squnion> \<Psi>" by blast
qed

lemma (in Classical_Logic) arbitrary_disjunction_remdups:
  "\<turnstile> (\<Squnion> \<Phi>) \<leftrightarrow> \<Squnion> (remdups \<Phi>)"
  by (simp add: arbitrary_disjunction_monotone biconditional_def)

subsubsection \<open> Distribution Identities \<close>

lemma (in Classical_Logic) conjunction_distribution:
  "\<turnstile> ((\<psi> \<squnion> \<chi>) \<sqinter> \<phi>) \<leftrightarrow> ((\<psi> \<sqinter> \<phi>) \<squnion> (\<chi> \<sqinter> \<phi>))"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ((\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<sqinter> \<^bold>\<langle>\<phi>\<^bold>\<rangle>) \<leftrightarrow> ((\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<phi>\<^bold>\<rangle>) \<squnion> (\<^bold>\<langle>\<chi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<phi>\<^bold>\<rangle>))"
      by auto
  hence "\<turnstile> \<^bold>\<lparr> ((\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<sqinter> \<^bold>\<langle>\<phi>\<^bold>\<rangle>) \<leftrightarrow> ((\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<phi>\<^bold>\<rangle>) \<squnion> (\<^bold>\<langle>\<chi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<phi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
    using propositional_semantics by blast
  thus ?thesis by simp
qed

lemma (in Classical_Logic) subtraction_distribution:
  "\<turnstile> ((\<psi> \<squnion> \<chi>) \<setminus> \<phi>) \<leftrightarrow> ((\<psi> \<setminus> \<phi>) \<squnion> (\<chi> \<setminus> \<phi>))"
  by (simp add: conjunction_distribution subtraction_def)

lemma (in Classical_Logic) conjunction_arbitrary_distribution:
  "\<turnstile> (\<Squnion> \<Psi> \<sqinter> \<phi>) \<leftrightarrow> \<Squnion> [\<psi> \<sqinter> \<phi>. \<psi> \<leftarrow> \<Psi>]"
proof (induct \<Psi>)
  case Nil
  then show ?case
    by (simp add: Ex_Falso_Quodlibet
                  biconditional_def
                  conjunction_left_elimination)
next
  case (Cons \<psi> \<Psi>)
  have "\<turnstile> (\<Squnion> (\<psi> # \<Psi>) \<sqinter> \<phi>) \<leftrightarrow> ((\<psi> \<sqinter> \<phi>) \<squnion> ((\<Squnion> \<Psi>) \<sqinter> \<phi>))"
    using conjunction_distribution by auto
  moreover
  from Cons have 
    "\<turnstile> ((\<psi> \<sqinter> \<phi>) \<squnion> ((\<Squnion> \<Psi>) \<sqinter> \<phi>)) \<leftrightarrow> ((\<psi> \<sqinter> \<phi>) \<squnion> (\<Squnion> [\<psi> \<sqinter> \<phi>. \<psi> \<leftarrow> \<Psi>]))"
    unfolding disjunction_def biconditional_def
    by (simp, meson Modus_Ponens hypothetical_syllogism)
  ultimately show ?case
    by (simp, metis biconditional_transitivity_rule)
qed

lemma (in Classical_Logic) subtraction_arbitrary_distribution:
  "\<turnstile> (\<Squnion> \<Psi> \<setminus> \<phi>) \<leftrightarrow> \<Squnion> [\<psi> \<setminus> \<phi>. \<psi> \<leftarrow> \<Psi>]"
  by (simp add: conjunction_arbitrary_distribution subtraction_def)

lemma (in Classical_Logic) disjunction_distribution:
  "\<turnstile> (\<phi> \<squnion> (\<psi> \<sqinter> \<chi>)) \<leftrightarrow> ((\<phi> \<squnion> \<psi>) \<sqinter> (\<phi> \<squnion> \<chi>))"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>))"
      by auto
  hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
    using propositional_semantics by blast
  thus ?thesis by simp
qed

lemma (in Classical_Logic) implication_distribution:
  "\<turnstile> (\<phi> \<rightarrow> (\<psi> \<sqinter> \<chi>)) \<leftrightarrow> ((\<phi> \<rightarrow> \<psi>) \<sqinter> (\<phi> \<rightarrow> \<chi>))"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>))"
      by auto
  hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
    using propositional_semantics by blast
  thus ?thesis by simp
qed

lemma (in Classical_Logic) list_implication_distribution:
  "\<turnstile> (\<Phi> :\<rightarrow> (\<psi> \<sqinter> \<chi>)) \<leftrightarrow> ((\<Phi> :\<rightarrow> \<psi>) \<sqinter> (\<Phi> :\<rightarrow> \<chi>))"
proof (induct \<Phi>)
  case Nil
  then show ?case
    by (simp add: biconditional_reflection)
next
  case (Cons \<phi> \<Phi>)
  hence " \<turnstile> (\<phi> # \<Phi>) :\<rightarrow> (\<psi> \<sqinter> \<chi>) \<leftrightarrow> (\<phi> \<rightarrow> (\<Phi> :\<rightarrow> \<psi> \<sqinter> \<Phi> :\<rightarrow> \<chi>))"
    unfolding biconditional_def
    apply simp
    using Modus_Ponens hypothetical_syllogism
    by blast
  moreover have "\<turnstile> (\<phi> \<rightarrow> (\<Phi> :\<rightarrow> \<psi> \<sqinter> \<Phi> :\<rightarrow> \<chi>)) \<leftrightarrow> (((\<phi> # \<Phi>) :\<rightarrow> \<psi>) \<sqinter> ((\<phi> # \<Phi>) :\<rightarrow> \<chi>))"
    using implication_distribution by auto
  ultimately show ?case
    by (simp, metis biconditional_transitivity_rule)
qed

lemma (in Classical_Logic) biconditional_conjunction_weaken:
  "\<turnstile> (\<alpha> \<leftrightarrow> \<beta>) \<rightarrow> ((\<gamma> \<sqinter> \<alpha>) \<leftrightarrow> (\<gamma> \<sqinter> \<beta>))"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<alpha>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<beta>\<^bold>\<rangle>) \<rightarrow> ((\<^bold>\<langle>\<gamma>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<alpha>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<gamma>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<beta>\<^bold>\<rangle>))"
      by auto
  hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<alpha>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<beta>\<^bold>\<rangle>) \<rightarrow> ((\<^bold>\<langle>\<gamma>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<alpha>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<gamma>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<beta>\<^bold>\<rangle>)) \<^bold>\<rparr>"
    using propositional_semantics by blast
  thus ?thesis by simp
qed

lemma (in Classical_Logic) biconditional_conjunction_weaken_rule:
  "\<turnstile> (\<alpha> \<leftrightarrow> \<beta>) \<Longrightarrow> \<turnstile> (\<gamma> \<sqinter> \<alpha>) \<leftrightarrow> (\<gamma> \<sqinter> \<beta>)"
  using Modus_Ponens biconditional_conjunction_weaken by blast

lemma (in Classical_Logic) disjunction_arbitrary_distribution:
  "\<turnstile> (\<phi> \<squnion> \<Sqinter> \<Psi>) \<leftrightarrow> \<Sqinter> [\<phi> \<squnion> \<psi>. \<psi> \<leftarrow> \<Psi>]"
proof (induct \<Psi>)
  case Nil
  then show ?case
    unfolding disjunction_def biconditional_def
    using Axiom_K Modus_Ponens verum_tautology
    by (simp, blast)
next
  case (Cons \<psi> \<Psi>)
  have "\<turnstile> (\<phi> \<squnion> \<Sqinter> (\<psi> # \<Psi>)) \<leftrightarrow> ((\<phi> \<squnion> \<psi>) \<sqinter> (\<phi> \<squnion> \<Sqinter> \<Psi>))"
    by (simp add: disjunction_distribution)
  moreover
  from biconditional_conjunction_weaken_rule
       Cons
  have " \<turnstile> ((\<phi> \<squnion> \<psi>) \<sqinter> \<phi> \<squnion> \<Sqinter> \<Psi>) \<leftrightarrow> \<Sqinter> (map (\<lambda> \<chi> . \<phi> \<squnion> \<chi>) (\<psi> # \<Psi>))"
    by simp
  ultimately show ?case
    by (metis biconditional_transitivity_rule)
qed

lemma (in Classical_Logic) list_implication_arbitrary_distribution:
  "\<turnstile> (\<Phi> :\<rightarrow> \<Sqinter> \<Psi>) \<leftrightarrow> \<Sqinter> [\<Phi> :\<rightarrow> \<psi>. \<psi> \<leftarrow> \<Psi>]"
proof (induct \<Psi>)
  case Nil
  then show ?case
    by (simp add: biconditional_def,
        meson Axiom_K
              Modus_Ponens
              list_implication_Axiom_K
              verum_tautology)
next
  case (Cons \<psi> \<Psi>)
  have "\<turnstile> \<Phi> :\<rightarrow> \<Sqinter> (\<psi> # \<Psi>) \<leftrightarrow> (\<Phi> :\<rightarrow> \<psi> \<sqinter> \<Phi> :\<rightarrow> \<Sqinter> \<Psi>)"
    using list_implication_distribution
    by fastforce
  moreover
  from biconditional_conjunction_weaken_rule
       Cons
  have "\<turnstile> (\<Phi> :\<rightarrow> \<psi> \<sqinter> \<Phi> :\<rightarrow> \<Sqinter> \<Psi>) \<leftrightarrow> \<Sqinter> [\<Phi> :\<rightarrow> \<psi>. \<psi> \<leftarrow> (\<psi> # \<Psi>)]"
    by simp
  ultimately show ?case
    by (metis biconditional_transitivity_rule)
qed

lemma (in Classical_Logic) implication_arbitrary_distribution:
  "\<turnstile> (\<phi> \<rightarrow> \<Sqinter> \<Psi>) \<leftrightarrow> \<Sqinter> [\<phi> \<rightarrow> \<psi>. \<psi> \<leftarrow> \<Psi>]"
  using list_implication_arbitrary_distribution [where ?\<Phi>="[\<phi>]"]
  by simp

subsubsection \<open> Negation \<close>

lemma (in Classical_Logic) double_negation_biconditional:
  "\<turnstile> \<sim> (\<sim> \<phi>) \<leftrightarrow> \<phi>"
  unfolding biconditional_def negation_def
  by (simp add: Double_Negation Double_Negation_converse)

lemma (in Classical_Logic) double_negation_elimination [simp]:
  "\<Gamma> \<tturnstile> \<sim> (\<sim> \<phi>) = \<Gamma> \<tturnstile> \<phi>"
  using set_deduction_weaken biconditional_weaken double_negation_biconditional
  by metis

lemma (in Classical_Logic) alt_double_negation_elimination [simp]:
  "\<Gamma> \<tturnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom> \<equiv> \<Gamma> \<tturnstile> \<phi>"
  using double_negation_elimination
  unfolding negation_def
  by auto

lemma (in Classical_Logic) base_double_negation_elimination [simp]:
  "\<turnstile> \<sim> (\<sim> \<phi>) = \<turnstile> \<phi>"
  by (metis double_negation_elimination set_deduction_base_theory)

lemma (in Classical_Logic) alt_base_double_negation_elimination [simp]:
  "\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom> \<equiv> \<turnstile> \<phi>"
  using base_double_negation_elimination
  unfolding negation_def
  by auto

subsection \<open> Mutual Exclusion Identities \<close>

lemma (in Classical_Logic) exclusion_contrapositive_equivalence:
  "\<turnstile> (\<phi> \<rightarrow> \<gamma>) \<leftrightarrow> \<sim> (\<phi> \<sqinter> \<sim> \<gamma>)"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<leftrightarrow> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<sim> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>)"
    by auto
  hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<leftrightarrow> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<sim> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<^bold>\<rparr>"
    using propositional_semantics by blast
  thus ?thesis by simp
qed

lemma (in Classical_Logic) disjuction_exclusion_equivalence:
  "\<Gamma> \<tturnstile> \<sim> (\<psi> \<sqinter> \<Squnion> \<Phi>) \<equiv> \<forall> \<phi> \<in> set \<Phi>. \<Gamma> \<tturnstile> \<sim> (\<psi> \<sqinter> \<phi>)"
proof (induct \<Phi>)
  case Nil
  then show ?case by (simp add: conjunction_right_elimination negation_def set_deduction_weaken)
next
  case (Cons \<phi> \<Phi>)
  have "\<turnstile> \<sim> (\<psi> \<sqinter> \<Squnion> (\<phi> # \<Phi>)) \<leftrightarrow> \<sim> (\<psi> \<sqinter> (\<phi> \<squnion> \<Squnion> \<Phi>))"
    by (simp add: biconditional_reflection)
  moreover have "\<turnstile> \<sim> (\<psi> \<sqinter> (\<phi> \<squnion> \<Squnion> \<Phi>)) \<leftrightarrow> (\<sim> (\<psi> \<sqinter> \<phi>) \<sqinter> \<sim> (\<psi> \<sqinter> \<Squnion> \<Phi>))"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<sim> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>)) \<leftrightarrow> (\<sim> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<phi>\<^bold>\<rangle>) \<sqinter> \<sim> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>))"
      by auto
    hence "\<turnstile> \<^bold>\<lparr> \<sim> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>)) \<leftrightarrow> (\<sim> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<phi>\<^bold>\<rangle>) \<sqinter> \<sim> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
      using propositional_semantics by blast
    thus ?thesis by simp
  qed
  ultimately have "\<turnstile> \<sim> (\<psi> \<sqinter> \<Squnion> (\<phi> # \<Phi>)) \<leftrightarrow> (\<sim> (\<psi> \<sqinter> \<phi>) \<sqinter> \<sim> (\<psi> \<sqinter> \<Squnion> \<Phi>))"
    by simp
  hence "\<Gamma> \<tturnstile> \<sim> (\<psi> \<sqinter> \<Squnion> (\<phi> # \<Phi>)) = (\<Gamma> \<tturnstile> \<sim> (\<psi> \<sqinter> \<phi>) \<and> (\<forall>\<phi>\<in>set \<Phi>. \<Gamma> \<tturnstile> \<sim> (\<psi> \<sqinter> \<phi>)))"
    using set_deduction_weaken [where \<Gamma>="\<Gamma>"]
          conjunction_set_deduction_equivalence [where \<Gamma>="\<Gamma>"]
          Cons.hyps
          biconditional_def
          set_deduction_modus_ponens
    by metis
  thus "\<Gamma> \<tturnstile> \<sim> (\<psi> \<sqinter> \<Squnion> (\<phi> # \<Phi>)) = (\<forall>\<phi>\<in>set (\<phi> # \<Phi>). \<Gamma> \<tturnstile> \<sim> (\<psi> \<sqinter> \<phi>))"
    by simp
qed

lemma (in Classical_Logic) exclusive_elimination1:
  assumes "\<Gamma> \<tturnstile> \<Coprod> \<Phi>"
  shows "\<forall> \<phi> \<in> set \<Phi>. \<forall> \<psi> \<in> set \<Phi>. (\<phi> \<noteq> \<psi>) \<longrightarrow> \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<psi>)"
  using assms
proof (induct \<Phi>)
  case Nil
  thus ?case by auto
next
  case (Cons \<chi> \<Phi>)
  assume "\<Gamma> \<tturnstile> \<Coprod> (\<chi> # \<Phi>)"
  hence "\<Gamma> \<tturnstile> \<Coprod> \<Phi>" by simp
  hence "\<forall>\<phi>\<in>set \<Phi>. \<forall>\<psi>\<in>set \<Phi>. \<phi> \<noteq> \<psi> \<longrightarrow> \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<psi>)" using Cons.hyps by blast
  moreover have "\<Gamma> \<tturnstile> \<sim> (\<chi> \<sqinter> \<Squnion> \<Phi>)"
    using \<open>\<Gamma> \<tturnstile> \<Coprod> (\<chi> # \<Phi>)\<close> conjunction_set_deduction_equivalence by auto
  hence "\<forall> \<phi> \<in> set \<Phi>. \<Gamma> \<tturnstile> \<sim> (\<chi> \<sqinter> \<phi>)"
    using disjuction_exclusion_equivalence by auto
  moreover {
    fix \<phi>
    have "\<turnstile> \<sim> (\<chi> \<sqinter> \<phi>) \<rightarrow> \<sim> (\<phi> \<sqinter> \<chi>)"
      unfolding negation_def
                conjunction_def
      using Modus_Ponens flip_hypothetical_syllogism flip_implication by blast
  }
  with \<open>\<forall> \<phi> \<in> set \<Phi>. \<Gamma> \<tturnstile> \<sim> (\<chi> \<sqinter> \<phi>)\<close> have "\<forall> \<phi> \<in> set \<Phi>. \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<chi>)"
    using set_deduction_weaken [where \<Gamma>="\<Gamma>"]
          set_deduction_modus_ponens [where \<Gamma>="\<Gamma>"]
    by blast
  ultimately show "\<forall>\<phi> \<in> set (\<chi> # \<Phi>). \<forall>\<psi> \<in> set (\<chi> # \<Phi>). \<phi> \<noteq> \<psi> \<longrightarrow> \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<psi>)"
    by simp
qed

lemma (in Classical_Logic) exclusive_elimination2:
  assumes "\<Gamma> \<tturnstile> \<Coprod> \<Phi>"
  shows "\<forall> \<phi> \<in> duplicates \<Phi>. \<Gamma> \<tturnstile> \<sim> \<phi>"
  using assms
proof (induct \<Phi>)
  case Nil
  then show ?case by simp
next
  case (Cons \<phi> \<Phi>)
  assume "\<Gamma> \<tturnstile> \<Coprod> (\<phi> # \<Phi>)"
  hence "\<Gamma> \<tturnstile> \<Coprod> \<Phi>" by simp
  hence "\<forall>\<phi>\<in>duplicates \<Phi>. \<Gamma> \<tturnstile> \<sim> \<phi>" using Cons.hyps by auto
  show ?case
  proof cases
    assume "\<phi> \<in> set \<Phi>"
    moreover {
      fix \<phi> \<psi> \<chi>
      have "\<turnstile> \<sim> (\<phi> \<sqinter> (\<psi> \<squnion> \<chi>)) \<leftrightarrow> (\<sim> (\<phi> \<sqinter> \<psi>) \<sqinter> \<sim> (\<phi> \<sqinter> \<chi>))"
      proof -
        have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<leftrightarrow> (\<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>))"
          by auto
        hence "\<turnstile> \<^bold>\<lparr> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<leftrightarrow> (\<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
          using propositional_semantics by blast
        thus ?thesis by simp
      qed
      hence "\<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> (\<psi> \<squnion> \<chi>)) \<equiv> \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<psi>) \<sqinter> \<sim> (\<phi> \<sqinter> \<chi>)"
        using set_deduction_weaken
              biconditional_weaken by presburger
    }
    moreover
    have "\<turnstile> \<sim> (\<phi> \<sqinter> \<phi>) \<leftrightarrow> \<sim> \<phi>"
    proof -
      have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<phi>\<^bold>\<rangle>) \<leftrightarrow> \<sim> \<^bold>\<langle>\<phi>\<^bold>\<rangle>"
        by auto
      hence "\<turnstile> \<^bold>\<lparr> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<phi>\<^bold>\<rangle>) \<leftrightarrow> \<sim> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<^bold>\<rparr>"
        using propositional_semantics by blast
      thus ?thesis by simp
    qed
    hence "\<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<phi>) \<equiv> \<Gamma> \<tturnstile> \<sim> \<phi>"
      using set_deduction_weaken
            biconditional_weaken by presburger
    moreover have "\<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<Squnion> \<Phi>)" using \<open>\<Gamma> \<tturnstile> \<Coprod> (\<phi> # \<Phi>)\<close> by simp
    ultimately have "\<Gamma> \<tturnstile> \<sim> \<phi>" by (induct \<Phi>, simp, simp, blast)
    thus ?thesis using \<open>\<phi> \<in> set \<Phi>\<close> \<open>\<forall>\<phi>\<in>duplicates \<Phi>. \<Gamma> \<tturnstile> \<sim> \<phi>\<close> by simp
  next
    assume "\<phi> \<notin> set \<Phi>"
    hence "duplicates (\<phi> # \<Phi>) = duplicates \<Phi>" by simp
    then show ?thesis using \<open>\<forall>\<phi>\<in>duplicates \<Phi>. \<Gamma> \<tturnstile> \<sim> \<phi>\<close>
      by auto
  qed
qed

lemma (in Classical_Logic) exclusive_equivalence:
   "\<Gamma> \<tturnstile> \<Coprod> \<Phi> =
      ((\<forall>\<phi>\<in>duplicates \<Phi>. \<Gamma> \<tturnstile> \<sim> \<phi>) \<and> 
         (\<forall> \<phi> \<in> set \<Phi>. \<forall> \<psi> \<in> set \<Phi>. (\<phi> \<noteq> \<psi>) \<longrightarrow> \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<psi>)))"
proof -
  {
    assume "\<forall>\<phi>\<in>duplicates \<Phi>. \<Gamma> \<tturnstile> \<sim> \<phi>"
           "\<forall> \<phi> \<in> set \<Phi>. \<forall> \<psi> \<in> set \<Phi>. (\<phi> \<noteq> \<psi>) \<longrightarrow> \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<psi>)"
    hence "\<Gamma> \<tturnstile> \<Coprod> \<Phi>"
    proof (induct \<Phi>)
      case Nil
      then show ?case
        by (simp add: set_deduction_weaken)
    next
      case (Cons \<phi> \<Phi>)
      assume A: "\<forall>\<phi>\<in>duplicates (\<phi> # \<Phi>). \<Gamma> \<tturnstile> \<sim> \<phi>"
         and B: "\<forall>\<chi>\<in>set (\<phi> # \<Phi>). \<forall>\<psi>\<in>set (\<phi> # \<Phi>). \<chi> \<noteq> \<psi> \<longrightarrow> \<Gamma> \<tturnstile> \<sim> (\<chi> \<sqinter> \<psi>)"
      hence C: "\<Gamma> \<tturnstile> \<Coprod> \<Phi>" using Cons.hyps by simp
      then show ?case
      proof cases
        assume "\<phi> \<in> duplicates (\<phi> # \<Phi>)"
        moreover from this have "\<Gamma> \<tturnstile> \<sim> \<phi>" using A by auto
        moreover have "duplicates \<Phi> \<subseteq> set \<Phi>" by (induct \<Phi>, simp, auto)
        ultimately have "\<phi> \<in> set \<Phi>" by (metis duplicates.simps(2) subsetCE)
        hence "\<turnstile> \<sim> \<phi> \<leftrightarrow> \<sim>(\<phi> \<sqinter> \<Squnion> \<Phi>)"
        proof (induct \<Phi>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<psi> \<Phi>)
          assume "\<phi> \<in> set (\<psi> # \<Phi>)"
          then show "\<turnstile> \<sim> \<phi> \<leftrightarrow> \<sim> (\<phi> \<sqinter> \<Squnion> (\<psi> # \<Phi>))"
          proof -
            {
              assume "\<phi> = \<psi>"
              hence ?thesis
              proof -
                have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<sim> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>))"
                  using \<open>\<phi> = \<psi>\<close> by auto
                hence "\<turnstile> \<^bold>\<lparr> \<sim> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
                  using propositional_semantics by blast
                thus ?thesis by simp
              qed
            }
            moreover
            {
              assume "\<phi> \<noteq> \<psi>"
              hence "\<phi> \<in> set \<Phi>" using \<open>\<phi> \<in> set (\<psi> # \<Phi>)\<close> by auto
              hence "\<turnstile> \<sim> \<phi> \<leftrightarrow> \<sim> (\<phi> \<sqinter> \<Squnion> \<Phi>)" using Cons.hyps by auto
              moreover have "\<turnstile> (\<sim> \<phi> \<leftrightarrow> \<sim> (\<phi> \<sqinter> \<Squnion> \<Phi>)) \<rightarrow> (\<sim> \<phi> \<leftrightarrow> \<sim> (\<phi> \<sqinter> (\<psi> \<squnion> \<Squnion> \<Phi>)))"
              proof -
                have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<sim> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>)) \<rightarrow>
                                     (\<sim> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>)))"
                  by auto
                hence "\<turnstile> \<^bold>\<lparr> (\<sim> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>)) \<rightarrow> (\<sim> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>))) \<^bold>\<rparr>"
                  using propositional_semantics by blast
                thus ?thesis by simp
              qed
              ultimately have ?thesis using Modus_Ponens by simp
            }
            ultimately show ?thesis by auto
          qed
        qed
        with \<open>\<Gamma> \<tturnstile> \<sim> \<phi>\<close> have "\<Gamma> \<tturnstile> \<sim>(\<phi> \<sqinter> \<Squnion> \<Phi>)"
          using biconditional_weaken set_deduction_weaken by blast
        with \<open>\<Gamma> \<tturnstile> \<Coprod> \<Phi>\<close> show ?thesis by simp
      next
        assume "\<phi> \<notin> duplicates (\<phi> # \<Phi>)"
        hence "\<phi> \<notin> set \<Phi>" by auto
        with B have "\<forall>\<psi>\<in>set \<Phi>. \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<psi>)" by (simp, metis)
        hence "\<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<Squnion> \<Phi>)"
          by (simp add: disjuction_exclusion_equivalence)
        with \<open>\<Gamma> \<tturnstile> \<Coprod> \<Phi>\<close> show ?thesis by simp
      qed
    qed
  }
  thus ?thesis
    by (metis exclusive_elimination1 exclusive_elimination2)
qed


end
