section {* Classical Propositional Connectives *}

theory Classical_Propositional_Connectives
  imports Classical_Propositional_Calculus
          "../../../Utilities/List_Utilities"
begin

subsection {* Conjunction *}

definition (in Classical_Propositional_Logic) conjunction :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixr "\<sqinter>" 67)
  where
    "\<phi> \<sqinter> \<psi> = (\<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>"

lemma (in Classical_Propositional_Logic) conjunction_introduction:
  "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> (\<phi> \<sqinter> \<psi>)"
  by (metis Modus_Ponens 
            conjunction_def 
            list_flip_implication1 
            list_implication.simps(1) 
            list_implication.simps(2))

lemma (in Classical_Propositional_Logic) conjunction_left_elimination:
  "\<turnstile> (\<phi> \<sqinter> \<psi>) \<rightarrow> \<phi>"
  by (metis (full_types) Peirces_law 
                         The_Principle_of_Pseudo_Scotus 
                         conjunction_def 
                         list_deduction_base_theory 
                         list_deduction_modus_ponens 
                         list_deduction_theorem 
                         list_deduction_weaken)  

lemma (in Classical_Propositional_Logic) conjunction_right_elimination:
  "\<turnstile> (\<phi> \<sqinter> \<psi>) \<rightarrow> \<psi>"
  by (metis (full_types) Axiom_1 
                         Contraposition 
                         Modus_Ponens 
                         conjunction_def 
                         flip_hypothetical_syllogism 
                         flip_implication)

lemma (in Classical_Propositional_Logic) conjunction_embedding [simp]:
  "\<^bold>\<lparr> \<phi> \<sqinter> \<psi> \<^bold>\<rparr> = \<^bold>\<lparr> \<phi> \<^bold>\<rparr> \<sqinter> \<^bold>\<lparr> \<psi> \<^bold>\<rparr>"
  unfolding conjunction_def Classical_Propositional_Logic_class.conjunction_def
  by simp

lemma conjunction_semantics [simp]:
  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<sqinter> \<psi> = (\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<and> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<psi>)"
  unfolding conjunction_def by simp
    
subsection {* Biconditional *}

definition (in Classical_Propositional_Logic) biconditional :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixr "\<leftrightarrow>" 75)
  where 
    "\<phi> \<leftrightarrow> \<psi> = (\<phi> \<rightarrow> \<psi>) \<sqinter> (\<psi> \<rightarrow> \<phi>)"

lemma (in Classical_Propositional_Logic) biconditional_introduction:
  "\<turnstile> (\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<psi> \<rightarrow> \<phi>) \<rightarrow> (\<phi> \<leftrightarrow> \<psi>)"
  by (simp add: biconditional_def conjunction_introduction)

lemma (in Classical_Propositional_Logic) biconditional_left_elimination:
  "\<turnstile> (\<phi> \<leftrightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<psi>"
  by (simp add: biconditional_def conjunction_left_elimination)

lemma (in Classical_Propositional_Logic) biconditional_right_elimination:
  "\<turnstile> (\<phi> \<leftrightarrow> \<psi>) \<rightarrow> \<psi> \<rightarrow> \<phi>"
  by (simp add: biconditional_def conjunction_right_elimination)

lemma (in Classical_Propositional_Logic) biconditional_embedding [simp]:
  "\<^bold>\<lparr> \<phi> \<leftrightarrow> \<psi> \<^bold>\<rparr> = \<^bold>\<lparr> \<phi> \<^bold>\<rparr> \<leftrightarrow> \<^bold>\<lparr> \<psi> \<^bold>\<rparr>"
  unfolding biconditional_def Classical_Propositional_Logic_class.biconditional_def
  by simp

lemma biconditional_semantics [simp]:
  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<leftrightarrow> \<psi> = (\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<longleftrightarrow> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<psi>)"
  unfolding biconditional_def
  by (simp, blast)
    
subsection {* Negation *}    

definition (in Minimal_Logic_With_Falsum) negation :: "'a \<Rightarrow> 'a"  ("\<sim>")
  where
    "\<sim> \<phi> = \<phi> \<rightarrow> \<bottom>"

lemma (in Minimal_Logic_With_Falsum) negation_introduction:
  "\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<sim> \<phi>"
  unfolding negation_def
  by (metis Axiom_1 Modus_Ponens implication_absorption)

lemma (in Minimal_Logic_With_Falsum) negation_elimination:
  "\<turnstile> \<sim> \<phi> \<rightarrow> (\<phi> \<rightarrow> \<bottom>)"
  unfolding negation_def
  by (metis Axiom_1 Modus_Ponens implication_absorption)  

lemma (in Classical_Propositional_Logic) negation_embedding [simp]:
  "\<^bold>\<lparr> \<sim> \<phi> \<^bold>\<rparr> = \<sim> \<^bold>\<lparr> \<phi> \<^bold>\<rparr>"
  unfolding negation_def Minimal_Logic_With_Falsum_class.negation_def
  by simp

lemma negation_semantics [simp]:
  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<sim> \<phi> = (\<not> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>)"
  unfolding negation_def
  by simp
    
subsection {* Disjunction *}
    
definition (in Classical_Propositional_Logic) disjunction :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixr "\<squnion>" 67)
  where
    "\<phi> \<squnion> \<psi> = (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>"

primrec (in Classical_Propositional_Logic) Arbitrary_Disjunction :: "'a list \<Rightarrow> 'a" ("\<Squnion>")
  where
     "\<Squnion> [] = \<bottom>"
  |  "\<Squnion> (\<phi> # \<Phi>) = \<phi> \<squnion> \<Squnion> \<Phi>"    
    
lemma (in Classical_Propositional_Logic) disjunction_elimination:
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
    
lemma (in Classical_Propositional_Logic) disjunction_left_introduction:
  "\<turnstile> \<phi> \<rightarrow> (\<phi> \<squnion> \<psi>)"
  unfolding disjunction_def
  by (metis Modus_Ponens 
            The_Principle_of_Pseudo_Scotus 
            flip_implication)

lemma (in Classical_Propositional_Logic) disjunction_right_introduction:
  "\<turnstile> \<psi> \<rightarrow> (\<phi> \<squnion> \<psi>)"
  unfolding disjunction_def
  using Axiom_1
  by simp

lemma (in Classical_Propositional_Logic) disjunction_embedding [simp]:
  "\<^bold>\<lparr> \<phi> \<squnion> \<psi> \<^bold>\<rparr> = \<^bold>\<lparr> \<phi> \<^bold>\<rparr> \<squnion> \<^bold>\<lparr> \<psi> \<^bold>\<rparr>"
  unfolding disjunction_def Classical_Propositional_Logic_class.disjunction_def
  by simp

lemma disjunction_semantics [simp]:
  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<squnion> \<psi> = (\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<or> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<psi>)"
  unfolding disjunction_def
  by (simp, blast)

subsection {* Verum *}    
    
definition (in Minimal_Logic_With_Falsum) verum :: "'a" ("\<top>")
  where
    "\<top> = \<bottom> \<rightarrow> \<bottom>"

lemma (in Minimal_Logic_With_Falsum) verum_tautology: "\<turnstile> \<top>"
  by (metis list_implication.simps(1) list_implication_Axiom_1 verum_def)

subsection {* Mutual Exclusion *}

primrec (in Classical_Propositional_Logic) exclusive :: "'a list \<Rightarrow> 'a"
  where
      "exclusive [] = \<top>"
    | "exclusive (\<phi> # \<Phi>) = \<sim> (\<phi> \<sqinter> \<Squnion> \<Phi>) \<sqinter> exclusive \<Phi>"
          
subsection {* Subtraction *}    
    
definition (in Classical_Propositional_Logic) subtraction :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixl "\<setminus>" 69)
  where
    "\<phi> \<setminus> \<psi> = \<phi> \<sqinter> \<sim> \<psi>"

lemma (in Classical_Propositional_Logic) subtraction_embedding [simp]:
  "\<^bold>\<lparr> \<phi> \<setminus> \<psi> \<^bold>\<rparr> = \<^bold>\<lparr> \<phi> \<^bold>\<rparr> \<setminus> \<^bold>\<lparr> \<psi> \<^bold>\<rparr>"
  unfolding subtraction_def Classical_Propositional_Logic_class.subtraction_def
  by simp
    
subsection {* Common Rules *}

subsubsection {* Biconditional Equivalence Relation *}

lemma (in Classical_Propositional_Logic) biconditional_reflection:
  "\<turnstile> \<phi> \<leftrightarrow> \<phi>"
  by (meson Axiom_1 Modus_Ponens biconditional_introduction implication_absorption)

lemma (in Classical_Propositional_Logic) biconditional_symmetry:
  "\<turnstile> (\<phi> \<leftrightarrow> \<psi>) \<leftrightarrow> (\<psi> \<leftrightarrow> \<phi>)"
  by (metis (full_types) Modus_Ponens 
                         biconditional_def 
                         conjunction_def
                         flip_hypothetical_syllogism 
                         flip_implication)

lemma (in Classical_Propositional_Logic) biconditional_transitivity:
    "\<turnstile> (\<phi> \<leftrightarrow> \<psi>) \<rightarrow> (\<psi> \<leftrightarrow> \<chi>) \<rightarrow> (\<phi> \<leftrightarrow> \<chi>)"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)"
    by simp
 hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<^bold>\<rparr>"
   using propositional_semantics by blast
 thus ?thesis by simp
qed

lemma (in Classical_Propositional_Logic) biconditional_weaken:
  assumes "\<Gamma> \<tturnstile> \<phi> \<leftrightarrow> \<psi>"
  shows "\<Gamma> \<tturnstile> \<phi> \<equiv> \<Gamma> \<tturnstile> \<psi>"
  by (smt assms 
          biconditional_left_elimination 
          biconditional_right_elimination 
          set_deduction_modus_ponens 
          set_deduction_weaken)

subsubsection {* Conjunction Identities *}

lemma (in Classical_Propositional_Logic) conjunction_negation_identity:
  "\<turnstile> \<sim> (\<phi> \<sqinter> \<psi>) \<leftrightarrow> (\<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom>)"
  by (metis Contraposition 
            Double_Negation_converse 
            Modus_Ponens 
            biconditional_introduction
            conjunction_def 
            negation_def)

lemma (in Classical_Propositional_Logic) conjunction_deduction_equivalence [simp]:
  "\<Gamma> \<tturnstile> \<phi> \<sqinter> \<psi> \<equiv> \<Gamma> \<tturnstile> \<phi> \<and> \<Gamma> \<tturnstile> \<psi>"
  using set_deduction_weaken [where \<Gamma>="\<Gamma>"]
        set_deduction_modus_ponens [where \<Gamma>="\<Gamma>"]
  by (smt conjunction_introduction conjunction_left_elimination conjunction_right_elimination)

lemma (in Classical_Propositional_Logic) weak_conjunction_deduction_equivalence [simp]:
  "\<turnstile> \<phi> \<sqinter> \<psi> \<equiv> \<turnstile> \<phi> \<and> \<turnstile> \<psi>"
  by (smt conjunction_deduction_equivalence set_deduction_base_theory)

    
lemma (in Classical_Propositional_Logic) conjunction_commutativity:
  "\<turnstile> (\<psi> \<sqinter> \<phi>) \<leftrightarrow> (\<phi> \<sqinter> \<psi>)"
  by (metis (full_types) Modus_Ponens 
                         biconditional_introduction 
                         conjunction_def 
                         flip_hypothetical_syllogism 
                         flip_implication)

lemma (in Classical_Propositional_Logic) conjunction_associativity:
  "\<turnstile> ((\<phi> \<sqinter> \<psi>) \<sqinter> \<chi>) \<leftrightarrow> (\<phi> \<sqinter> (\<psi> \<sqinter> \<chi>))"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>))"
    by simp
  hence "\<turnstile> \<^bold>\<lparr> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
    using propositional_semantics by blast
  thus ?thesis by simp
qed

subsubsection {* Disjunction Identities *}

lemma (in Classical_Propositional_Logic) bivalence:
  "\<turnstile> \<sim> \<phi> \<squnion> \<phi>"
  by (simp add: Double_Negation disjunction_def negation_def)

lemma (in Classical_Propositional_Logic) implication_equivalence:
  "\<turnstile> (\<sim> \<phi> \<squnion> \<psi>) \<leftrightarrow> (\<phi> \<rightarrow> \<psi>)"
  by (metis Double_Negation_converse 
            Modus_Ponens 
            biconditional_introduction 
            bivalence 
            disjunction_def 
            flip_hypothetical_syllogism 
            negation_def)
  
lemma (in Classical_Propositional_Logic) disjunction_commutativity:
  "\<turnstile> (\<psi> \<squnion> \<phi>) \<leftrightarrow> (\<phi> \<squnion> \<psi>)"
  by (meson Modus_Ponens 
            biconditional_introduction 
            disjunction_elimination 
            disjunction_left_introduction 
            disjunction_right_introduction)  
  
lemma (in Classical_Propositional_Logic) disjunction_associativity:
  "\<turnstile> ((\<phi> \<squnion> \<psi>) \<squnion> \<chi>) \<leftrightarrow> (\<phi> \<squnion> (\<psi> \<squnion> \<chi>))"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>))"
    by simp
  hence "\<turnstile> \<^bold>\<lparr> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
    using propositional_semantics by blast
  thus ?thesis by simp
qed

lemma (in Classical_Propositional_Logic) arbitrary_disjunction_monotone:
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
                      meson Axiom_1 Modus_Ponens flip_hypothetical_syllogism implication_absorption)
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
          apply simp
          unfolding disjunction_def
          using Modus_Ponens hypothetical_syllogism by blast
        ultimately show ?thesis
          apply simp
          using Modus_Ponens hypothetical_syllogism by blast
      next
        assume "\<psi> \<notin> set \<Phi>"
        hence "\<turnstile> \<Squnion> \<Phi> \<rightarrow> \<Squnion> \<Psi>"
          using Cons.hyps \<open>set \<Phi> \<subseteq> set (\<psi> # \<Psi>)\<close>
          by auto
        then show ?thesis
          apply simp
          unfolding disjunction_def
          using Axiom_1 Modus_Ponens flip_implication by blast
      qed
        
    }
    then show ?case by blast
  qed
  thus "set \<Phi> \<subseteq> set \<Psi> \<Longrightarrow> \<turnstile> \<Squnion> \<Phi> \<rightarrow> \<Squnion> \<Psi>" by blast
qed

lemma (in Classical_Propositional_Logic) arbitrary_disjunction_remdups:
  "\<turnstile> (\<Squnion> \<Phi>) \<leftrightarrow> \<Squnion> (remdups \<Phi>)"
  by (simp add: arbitrary_disjunction_monotone biconditional_def)
  
subsubsection {* Negation *}

lemma (in Classical_Propositional_Logic) double_negation_biconditional:
  "\<turnstile> \<sim> (\<sim> \<phi>) \<leftrightarrow> \<phi>"
  unfolding biconditional_def negation_def
  by (simp add: Double_Negation Double_Negation_converse)
  
lemma (in Classical_Propositional_Logic) double_negation_elimination [simp]:
  "\<Gamma> \<tturnstile> \<sim> (\<sim> \<phi>) \<equiv> \<Gamma> \<tturnstile> \<phi>"
  using set_deduction_weaken biconditional_weaken double_negation_biconditional
  by smt

lemma (in Classical_Propositional_Logic) alt_double_negation_elimination [simp]:
  "\<Gamma> \<tturnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom> \<equiv> \<Gamma> \<tturnstile> \<phi>"
  using double_negation_elimination 
  unfolding negation_def
  by auto
    
lemma (in Classical_Propositional_Logic) base_double_negation_elimination [simp]:    
  "\<turnstile> \<sim> (\<sim> \<phi>) \<equiv> \<turnstile> \<phi>"
  by (smt double_negation_elimination set_deduction_base_theory)
  

lemma (in Classical_Propositional_Logic) alt_base_double_negation_elimination [simp]:
  "\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom> \<equiv> \<turnstile> \<phi>"
  using base_double_negation_elimination
  unfolding negation_def
  by auto
    
subsection {* Mutual Exclusion Identities *}

lemma (in Classical_Propositional_Logic) exclusion_contrapositive_equivalence:
  "\<turnstile> (\<phi> \<rightarrow> \<gamma>) \<leftrightarrow> \<sim> (\<phi> \<sqinter> \<sim> \<gamma>)"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<leftrightarrow> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<sim> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>)"
    by auto
  hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<leftrightarrow> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<sim> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<^bold>\<rparr>"
    using propositional_semantics by blast
  thus ?thesis by simp
qed
  
lemma (in Classical_Propositional_Logic) disjuction_exclusion_equivalence:
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
  hence "\<Gamma> \<tturnstile> \<sim> (\<psi> \<sqinter> \<Squnion> (\<phi> # \<Phi>)) \<equiv> \<Gamma> \<tturnstile> \<sim> (\<psi> \<sqinter> \<phi>) \<and> (\<forall>\<phi>\<in>set \<Phi>. \<Gamma> \<tturnstile> \<sim> (\<psi> \<sqinter> \<phi>))"
    using set_deduction_weaken [where \<Gamma>="\<Gamma>"]
          conjunction_deduction_equivalence [where \<Gamma>="\<Gamma>"]
          Cons.hyps
          biconditional_def
          set_deduction_modus_ponens
    by smt
  thus "\<Gamma> \<tturnstile> \<sim> (\<psi> \<sqinter> \<Squnion> (\<phi> # \<Phi>)) = (\<forall>\<phi>\<in>set (\<phi> # \<Phi>). \<Gamma> \<tturnstile> \<sim> (\<psi> \<sqinter> \<phi>))"
    by simp
qed  
  
lemma (in Classical_Propositional_Logic) exclusive_elimination1:
  assumes "\<Gamma> \<tturnstile> exclusive \<Phi>"
  shows "\<forall> \<phi> \<in> set \<Phi>. \<forall> \<psi> \<in> set \<Phi>. (\<phi> \<noteq> \<psi>) \<longrightarrow> \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<psi>)"
  using assms
proof (induct \<Phi>)
  case Nil 
  thus ?case by auto 
next
  case (Cons \<chi> \<Phi>)
  assume "\<Gamma> \<tturnstile> exclusive (\<chi> # \<Phi>)"
  hence "\<Gamma> \<tturnstile> exclusive \<Phi>" by simp
  hence "\<forall>\<phi>\<in>set \<Phi>. \<forall>\<psi>\<in>set \<Phi>. \<phi> \<noteq> \<psi> \<longrightarrow> \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<psi>)" using Cons.hyps by blast 
  moreover have "\<Gamma> \<tturnstile> \<sim> (\<chi> \<sqinter> \<Squnion> \<Phi>)"
    using \<open>\<Gamma> \<tturnstile> exclusive (\<chi> # \<Phi>)\<close> conjunction_deduction_equivalence by auto
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
  
lemma (in Classical_Propositional_Logic) exclusive_elimination2:
  assumes "\<Gamma> \<tturnstile> exclusive \<Phi>"
  shows "\<forall> \<phi> \<in> duplicates \<Phi>. \<Gamma> \<tturnstile> \<sim> \<phi>"
  using assms
proof (induct \<Phi>)
  case Nil
  then show ?case by simp
next
  case (Cons \<phi> \<Phi>)
  assume "\<Gamma> \<tturnstile> exclusive (\<phi> # \<Phi>)"
  hence "\<Gamma> \<tturnstile> exclusive \<Phi>" by simp
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
    moreover have "\<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<Squnion> \<Phi>)" using \<open>\<Gamma> \<tturnstile> exclusive (\<phi> # \<Phi>)\<close> by simp
    ultimately have "\<Gamma> \<tturnstile> \<sim> \<phi>" by (induct \<Phi>, simp, simp, blast)
    thus ?thesis using \<open>\<phi> \<in> set \<Phi>\<close> \<open>\<forall>\<phi>\<in>duplicates \<Phi>. \<Gamma> \<tturnstile> \<sim> \<phi>\<close> by simp
  next
    assume "\<phi> \<notin> set \<Phi>"
    hence "duplicates (\<phi> # \<Phi>) = duplicates \<Phi>" by simp
    then show ?thesis using \<open>\<forall>\<phi>\<in>duplicates \<Phi>. \<Gamma> \<tturnstile> \<sim> \<phi>\<close> 
      by auto
  qed
qed

lemma (in Classical_Propositional_Logic) exclusive_equivalence:
   "\<Gamma> \<tturnstile> exclusive \<Phi> \<equiv> 
    (\<forall>\<phi>\<in>duplicates \<Phi>. \<Gamma> \<tturnstile> \<sim> \<phi>) \<and> (\<forall> \<phi> \<in> set \<Phi>. \<forall> \<psi> \<in> set \<Phi>. (\<phi> \<noteq> \<psi>) \<longrightarrow> \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<psi>))"
proof -
  {
    assume "\<forall>\<phi>\<in>duplicates \<Phi>. \<Gamma> \<tturnstile> \<sim> \<phi>"
           "\<forall> \<phi> \<in> set \<Phi>. \<forall> \<psi> \<in> set \<Phi>. (\<phi> \<noteq> \<psi>) \<longrightarrow> \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<psi>)"
    hence "\<Gamma> \<tturnstile> exclusive \<Phi>"
    proof (induct \<Phi>)
      case Nil
      then show ?case
        by (simp add: set_deduction_weaken verum_tautology) 
    next
      case (Cons \<phi> \<Phi>)
      assume A: "\<forall>\<phi>\<in>duplicates (\<phi> # \<Phi>). \<Gamma> \<tturnstile> \<sim> \<phi>"
         and B: "\<forall>\<chi>\<in>set (\<phi> # \<Phi>). \<forall>\<psi>\<in>set (\<phi> # \<Phi>). \<chi> \<noteq> \<psi> \<longrightarrow> \<Gamma> \<tturnstile> \<sim> (\<chi> \<sqinter> \<psi>)"
      hence C: "\<Gamma> \<tturnstile> exclusive \<Phi>" using Cons.hyps by simp 
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
        with \<open>\<Gamma> \<tturnstile> exclusive \<Phi>\<close> show ?thesis by simp
      next
        assume "\<phi> \<notin> duplicates (\<phi> # \<Phi>)"
        hence "\<phi> \<notin> set \<Phi>" by auto
        with B have "\<forall>\<psi>\<in>set \<Phi>. \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<psi>)" by (simp, metis)
        hence "\<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<Squnion> \<Phi>)"
          by (simp add: disjuction_exclusion_equivalence) 
        with \<open>\<Gamma> \<tturnstile> exclusive \<Phi>\<close> show ?thesis by simp
      qed
    qed
  }
  thus "\<Gamma> \<tturnstile> exclusive \<Phi> \<equiv> 
        (\<forall>\<phi>\<in>duplicates \<Phi>. \<Gamma> \<tturnstile> \<sim> \<phi>) \<and> (\<forall> \<phi> \<in> set \<Phi>. \<forall> \<psi> \<in> set \<Phi>. (\<phi> \<noteq> \<psi>) \<longrightarrow> \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<psi>))"
    by (smt exclusive_elimination1 exclusive_elimination2)
qed

  
end