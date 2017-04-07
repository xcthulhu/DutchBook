section {* Boolean Propositional Connectives *}

theory Boolean_Propositional_Connectives
   imports Boolean_Propositional_Soundness_And_Completeness
begin

subsection {* Conjunction *}

definition (in Boolean_Propositional_Logic) conjunction :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixr "\<sqinter>" 67)
  where
    "\<phi> \<sqinter> \<psi> = (\<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>"

lemma (in Boolean_Propositional_Logic) conjunction_introduction:
  "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> (\<phi> \<sqinter> \<psi>)"
  by (metis Modus_Ponens 
            conjunction_def 
            list_flip_implication1 
            list_implication.simps(1) 
            list_implication.simps(2))

lemma (in Boolean_Propositional_Logic) conjunction_left_elimination:
  "\<turnstile> (\<phi> \<sqinter> \<psi>) \<rightarrow> \<phi>"
  by (metis (full_types) Peirces_law 
                         The_Principle_of_Pseudo_Scotus 
                         conjunction_def 
                         list_deduction_base_theory 
                         list_deduction_modus_ponens 
                         list_deduction_theorem 
                         list_deduction_weaken)  

lemma (in Boolean_Propositional_Logic) conjunction_right_elimination:
  "\<turnstile> (\<phi> \<sqinter> \<psi>) \<rightarrow> \<psi>"
  by (metis (full_types) Axiom_1 
                         Contraposition 
                         Modus_Ponens 
                         conjunction_def 
                         flip_hypothetical_syllogism 
                         flip_implication)

lemma (in Boolean_Propositional_Logic) conjunction_embedding [simp]:
  "\<^bold>\<lparr> \<phi> \<sqinter> \<psi> \<^bold>\<rparr> = \<^bold>\<lparr> \<phi> \<^bold>\<rparr> \<sqinter> \<^bold>\<lparr> \<psi> \<^bold>\<rparr>"
  unfolding conjunction_def Boolean_Propositional_Logic_class.conjunction_def
  by simp

lemma conjunction_semantics [simp]:
  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<sqinter> \<psi> = (\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<and> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<psi>)"
  unfolding conjunction_def by simp
    
subsection {* Biconditional *}

definition (in Boolean_Propositional_Logic) biconditional :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixr "\<leftrightarrow>" 75)
  where 
    "\<phi> \<leftrightarrow> \<psi> = (\<phi> \<rightarrow> \<psi>) \<sqinter> (\<psi> \<rightarrow> \<phi>)"

lemma (in Boolean_Propositional_Logic) biconditional_introduction:
  "\<turnstile> (\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<psi> \<rightarrow> \<phi>) \<rightarrow> (\<phi> \<leftrightarrow> \<psi>)"
  by (simp add: biconditional_def conjunction_introduction)

lemma (in Boolean_Propositional_Logic) biconditional_left_elimination:
  "\<turnstile> (\<phi> \<leftrightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<psi>"
  by (simp add: biconditional_def conjunction_left_elimination)

lemma (in Boolean_Propositional_Logic) biconditional_right_elimination:
  "\<turnstile> (\<phi> \<leftrightarrow> \<psi>) \<rightarrow> \<psi> \<rightarrow> \<phi>"
  by (simp add: biconditional_def conjunction_right_elimination)

lemma (in Boolean_Propositional_Logic) biconditional_embedding [simp]:
  "\<^bold>\<lparr> \<phi> \<leftrightarrow> \<psi> \<^bold>\<rparr> = \<^bold>\<lparr> \<phi> \<^bold>\<rparr> \<leftrightarrow> \<^bold>\<lparr> \<psi> \<^bold>\<rparr>"
  unfolding biconditional_def Boolean_Propositional_Logic_class.biconditional_def
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

lemma (in Boolean_Propositional_Logic) negation_embedding [simp]:
  "\<^bold>\<lparr> \<sim> \<phi> \<^bold>\<rparr> = \<sim> \<^bold>\<lparr> \<phi> \<^bold>\<rparr>"
  unfolding negation_def Minimal_Logic_With_Falsum_class.negation_def
  by simp

lemma negation_semantics [simp]:
  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<sim> \<phi> = (\<not> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>)"
  unfolding negation_def
  by simp
    
subsection {* Disjunction *}
    
definition (in Boolean_Propositional_Logic) disjunction :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixr "\<squnion>" 68)
  where
    "\<phi> \<squnion> \<psi> = (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>"

lemma (in Boolean_Propositional_Logic) disjunction_elimination:
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
    
lemma (in Boolean_Propositional_Logic) disjunction_left_introduction:
  "\<turnstile> \<phi> \<rightarrow> (\<phi> \<squnion> \<psi>)"
  unfolding disjunction_def
  by (metis Modus_Ponens 
            The_Principle_of_Pseudo_Scotus 
            flip_implication)

lemma (in Boolean_Propositional_Logic) disjunction_right_introduction:
  "\<turnstile> \<psi> \<rightarrow> (\<phi> \<squnion> \<psi>)"
  unfolding disjunction_def
  using Axiom_1
  by simp

lemma (in Boolean_Propositional_Logic) disjunction_embedding [simp]:
  "\<^bold>\<lparr> \<phi> \<squnion> \<psi> \<^bold>\<rparr> = \<^bold>\<lparr> \<phi> \<^bold>\<rparr> \<squnion> \<^bold>\<lparr> \<psi> \<^bold>\<rparr>"
  unfolding disjunction_def Boolean_Propositional_Logic_class.disjunction_def
  by simp

lemma disjunction_semantics [simp]:
  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<squnion> \<psi> = (\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<or> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<psi>)"
  unfolding disjunction_def
  by (simp, blast)
    
subsection {* Subtraction *}    
    
definition (in Boolean_Propositional_Logic) subtraction :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixl "\<setminus>" 69)
  where
    "\<phi> \<setminus> \<psi> = \<phi> \<sqinter> \<sim> \<psi>"

lemma (in Boolean_Propositional_Logic) subtraction_embedding [simp]:
  "\<^bold>\<lparr> \<phi> \<setminus> \<psi> \<^bold>\<rparr> = \<^bold>\<lparr> \<phi> \<^bold>\<rparr> \<setminus> \<^bold>\<lparr> \<psi> \<^bold>\<rparr>"
  unfolding subtraction_def Boolean_Propositional_Logic_class.subtraction_def
  by simp
    
subsection {* Common Rules *}
  
subsubsection {* Biconditional Equivalence Relation *}

lemma (in Boolean_Propositional_Logic) biconditional_reflection:
  "\<turnstile> \<phi> \<leftrightarrow> \<phi>"
  by (meson Axiom_1 Modus_Ponens biconditional_introduction implication_absorption)

lemma (in Boolean_Propositional_Logic) biconditional_symmetry:
  "\<turnstile> (\<phi> \<leftrightarrow> \<psi>) \<leftrightarrow> (\<psi> \<leftrightarrow> \<phi>)"
  by (metis (full_types) Modus_Ponens 
                         biconditional_def 
                         conjunction_def
                         flip_hypothetical_syllogism 
                         flip_implication)

lemma (in Boolean_Propositional_Logic) biconditional_transitivity:
    "\<turnstile> (\<phi> \<leftrightarrow> \<psi>) \<rightarrow> (\<psi> \<leftrightarrow> \<chi>) \<rightarrow> (\<phi> \<leftrightarrow> \<chi>)"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)"
    unfolding Boolean_Propositional_Logic_class.biconditional_def
              Boolean_Propositional_Logic_class.conjunction_def
              implication_Boolean_Propositional_Formula_def
              Boolean_Propositional_Semantics.simps(2)
    by smt
 hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<^bold>\<rparr>"
   using propositional_semantics by blast
 thus ?thesis by simp
qed

subsubsection {* Conjunction Identities *}

lemma (in Boolean_Propositional_Logic) conjunction_negation_identity:
  "\<turnstile> \<sim> (\<phi> \<sqinter> \<psi>) \<leftrightarrow> (\<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom>)"
  by (metis Contraposition 
            Double_Negation_converse 
            Modus_Ponens 
            biconditional_introduction
            conjunction_def 
            negation_def)
  
lemma (in Boolean_Propositional_Logic) conjunction_commutativity:
  "\<turnstile> (\<psi> \<sqinter> \<phi>) \<leftrightarrow> (\<phi> \<sqinter> \<psi>)"
  by (metis (full_types) Modus_Ponens 
                         biconditional_introduction 
                         conjunction_def 
                         flip_hypothetical_syllogism 
                         flip_implication)

lemma (in Boolean_Propositional_Logic) conjunction_associativity:
  "\<turnstile> ((\<phi> \<sqinter> \<psi>) \<sqinter> \<chi>) \<leftrightarrow> (\<phi> \<sqinter> (\<psi> \<sqinter> \<chi>))"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>))"
    by (simp add: Boolean_Propositional_Logic_class.biconditional_def 
                  Boolean_Propositional_Logic_class.conjunction_def)
  hence "\<turnstile> \<^bold>\<lparr> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
    using propositional_semantics by blast
  thus ?thesis by simp
qed

subsubsection {* Disjunction Identities *}

lemma (in Boolean_Propositional_Logic) bivalence:
  "\<turnstile> \<sim> \<phi> \<squnion> \<phi>"
  by (simp add: Double_Negation disjunction_def negation_def)  
  
lemma (in Boolean_Propositional_Logic) disjunction_commutativity:
  "\<turnstile> (\<psi> \<squnion> \<phi>) \<leftrightarrow> (\<phi> \<squnion> \<psi>)"
  by (meson Modus_Ponens 
            biconditional_introduction 
            disjunction_elimination 
            disjunction_left_introduction 
            disjunction_right_introduction)  
  
lemma (in Boolean_Propositional_Logic) disjunction_associativity:
  "\<turnstile> ((\<phi> \<squnion> \<psi>) \<squnion> \<chi>) \<leftrightarrow> (\<phi> \<squnion> (\<psi> \<squnion> \<chi>))"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>))"
    by (simp add: Boolean_Propositional_Logic_class.biconditional_def 
                  Boolean_Propositional_Logic_class.conjunction_def 
                  Boolean_Propositional_Logic_class.disjunction_def)
  hence "\<turnstile> \<^bold>\<lparr> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
    using propositional_semantics by blast
  thus ?thesis by simp
qed

end