subsection {* Intuitionistic Logic *}
  
theory Intuitionistic_Logic
  imports Boolean_Propositional_Logic
begin

text {* This theory presents extends minimal logic to \emph{intuitionistic logic}.
        Intuitionistic logic include binary logical connectives
        for \emph{conjunction} and \emph{disjunction} as well as \emph{negation},
        \emph{falsum} and \emph{verum}. *}

subsection {* Axiomatization *}
  
class Intuitionistic_Logic = Minimal_Logic_With_Falsum +
  fixes verum :: "'a"                                            ("\<top>")
  fixes negation :: "'a \<Rightarrow> 'a"                                   ("\<sim>")
  fixes conjunction :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"                          (infixr "\<sqinter>" 67)
  fixes disjunction :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"                          (infixr "\<squnion>" 68)
  fixes biconditional :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"                        (infixr "\<leftrightarrow>" 75)
  assumes Conjunction_Introduction: "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> (\<phi> \<sqinter> \<psi>)"
  assumes Conjunction_Left_Elimination: "\<turnstile> (\<phi> \<sqinter> \<psi>) \<rightarrow> \<phi>"
  assumes Conjunction_Right_Elimination: "\<turnstile> (\<phi> \<sqinter> \<psi>) \<rightarrow> \<psi>"
  assumes Biconditional_Introduction: "\<turnstile> (\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<psi> \<rightarrow> \<phi>) \<rightarrow> (\<phi> \<leftrightarrow> \<psi>)"
  assumes Biconditional_Left_Elimination: "\<turnstile> (\<phi> \<leftrightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<psi>"
  assumes Biconditional_Right_Elimination: "\<turnstile> (\<phi> \<leftrightarrow> \<psi>) \<rightarrow> \<psi> \<rightarrow> \<phi>"
  assumes Disjunction_Elimination: "\<turnstile> (\<phi> \<rightarrow> \<chi>) \<rightarrow> (\<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<squnion> \<psi>) \<rightarrow> \<chi>"
  assumes Disjunction_Left_Introduction: "\<turnstile> \<phi> \<rightarrow> (\<phi> \<squnion> \<psi>)"
  assumes Disjunction_Right_Introduction: "\<turnstile> \<psi> \<rightarrow> (\<phi> \<squnion> \<psi>)"
  assumes Negation_Introduction: "\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<sim> \<phi>"
  assumes Negation_Elimination: "\<turnstile> \<sim> \<phi> \<rightarrow> \<phi> \<rightarrow> \<bottom>"
  assumes Verum_Rule: "\<turnstile> \<phi> \<rightarrow> \<top>"
  assumes Ex_Falso_Quodlibet: "\<turnstile> \<bottom> \<rightarrow> \<phi>"

class Extended_Boolean_Propositional_Logic = Boolean_Propositional_Logic + Intuitionistic_Logic 
    
subsection {* Maximally Consistent Sets *}
    
theorem (in Intuitionistic_Logic) Formula_Maximally_Consistent_Set_conjunction:
  assumes "\<phi>-MCS \<Omega>"
  shows "(\<psi> \<sqinter> \<chi>) \<in> \<Omega> \<equiv> \<psi> \<in> \<Omega> \<and> \<chi> \<in> \<Omega>"
proof -
  {
    assume "(\<psi> \<sqinter> \<chi>) \<in> \<Omega>"
    hence "\<psi> \<in> \<Omega>" "\<chi> \<in> \<Omega>"
      using assms
            Formula_Maximally_Consistent_Set_reflection
            Conjunction_Right_Elimination 
            Conjunction_Left_Elimination
            set_deduction_modus_ponens 
            set_deduction_weaken
      by metis+
  }
  moreover
  {
    assume "\<psi> \<in> \<Omega> \<and> \<chi> \<in> \<Omega>"
    hence "(\<psi> \<sqinter> \<chi>) \<in> \<Omega>"
      using assms
            Set.set_insert 
            insert_iff 
            Conjunction_Introduction [where \<phi>="\<psi>" and \<psi>="\<chi>"]
            Formula_Maximally_Consistent_Set_reflection [where \<Gamma>="\<Omega>" and \<phi>="\<phi>"]
            Modus_Ponens 
            implication_absorption 
            set_deduction_theorem 
            set_deduction_weaken
      by metis
  }
  ultimately show "(\<psi> \<sqinter> \<chi>) \<in> \<Omega> \<equiv> \<psi> \<in> \<Omega> \<and> \<chi> \<in> \<Omega>"
    by linarith
qed

lemma (in Intuitionistic_Logic) Formula_Maximally_Consistent_Set_disjunction:
  assumes "\<phi>-MCS \<Omega>"
  shows "(\<psi> \<squnion> \<chi>) \<in> \<Omega> \<equiv> \<psi> \<in> \<Omega> \<or> \<chi> \<in> \<Omega>"
proof -
  {
    assume "(\<psi> \<squnion> \<chi>) \<in> \<Omega>"
    { 
      assume "\<psi> \<notin> \<Omega>" "\<chi> \<notin> \<Omega>"
      hence "\<Omega> \<tturnstile> \<psi> \<rightarrow> \<phi>" "\<Omega> \<tturnstile> \<chi> \<rightarrow> \<phi>"
        using assms Formula_Maximally_Consistent_Set_def set_deduction_reflection 
        by blast+
      hence "\<Omega> \<tturnstile> \<phi>" 
        using \<open>(\<psi> \<squnion> \<chi>) \<in> \<Omega>\<close>
              set_deduction_weaken [where \<Gamma>="\<Omega>"]
              set_deduction_modus_ponens [where \<Gamma>="\<Omega>"]
              set_deduction_reflection [where \<Gamma>="\<Omega>" and \<phi>="\<psi> \<squnion> \<chi>"]
              Disjunction_Elimination [where \<phi>="\<psi>" and \<psi>="\<chi>" and \<chi>="\<phi>"]
        by blast
      hence "False" using assms by simp 
    }
    hence "\<psi> \<in> \<Omega> \<or> \<chi> \<in> \<Omega>" by blast      
  }
  moreover
  {
    assume "\<psi> \<in> \<Omega> \<or> \<chi> \<in> \<Omega>"
    hence "(\<psi> \<squnion> \<chi>) \<in> \<Omega>"
      using assms 
            Formula_Maximally_Consistent_Set_reflection 
            Disjunction_Left_Introduction 
            Disjunction_Right_Introduction 
            set_deduction_modus_ponens 
            set_deduction_weaken 
      by blast
  }
  ultimately show "(\<psi> \<squnion> \<chi>) \<in> \<Omega> \<equiv> \<psi> \<in> \<Omega> \<or> \<chi> \<in> \<Omega>"
    by linarith 
qed

lemma (in Intuitionistic_Logic) Formula_Maximally_Consistent_Set_verum:
  assumes "\<phi>-MCS \<Omega>"
  shows "\<top> \<in> \<Omega>"
  using assms 
        Formula_Maximally_Consistent_Set_reflection 
        Modus_Ponens 
        Verum_Rule 
        set_deduction_weaken 
  by blast

lemma (in Intuitionistic_Logic) Formula_Maximally_Consistent_Set_falsum:
  assumes "\<phi>-MCS \<Omega>"
  shows "\<bottom> \<notin> \<Omega>"
  by (metis assms 
            insert_Diff 
            Ex_Falso_Quodlibet 
            Formula_Consistent_def 
            Formula_Maximally_Consistent_Set_def 
            set_deduction_theorem 
            set_deduction_weaken)

lemma (in Intuitionistic_Logic) Formula_Maximally_Consistent_Set_negation:
  assumes "\<phi>-MCS \<Omega>"
  shows "\<psi> \<rightarrow> \<bottom> \<in> \<Omega> \<equiv> \<sim> \<psi> \<in> \<Omega>"
  by (smt assms 
          Formula_Maximally_Consistent_Set_reflection 
          Negation_Elimination 
          Negation_Introduction 
          set_deduction_modus_ponens 
          set_deduction_weaken)

theorem (in Intuitionistic_Logic) Formula_Maximally_Consistent_Set_biconditional_elimination:
  assumes "\<phi>-MCS \<Omega>"
  shows "(\<psi> \<leftrightarrow> \<chi>) \<in> \<Omega> \<Longrightarrow> \<psi> \<in> \<Omega> \<longleftrightarrow> \<chi> \<in> \<Omega>"
  by (meson assms 
            Formula_Maximally_Consistent_Set_implication_elimination 
            Formula_Maximally_Consistent_Set_reflection 
            Biconditional_Left_Elimination 
            Biconditional_Right_Elimination 
            set_deduction_weaken)
        
theorem (in Extended_Boolean_Propositional_Logic) Formula_Maximally_Consistent_Set_biconditional:
  assumes "\<phi>-MCS \<Omega>"
  shows "(\<psi> \<leftrightarrow> \<chi>) \<in> \<Omega> \<equiv> \<psi> \<in> \<Omega> \<longleftrightarrow> \<chi> \<in> \<Omega>"   
proof -
  {
    assume "\<psi> \<in> \<Omega> \<longleftrightarrow> \<chi> \<in> \<Omega>"
    hence "(\<psi> \<leftrightarrow> \<chi>) \<in> \<Omega>"
      by (meson assms 
                Biconditional_Introduction [where \<phi>="\<psi>" and \<psi>="\<chi>"] 
                Formula_Maximally_Consistent_Set_reflection [where \<Gamma>="\<Omega>"]
                Formula_Maximally_Consistent_Set_implication
                set_deduction_weaken) 
  }
  thus "(\<psi> \<leftrightarrow> \<chi>) \<in> \<Omega> \<equiv> \<psi> \<in> \<Omega> \<longleftrightarrow> \<chi> \<in> \<Omega>"
    using assms 
          Formula_Maximally_Consistent_Set_biconditional_elimination
    by smt
qed
        
end
