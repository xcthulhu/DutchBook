theory Extended_Classical_Propositional_Soundness_And_Completeness
  imports Intuitionistic_Logic
begin

datatype 'a Extended_Classical_Propositional_Formula =
      Falsum                                            ("\<^bold>\<bottom>")
    | Verum                                             ("\<^bold>\<top>")
    | Proposition 'a
    | Negation "'a Extended_Classical_Propositional_Formula"      ("\<^bold>\<sim>")
    | Conjunction "'a Extended_Classical_Propositional_Formula" 
                  "'a Extended_Classical_Propositional_Formula"   (infixr "\<^bold>\<sqinter>" 67)
    | Disjunction "'a Extended_Classical_Propositional_Formula"
                  "'a Extended_Classical_Propositional_Formula"   (infixr "\<^bold>\<squnion>" 68)
    | Implication "'a Extended_Classical_Propositional_Formula" 
                  "'a Extended_Classical_Propositional_Formula"   (infixr "\<^bold>\<rightarrow>" 70)
    | Biconditional "'a Extended_Classical_Propositional_Formula" 
                    "'a Extended_Classical_Propositional_Formula" (infixr "\<^bold>\<leftrightarrow>" 75)
                  
named_theorems Extended_Classical_Propositional_Calculus 
               "Rules for the Extended Propositional Calculus"
                  
inductive Extended_Classical_Propositional_Calculus 
          :: "'a Extended_Classical_Propositional_Formula \<Rightarrow> bool"  ("\<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P _" [60] 55)
  where
       Axiom_1 [Extended_Classical_Propositional_Calculus]: 
         "\<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<^bold>\<rightarrow> \<psi> \<^bold>\<rightarrow> \<phi>"
    |  Axiom_2 [Extended_Classical_Propositional_Calculus]: 
         "\<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P (\<phi> \<^bold>\<rightarrow> \<psi> \<^bold>\<rightarrow> \<chi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> \<phi> \<^bold>\<rightarrow> \<chi>"
    |  Double_Negation [Extended_Classical_Propositional_Calculus]: 
         "\<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P ((\<phi> \<^bold>\<rightarrow> \<^bold>\<bottom>) \<^bold>\<rightarrow> \<^bold>\<bottom>) \<^bold>\<rightarrow> \<phi>"
    |  Conjunction_Introduction [Extended_Classical_Propositional_Calculus]: 
         "\<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<^bold>\<rightarrow> \<psi> \<^bold>\<rightarrow> (\<phi> \<^bold>\<sqinter> \<psi>)"
    |  Conjunction_Left_Elimination [Extended_Classical_Propositional_Calculus]: 
         "\<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P (\<phi> \<^bold>\<sqinter> \<psi>) \<^bold>\<rightarrow> \<phi>"
    |  Conjunction_Right_Elimination [Extended_Classical_Propositional_Calculus]: 
         "\<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P (\<phi> \<^bold>\<sqinter> \<psi>) \<^bold>\<rightarrow> \<psi>"
    |  Disjunction_Elimination [Extended_Classical_Propositional_Calculus]: 
         "\<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P (\<phi> \<^bold>\<rightarrow> \<chi>) \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<chi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<squnion> \<psi>) \<^bold>\<rightarrow> \<chi>"
    |  Disjunction_Left_Introduction [Extended_Classical_Propositional_Calculus]: 
         "\<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<^bold>\<rightarrow> (\<phi> \<^bold>\<squnion> \<psi>)"
    |  Disjunction_Right_Introduction [Extended_Classical_Propositional_Calculus]: 
         "\<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<psi> \<^bold>\<rightarrow> (\<phi> \<^bold>\<squnion> \<psi>)"
    |  Negation_Introduction [Extended_Classical_Propositional_Calculus]: 
         "\<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P (\<phi> \<^bold>\<rightarrow> \<^bold>\<bottom>) \<^bold>\<rightarrow> \<^bold>\<sim> \<phi>"
    |  Negation_Elimination [Extended_Classical_Propositional_Calculus]: 
         "\<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<^bold>\<sim> \<phi> \<^bold>\<rightarrow> \<phi> \<^bold>\<rightarrow> \<^bold>\<bottom>"
    |  Verum_Rule [Extended_Classical_Propositional_Calculus]: 
         "\<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<^bold>\<rightarrow> \<^bold>\<top>"
    |  Modus_Ponens [Extended_Classical_Propositional_Calculus]: 
         "\<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<^bold>\<rightarrow> \<psi> \<Longrightarrow> \<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<Longrightarrow> \<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<psi>"
    |  Biconditional_Introduction [Extended_Classical_Propositional_Calculus]: 
        "\<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P (\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<phi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<leftrightarrow> \<psi>)"
    |  Biconditional_Left_Elimination [Extended_Classical_Propositional_Calculus]: 
        "\<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P (\<phi> \<^bold>\<leftrightarrow> \<psi>) \<^bold>\<rightarrow> \<phi> \<^bold>\<rightarrow> \<psi>"
    |  Biconditional_Right_Elimination [Extended_Classical_Propositional_Calculus]: 
        "\<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P (\<phi> \<^bold>\<leftrightarrow> \<psi>) \<^bold>\<rightarrow> \<psi> \<^bold>\<rightarrow> \<phi>"

instantiation Extended_Classical_Propositional_Formula :: (type) Extended_Classical_Propositional_Logic
begin
definition [simp]: "\<bottom> = \<^bold>\<bottom>"
definition [simp]: "\<turnstile> \<phi> = \<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi>"
definition [simp]: "\<phi> \<rightarrow> \<psi> = \<phi> \<^bold>\<rightarrow> \<psi>"
definition [simp]: "\<phi> \<leftrightarrow> \<psi> = \<phi> \<^bold>\<leftrightarrow> \<psi>"
definition [simp]: "\<top> = \<^bold>\<top>"
definition [simp]: "\<sim> = \<^bold>\<sim>"
definition [simp]: "(op \<sqinter>) = (op \<^bold>\<sqinter>)"
definition [simp]: "(op \<squnion>) = (op \<^bold>\<squnion>)"
instance 
by standard ((simp add: Extended_Classical_Propositional_Calculus)+, 
             meson Extended_Classical_Propositional_Calculus) 
end

primrec Extended_Classical_Propositional_Semantics :: 
  "'a set \<Rightarrow> 'a Extended_Classical_Propositional_Formula \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P" 65)
  where
       "\<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P Proposition p = (p \<in> \<MM>)"
    |  "\<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<^bold>\<rightarrow> \<psi> = (\<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<longrightarrow> \<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<psi>)"
    |  "\<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<^bold>\<bottom> = False"
    |  "\<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<^bold>\<top> = True"
    |  "\<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<^bold>\<sim> \<phi> = (~ \<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi>)"
    |  "\<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<^bold>\<sqinter> \<psi> = (\<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<and>  \<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<psi>)"
    |  "\<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<^bold>\<squnion> \<psi> = (\<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<or>  \<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<psi>)"
    |  "\<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<^bold>\<leftrightarrow> \<psi> = (\<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<longleftrightarrow> \<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<psi>)"
      
theorem Extended_Classical_Propositional_Calculus_Soundness:
  "\<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<Longrightarrow> \<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi>"
  by (induct rule: Extended_Classical_Propositional_Calculus.induct, simp+, blast, simp+)
  
definition Strong_Extended_Classical_Propositional_Deduction :: 
  "'a Extended_Classical_Propositional_Formula set \<Rightarrow> 'a Extended_Classical_Propositional_Formula \<Rightarrow> bool"  
  (infix "\<tturnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P" 65)
  where
    [simp]: "\<Gamma> \<tturnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<equiv> \<Gamma> \<tturnstile> \<phi>"
  
definition Strong_Extended_Classical_Propositional_Models ::
  "'a Extended_Classical_Propositional_Formula set \<Rightarrow> 'a Extended_Classical_Propositional_Formula \<Rightarrow> bool"  
  (infix "\<TTurnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P" 65)
  where
    [simp]: "\<Gamma> \<TTurnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<equiv> \<forall> \<MM>.(\<forall> \<gamma> \<in> \<Gamma>. \<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<gamma>) \<longrightarrow> \<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi>"
    
definition Extended_Theory_Propositions :: 
  "'a Extended_Classical_Propositional_Formula set \<Rightarrow> 'a set" ("\<^bold>\<lbrace> _ \<^bold>\<rbrace>" [50])
  where
    [simp]: "\<^bold>\<lbrace> \<Gamma> \<^bold>\<rbrace> = {p . \<Gamma> \<tturnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P Proposition p}"

lemma Truth_Lemma:
  assumes "MCS \<Gamma>"
  shows "\<Gamma> \<tturnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<equiv> \<^bold>\<lbrace> \<Gamma> \<^bold>\<rbrace> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi>"
  unfolding Strong_Extended_Classical_Propositional_Deduction_def
proof (induct \<phi>)
  case Falsum
  then show ?case using assms by auto 
next
  case Verum
  then show ?case
    by (metis assms
              Extended_Classical_Propositional_Semantics.simps(4) [where \<MM>="\<^bold>\<lbrace> \<Gamma> \<^bold>\<rbrace>"]
              Formula_Maximal_Consistency 
              Formula_Maximally_Consistent_Set_verum  
              set_deduction_reflection 
              verum_Extended_Classical_Propositional_Formula_def)
next
  case Proposition
  then show ?case by simp
next
  case Implication
  then show ?case
    by (metis assms
              Maximally_Consistent_Set_def
              Formula_Maximally_Consistent_Set_implication 
              Extended_Classical_Propositional_Semantics.simps(2) [where \<MM>="\<^bold>\<lbrace> \<Gamma> \<^bold>\<rbrace>"]
              implication_Extended_Classical_Propositional_Formula_def 
              set_deduction_modus_ponens 
              set_deduction_reflection) 
next
  case Negation
  then show ?case
    by (metis assms
              Extended_Classical_Propositional_Semantics.simps(5) [where \<MM>="\<^bold>\<lbrace> \<Gamma> \<^bold>\<rbrace>"]
              Formula_Maximally_Consistent_Set_falsum 
              Formula_Maximally_Consistent_Set_negation 
              Formula_Maximally_Consistent_Set_reflection [where \<phi>="\<bottom>" and \<Gamma>="\<Gamma>"]
              Maximally_Consistent_Set_def 
              Formula_Maximally_Consistent_Set_implication 
              negation_Extended_Classical_Propositional_Formula_def)
next
  case Conjunction
  then show ?case
    by (metis assms
              Extended_Classical_Propositional_Semantics.simps(6) [where \<MM>="\<^bold>\<lbrace> \<Gamma> \<^bold>\<rbrace>"]
              Formula_Maximally_Consistent_Set_conjunction 
              Formula_Maximally_Consistent_Set_reflection [where \<phi>="\<bottom>" and \<Gamma>="\<Gamma>"]
              Maximally_Consistent_Set_def 
              conjunction_Extended_Classical_Propositional_Formula_def)
next
  case Disjunction
  then show ?case
    by (metis assms 
              Extended_Classical_Propositional_Semantics.simps(7) [where \<MM>="\<^bold>\<lbrace> \<Gamma> \<^bold>\<rbrace>"] 
              Formula_Maximally_Consistent_Set_disjunction 
              Formula_Maximally_Consistent_Set_reflection [where \<phi>="\<bottom>" and \<Gamma>="\<Gamma>"] 
              Maximally_Consistent_Set_def 
              disjunction_Extended_Classical_Propositional_Formula_def)
next
  case (Biconditional \<phi> \<psi>)
  then show ?case
    using assms
          Extended_Classical_Propositional_Semantics.simps(8) [where \<MM>="\<^bold>\<lbrace> \<Gamma> \<^bold>\<rbrace>"]
          Maximally_Consistent_Set_def
          Formula_Maximally_Consistent_Set_biconditional [where \<Omega>="\<Gamma>"]
          Formula_Maximally_Consistent_Set_reflection [where \<phi>="\<bottom>" and \<Gamma>="\<Gamma>"]
    unfolding biconditional_Extended_Classical_Propositional_Formula_def
    by blast
qed

theorem Extended_Classical_Propositional_Calculus_Strong_Soundness_And_Completeness:
  "\<Gamma> \<tturnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<equiv> \<Gamma> \<TTurnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi>"
proof -
  have soundness: "\<Gamma> \<tturnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<Longrightarrow> \<Gamma> \<TTurnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi>" 
  proof -
    assume "\<Gamma> \<tturnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi>"
    from this obtain \<Gamma>' where \<Gamma>': "set \<Gamma>' \<subseteq> \<Gamma>" "\<Gamma>' :\<turnstile> \<phi>" by (simp add: set_deduction_def, blast)     
    {
      fix \<MM>
      assume "\<forall> \<gamma> \<in> \<Gamma>. \<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<gamma>"
      hence "\<forall> \<gamma> \<in> set \<Gamma>'. \<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<gamma>" using \<Gamma>'(1) by auto
      hence "\<forall> \<phi>. \<Gamma>' :\<turnstile> \<phi> \<longrightarrow> \<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi>"
      proof (induct \<Gamma>')
        case Nil
        then show ?case
          by (simp add: Extended_Classical_Propositional_Calculus_Soundness 
                        list_deduction_def) 
      next
        case (Cons \<psi> \<Gamma>')
        thus ?case using list_deduction_theorem by fastforce 
      qed
      with \<Gamma>'(2) have "\<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi>" by blast
    }
    thus "\<Gamma> \<TTurnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi>"
      using Strong_Extended_Classical_Propositional_Models_def by blast
  qed
  have completeness: "\<Gamma> \<TTurnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<Longrightarrow> \<Gamma> \<tturnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi>"
  proof (erule contrapos_pp)
    assume "~ \<Gamma> \<tturnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi>"
    hence "\<exists> \<MM>. (\<forall> \<gamma> \<in> \<Gamma>. \<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<gamma>) \<and> ~ \<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi>"
    proof -
      from \<open>~ \<Gamma> \<tturnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi>\<close> obtain \<Omega> where \<Omega>: "\<Gamma> \<subseteq> \<Omega>" "\<phi>-MCS \<Omega>"
        by (meson Formula_Consistent_def 
                  Formula_Maximally_Consistent_Extension 
                  Strong_Extended_Classical_Propositional_Deduction_def)
      hence "(\<phi> \<rightarrow> \<bottom>) \<in> \<Omega>"
        using Formula_Maximal_Consistent_Set_negation by blast
      hence "~ \<^bold>\<lbrace> \<Omega> \<^bold>\<rbrace> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi>"
        using \<Omega>
              Formula_Consistent_def 
              Formula_Maximal_Consistency 
              Formula_Maximally_Consistent_Set_def 
              Truth_Lemma 
        unfolding Strong_Extended_Classical_Propositional_Deduction_def
        by blast
      moreover have "\<forall> \<gamma> \<in> \<Gamma>. \<^bold>\<lbrace> \<Omega> \<^bold>\<rbrace> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<gamma>"
        using Formula_Maximal_Consistency Truth_Lemma \<Omega> set_deduction_reflection 
        unfolding Strong_Extended_Classical_Propositional_Deduction_def
        by blast  
      ultimately show ?thesis by auto
    qed
    thus "~ \<Gamma> \<TTurnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi>"
      unfolding Strong_Extended_Classical_Propositional_Models_def
      by simp
  qed
  from soundness completeness show "\<Gamma> \<tturnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<equiv> \<Gamma> \<TTurnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi>" by smt
qed

theorem Extended_Classical_Propositional_Calculus_Soundness_And_Completeness:
  "\<turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi> \<equiv> \<forall>\<MM>. \<MM> \<Turnstile>\<^sub>P\<^sub>R\<^sub>O\<^sub>P \<phi>"
  by (smt Extended_Classical_Propositional_Calculus_Strong_Soundness_And_Completeness 
          Extended_Classical_Propositional_Calculus_Soundness 
          Strong_Extended_Classical_Propositional_Deduction_def 
          Strong_Extended_Classical_Propositional_Models_def 
          proves_Extended_Classical_Propositional_Formula_def 
          set_deduction_base_theory)
        
end
