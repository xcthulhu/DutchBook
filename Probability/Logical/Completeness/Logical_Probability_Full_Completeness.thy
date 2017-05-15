theory Logical_Probability_Full_Completeness
  imports "../Weakly_Additive/Weakly_Additive_Logical_Probability"
begin
  
primrec (in Classical_Propositional_Logic) 
  stratified_deduction :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool" ("_ #\<turnstile> _ _" [60,100,59] 60)
  where
    "\<Gamma> #\<turnstile> 0 \<phi> = True"
  | "\<Gamma> #\<turnstile> (Suc n) \<phi> = (\<exists> \<Psi>. mset \<Psi> \<subseteq># mset \<Gamma> \<and> 
                             \<Psi> :\<turnstile> \<phi> \<and> 
                             (\<Gamma> \<ominus> \<Psi>) @ [\<psi> \<squnion> (\<sim> \<phi>). \<psi> \<leftarrow> \<Psi>] #\<turnstile> n \<phi>)"
    
primrec (in Classical_Propositional_Logic) 
  dutch_book_deduction :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" ("_ $\<turnstile> _" [60,100] 60)
  where
    "\<Gamma> $\<turnstile> [] = True"
  | "\<Gamma> $\<turnstile> (\<phi> # \<Phi>) = (\<exists> \<Psi>. mset \<Psi> \<subseteq># mset \<Gamma> \<and> 
                           \<Psi> :\<turnstile> \<phi> \<and> 
                           (\<Gamma> \<ominus> \<Psi>) @ [\<psi> \<squnion> (\<sim> \<phi>). \<psi> \<leftarrow> \<Psi>] $\<turnstile> \<Phi>)"

lemma (in Classical_Propositional_Logic) stratified_dutch_book_deduction_replicate:
  "\<Gamma> #\<turnstile> n \<phi> = \<Gamma> $\<turnstile> (replicate n \<phi>)"
proof -
  have "\<forall> \<Gamma>. \<Gamma> #\<turnstile> n \<phi> = \<Gamma> $\<turnstile> (replicate n \<phi>)"
    by (induct n, simp+)
  thus ?thesis by blast
qed

lemma (in Classical_Propositional_Logic) conj_cons_list_deduction [simp]:
  "(\<phi> \<sqinter> \<psi>) # \<Phi> :\<turnstile> \<chi> = \<phi> # \<psi> # \<Phi> :\<turnstile> \<chi>"
  sorry

lemma (in Classical_Propositional_Logic) subtr_cons_list_deduction [simp]:
  "(\<phi> \<setminus> \<psi>) # \<Phi> :\<turnstile> \<chi> = \<phi> # (\<sim> \<psi>) # \<Phi> :\<turnstile> \<chi>"
  unfolding subtraction_def
  by simp

lemma (in Classical_Propositional_Logic) intuitionistic_demorgans:
  "\<turnstile> \<sim>(a \<sqinter> b) \<leftrightarrow> (\<sim>a \<squnion> \<sim>b)"
  sorry
    
lemma (in Weakly_Additive_Logical_Probability)
  "2 * Pr p \<le> Pr (\<sim>(a \<sqinter> (b \<rightarrow> (\<sim> p)))) + 
              Pr (\<sim>(b \<sqinter> (a \<rightarrow> (\<sim> p)))) + 
              Pr (\<sim>((a \<rightarrow> (\<sim> p)) \<sqinter> (b \<rightarrow> (\<sim> p))))"
proof -
  have "\<turnstile> \<sim>(a \<sqinter> (b \<rightarrow> (\<sim> p))) \<leftrightarrow> (\<sim>a \<squnion> \<sim>(b \<rightarrow> (\<sim> p)))"
       "\<turnstile> \<sim>(b \<sqinter> (a \<rightarrow> (\<sim> p))) \<leftrightarrow> (\<sim>b \<squnion> \<sim>(a \<rightarrow> (\<sim> p)))"
       "\<turnstile> \<sim>((a \<rightarrow> (\<sim> p)) \<sqinter> (b \<rightarrow> (\<sim> p))) \<leftrightarrow>
          (\<sim>(a \<rightarrow> (\<sim> p)) \<squnion> \<sim> (b \<rightarrow> (\<sim> p)))"
    by (simp add: intuitionistic_demorgans)+
  moreover have "\<turnstile> \<sim>(b \<rightarrow> (\<sim> p)) \<leftrightarrow> (b \<sqinter> p)"
                "\<turnstile> \<sim>(a \<rightarrow> (\<sim> p)) \<leftrightarrow> (a \<sqinter> p)"
    by (simp add: biconditional_def, 
        simp add: conjunction_def 
                  negation_def 
                  The_Principle_of_Pseudo_Scotus)+ 
  ultimately have "\<turnstile> \<sim>(a \<sqinter> (b \<rightarrow> (\<sim> p))) \<leftrightarrow> (\<sim>a \<squnion> (b \<sqinter> p))"
                  "\<turnstile> \<sim>(b \<sqinter> (a \<rightarrow> (\<sim> p))) \<leftrightarrow> (\<sim>b \<squnion> (a \<sqinter> p))"
                  "\<turnstile> \<sim>((a \<rightarrow> (\<sim> p)) \<sqinter> (b \<rightarrow> (\<sim> p))) \<leftrightarrow>
                       ((a \<sqinter> p) \<squnion> (b \<sqinter> p))"
    by (simp add: conjunction_def negation_def)+
  hence 
    "Pr (\<sim>(a \<sqinter> (b \<rightarrow> (\<sim> p)))) + 
     Pr (\<sim>(b \<sqinter> (a \<rightarrow> (\<sim> p)))) + 
     Pr (\<sim>((a \<rightarrow> (\<sim> p)) \<sqinter> (b \<rightarrow> (\<sim> p))))
              =  
     Pr (\<sim>a \<squnion> (b \<sqinter> p)) + 
     Pr (\<sim>b \<squnion> (a \<sqinter> p)) + 
     Pr ((a \<sqinter> p) \<squnion> (b \<sqinter> p))"
    using biconditional_equivalence by auto  
  

  (*
lemma (in Classical_Propositional_Logic)
  "[a \<sqinter> (b \<rightarrow> p), b \<sqinter> (a \<rightarrow> p), (a \<rightarrow> p) \<sqinter> (b \<rightarrow> p)] #\<turnstile> 2 p"
  (is "[?X, ?Y, ?Z] #\<turnstile> 2 _")
proof -
  have "[?Y, ?Z] :\<turnstile> p"
  proof -
    let ?\<Gamma> = "[a \<rightarrow> p, b \<rightarrow> p, b, a \<rightarrow> p]"
    have "[?Y, ?Z] :\<turnstile> p = [b, a \<rightarrow> p, ?Z] :\<turnstile> p" by simp
    moreover have "set [b, a \<rightarrow> p, ?Z] = set [?Z, b, a \<rightarrow> p]" by fastforce
    ultimately have "[?Y, ?Z] :\<turnstile> p = [?Z, b, a \<rightarrow> p] :\<turnstile> p"
      by (smt insert_subset list.simps(15) list_deduction_monotonic set_subset_Cons)
    hence "[?Y, ?Z] :\<turnstile> p = ?\<Gamma> :\<turnstile> p" by simp
    moreover have "?\<Gamma> :\<turnstile> b" "?\<Gamma> :\<turnstile> b \<rightarrow> p"
      by (simp add: list_deduction_reflection)+
    hence "?\<Gamma> :\<turnstile> p" using list_deduction_modus_ponens by blast
    ultimately show "[?Y, ?Z] :\<turnstile> p" by simp
  qed
  moreover have "[?X, ?Y \<setminus> p, ?Z \<setminus> p] :\<turnstile> p"
    *)