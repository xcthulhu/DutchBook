theory Classical
imports Main "../Formula" ImplicationalIntuitionistic
begin
        
inductive classical_proof :: "'a Formula \<Rightarrow> bool" ("\<turnstile>\<^sub>C\<^sub>L _" [60] 55)
  where
    S_axiom        : "\<turnstile>\<^sub>C\<^sub>L (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<chi>"
  | K_axiom        : "\<turnstile>\<^sub>C\<^sub>L \<phi> \<rightarrow> \<psi> \<rightarrow> \<phi>"
  | contraposition : "\<turnstile>\<^sub>C\<^sub>L ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> (\<psi> \<rightarrow> \<bottom>)) \<rightarrow> \<psi> \<rightarrow> \<phi>"
  | modus_ponens   : "\<turnstile>\<^sub>C\<^sub>L \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<turnstile>\<^sub>C\<^sub>L \<phi> \<Longrightarrow> \<turnstile>\<^sub>C\<^sub>L \<psi>"
    
lemma intuitionistic_subsystem: "\<turnstile>\<^sub>I\<^sub>I\<^sub>L \<phi> \<Longrightarrow> \<turnstile>\<^sub>C\<^sub>L \<phi>"
proof (induct rule: iil_proof.induct)
  case S_axiom thus ?case by (simp add: classical_proof.S_axiom)
  next case K_axiom thus ?case by (simp add: classical_proof.K_axiom)
  next case modus_ponens thus ?case by (simp add: classical_proof.modus_ponens)
qed

