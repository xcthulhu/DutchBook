theory Simply_Typed_Free_SKCombinator
imports Main Free_SKCombinator "../../Logic/Formula"
begin
  inductive Simply_Typed_Free_SKCombinator :: "Free_SKCombinator \<Rightarrow> 'a Formula \<Rightarrow> bool" (infix "\<Colon>" 65)
  where
    S_type      : "S \<Colon> (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<chi>"
  | K_type      : "K \<Colon> \<phi> \<rightarrow> \<psi> \<rightarrow> \<phi>"
  | application : "E\<^sub>1 \<Colon> \<phi> \<rightarrow> \<psi> \<Longrightarrow> E\<^sub>2 \<Colon> \<phi> \<Longrightarrow> E\<^sub>1 \<bullet> E\<^sub>2 \<Colon> \<psi>"
end