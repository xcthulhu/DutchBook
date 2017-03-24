theory Formula
imports Main
begin
  datatype 'a Formula = 
      Falsum                              ("\<bottom>")
    | Implies "'a Formula" "'a Formula"   (infixr "\<rightarrow>" 70)
    | Atom 'a
  
fun List_Implies :: "('a Formula) list \<Rightarrow> 'a Formula \<Rightarrow> 'a Formula" (infix "\<mapsto>" 75)
  where
    "[] \<mapsto> \<psi> = \<psi>"
  | "(\<phi> # \<Phi>) \<mapsto> \<psi> = \<phi> \<rightarrow> (\<Phi> \<mapsto> \<psi>)"


end
