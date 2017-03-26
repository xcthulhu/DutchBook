theory Formula
imports Main
begin
  datatype 'a Formula = 
      Implies "'a Formula" "'a Formula"   (infixr "\<Rightarrow>" 70)
    | Atom 'a

end
