theory Formula
imports Main
begin
  datatype 'a Formula = 
      Falsum                              ("\<bottom>")
    | Implies "'a Formula" "'a Formula"   (infixr "\<rightarrow>" 70)
    | Atom 'a
end
