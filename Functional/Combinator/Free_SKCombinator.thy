theory Free_SKCombinator
imports Main
begin
  datatype Free_SKCombinator = 
    S 
  | K    
  | Apply "Free_SKCombinator" "Free_SKCombinator"         (infixl "\<bullet>" 70)
end