set_option pp.parens true
set_option autoImplicit false

section A

/-
Basta demonstrar _.                       : Prop → Cmd
_ nasceu na capital de _.                 : Person ⨯ Country → Prop
Se João é _, então _ ∈ _.                 : (Person → Prop) ⨯ Person ⨯ Set Person → Prop
O computador de _ tem _ teclas quebradas. : Person ⨯ Nat → Prop
Para cada x : Set _, defina x' ≝ _.       : Type ⨯ (Set Int → Set Int) → Cmd
Seja x : _ tal que √2.                    : Type Error
_ ∈ {{√2}, {_, _}}.                       : Set Real ⨯ (Real ⨯ Real) → Prop
n ∣ m ⇐≝⇒ (∃_ : Int)[_].                  : Var ⨯ Prop → Cmd
n _ 42 ⇐⇒ _.                              : (Int ⨯ Int → Prop) ⨯ Prop → Prop
-/

end A

section B

-- B1
theorem conj_as_neg_disj (P Q : Prop) : P ∧ Q → ¬(¬P ∨ ¬Q) := by
  intro h' h''
  rcases h' with ⟨p, q⟩
  rcases h'' with np | nq
  . apply np
    assumption
  . apply nq
    assumption

end B
