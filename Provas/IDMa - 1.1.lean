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
  · apply np
    assumption
  · apply nq
    assumption

-- B2
theorem curry_uncurry (P Q R : Prop) : (P ∧ Q → R) ↔ (P → (Q → R)) := by
  constructor
  · intro h p q
    have pq : P ∧ Q := by
      constructor
      · assumption
      · assumption
    apply h
    assumption
  · intro h pq
    rcases pq with ⟨p, q⟩
    have qr : Q → R := h p
    have r : R := qr q
    assumption

end B

section C

/-
Allowed tactics:

- Int.add_assoc             Int.mul_assoc
- Int.add_zero              Int.mul_one
- Int.add_comm              Int.mul_comm
- Int.add_right_neg         Int.add_mul
-/

-- Lemmas

theorem neg_neg (a : Int) : -(-a) = a := by
  calc
    -(-a) = -(-a) + 0             := by rw [Int.add_zero]
    _     = -(-a) + (a + (-a))    := by rw [Int.add_right_neg]
    _     = (-(-a) + a) + (-a)    := by rw [Int.add_assoc]
    _     = (a + (-(-a))) + (-a)  := by rw [Int.add_comm a (-(-a))]
    _     = a + (-(-a) + (-a))    := by rw [Int.add_assoc]
    _     = a + (-a + (-(-a)))    := by rw [Int.add_comm (-(-a)) (-a)]
    _     = a + 0                 := by rw [Int.add_right_neg]
    _     = a                     := by rw [Int.add_zero]

theorem add_right_cancel (c : Int) (x y : Int) : x + c = y + c → x = y := by
  intro h
  have h : (x + c) + (-c) = (y + c) + (-c) := congrArg (fun z => z + (-c)) h
  rw [Int.add_assoc, Int.add_assoc] at h
  rw [Int.add_right_neg] at h
  rw [Int.add_zero, Int.add_zero] at h
  exact h

theorem mul_zero (a : Int) : a * 0 = 0 := by
  calc
    a * 0 = a * 0 + 0                     := by rw [Int.add_zero]
    _     = a * 0 + (a * 0 + (-(a * 0)))  := by rw [Int.add_right_neg]
    _     = (a * 0 + a * 0) + (-(a * 0))  := by rw [Int.add_assoc]
    _     = (0 * a + 0 * a) + (-(a * 0))  := by rw [Int.mul_comm]
    _     = ((0 + 0) * a) + (-(a * 0))    := by rw [Int.add_mul]
    _     = 0 * a + (-(a * 0))            := by rw [Int.add_zero]
    _     = a * 0 + (-(a * 0))            := by rw [Int.mul_comm]
    _     = 0                             := by rw [Int.add_right_neg]

theorem neg_one_mul (a : Int) : (-1) * a = -a := by
  calc
    (-1) * a = (-1) * a + 0               := by rw [Int.add_zero]
    _        = (-1) * a + (a + (-a))      := by rw [Int.add_right_neg]
    _        = ((-1) * a + a) + (-a)      := by rw [Int.add_assoc]
    _        = ((-1) * a + a * 1) + (-a)  := by rw [Int.mul_one]
    _        = ((-1) * a + 1 * a) + (-a)  := by rw [Int.mul_comm a 1]
    _        = (((-1) + 1) * a) + (-a)    := by rw [Int.add_mul]
    _        = ((1 + (-1)) * a) + (-a)    := by rw [Int.add_comm 1 (-1)]
    _        = (0 * a) + (-a)             := by rw [Int.add_right_neg]
    _        = (a * 0) + (-a)             := by rw [Int.mul_comm]
    _        = 0 + (-a)                   := by rw [mul_zero]
    _        = (-a) + 0                   := by rw [Int.add_comm]
    _        = -a                         := by rw [Int.add_zero]

-- C2
theorem neg_sub (a b : Int) : -(a - b) = b - a := by
  calc
    -(a - b) = -(a + (-b))             := by rw [Int.sub_eq_add_neg]  -- Sugar
    _        = (-1) * (a + (-b))       := by rw [neg_one_mul]
    _        = (a + (-b)) * (-1)       := by rw [Int.mul_comm]
    _        = a * (-1) + (-b) * (-1)  := by rw [Int.add_mul]
    _        = (-1) * a + (-1) * (-b)  := by rw [Int.mul_comm a (-1), Int.mul_comm (-b) (-1)]
    _        = (-a) + (-(-b))          := by rw [neg_one_mul, neg_one_mul]
    _        = (-a) + b                := by rw [neg_neg]
    _        = b + (-a)                := by rw [Int.add_comm]
    _        = b - a                   := by rw [Int.sub_eq_add_neg]  -- Sugar

end C
