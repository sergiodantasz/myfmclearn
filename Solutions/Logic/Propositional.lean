set_option pp.parens true

variable (P Q R : Prop)


------------------------------------------------
-- Double negation
------------------------------------------------

-- x1.1
theorem doubleneg_intro : P → ¬¬P := by
  intro p
  intro np
  have c : False := np p
  exact c

-- x1.2
theorem doubleneg_elim : ¬¬P → P := by
  intro nnp
  have np : ¬ P := by
    intro p
    sorry
  sorry

theorem doubleneg_law : ¬¬P ↔ P := by
  constructor
  . intro nnp
    sorry
  . intro p
    intro np
    have c : False := np p
    exact c


------------------------------------------------
-- Commutativity of ∨,∧
------------------------------------------------

-- x2.1
theorem disj_comm : (P ∨ Q) → (Q ∨ P) := by
  intro pvq
  rcases pvq with p | q
  . right
    exact p
  . left
    exact q

-- x2.2
theorem conj_comm : (P ∧ Q) → (Q ∧ P) := by
  intro peq
  rcases peq with ⟨p, q⟩
  constructor
  . exact q
  . exact p


------------------------------------------------
-- Interdefinability of →,∨
------------------------------------------------

-- x3.2
theorem impl_as_disj_converse : (¬P ∨ Q) → (P → Q) := by
  intro h p
  rcases h with np | q
  . have c : False := np p
    contradiction
  . exact q

-- x3.3
theorem disj_as_impl : (P ∨ Q) → (¬P → Q) := by
  intro h np
  rcases h with p | q
  . have c : False := np p
    contradiction
  . exact q


------------------------------------------------
-- Contrapositive
------------------------------------------------

-- x4.1
theorem impl_as_contrapositive : (P → Q) → (¬Q → ¬P) := by
  intro pq nq p
  have q : Q := pq p
  have c : False := nq q
  contradiction

-- x4.2
theorem impl_as_contrapositive_converse : (¬Q → ¬P) → (P → Q) := by
  intro qp p
  by_cases h : Q
  . assumption
  . have np : ¬P := qp h
    have c : False := np p
    contradiction

theorem contrapositive_law : (P → Q) ↔ (¬Q → ¬P) := by
  constructor
  . intro pq nq p
    have q : Q := pq p
    have c : False := nq q
    contradiction
  . intro qp p
    by_cases h : Q
    . assumption
    . have np : ¬P := qp h
      have c : False := np p
      contradiction
