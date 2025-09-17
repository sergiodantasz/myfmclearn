set_option pp.parens true


------------------------------------------------


section propositional

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
  by_cases h : P
  . assumption
  . have c : False := nnp h
    contradiction

theorem doubleneg_law : ¬¬P ↔ P := by
  constructor
  . intro nnp
    by_cases h : P
    . assumption
    . have c : False := nnp h
      contradiction
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


------------------------------------------------
-- Irrefutability of LEM[P]
------------------------------------------------

-- x5.1
theorem lem_irrefutable : ¬¬(P ∨ ¬P)  := by
  intro h
  have o_lem : P ∨ ¬P := by
    right
    intro p
    have i_lem : P ∨ ¬P := by
      left
      assumption
    have c : False := h i_lem
    contradiction
  have c : False := h o_lem
  contradiction


------------------------------------------------
-- Peirce's law
------------------------------------------------

-- x6.2
theorem peirce_law_weak : ((P → Q) → P) → ¬¬P := by
  intro h np
  have pq : P → Q := by
    intro p
    have c : False := np p
    contradiction
  have p : P := h pq
  have c : False := np p
  contradiction


------------------------------------------------
-- Linearity of →
------------------------------------------------

theorem impl_linear : (P → Q) ∨ (Q → P) := by
  by_cases h : P
  . right
    intro q
    assumption
  . left
    intro p
    have c : False := h p
    contradiction


------------------------------------------------
-- Interdefinability of ∨,∧
------------------------------------------------

-- x7.1
theorem disj_as_negconj : P ∨ Q → ¬(¬P ∧ ¬Q) := by
  intro h' h''
  rcases h'' with ⟨np, nq⟩
  rcases h' with p | q
  . have c : False := np p
    contradiction
  . have c : False := nq q
    contradiction

-- x7.3
theorem conj_as_negdisj : P ∧ Q → ¬(¬P ∨ ¬Q) := by
  intro h' h''
  rcases h' with ⟨p, q⟩
  rcases h'' with np | nq
  . have c : False := np p
    contradiction
  . have c : False := nq q
    contradiction


------------------------------------------------
-- De Morgan laws for ∨,∧
------------------------------------------------

-- x8.1
theorem demorgan_disj : ¬(P ∨ Q) → (¬P ∧ ¬Q) := by
  intro h
  constructor
  . intro p
    have pq : P ∨ Q := by
      left
      exact p
    have c : False := h pq
    contradiction
  . intro q
    have pq : P ∨ Q := by
      right
      exact q
    have c : False := h pq
    contradiction

-- x8.2
theorem demorgan_disj_converse : (¬P ∧ ¬Q) → ¬(P ∨ Q) := by
  intro h' h''
  rcases h' with ⟨np, nq⟩
  rcases h'' with p | q
  . have c : False := np p
    contradiction
  . have c : False := nq q
    contradiction


-- x8.3
theorem demorgan_conj : ¬(P ∧ Q) → (¬Q ∨ ¬P) := by
  intro h
  by_cases hp : P
  . by_cases hq : Q
    . have pq : P ∧ Q := by
        constructor
        . assumption
        . assumption
      have c : False := h pq
      contradiction
    . left
      assumption
  . right
    assumption

-- x8.4
theorem demorgan_conj_converse : (¬Q ∨ ¬P) → ¬(P ∧ Q) := by
  intro h' h''
  rcases h'' with ⟨p, q⟩
  rcases h' with nq | np
  . have c : False := nq q
    contradiction
  . have c : False := np p
    contradiction

theorem demorgan_conj_law : ¬(P ∧ Q) ↔ (¬Q ∨ ¬P) := by
  constructor
  . intro h
    by_cases hp : P
    . by_cases hq : Q
      . have pq : P ∧ Q := by
          constructor
          . assumption
          . assumption
        have c : False := h pq
        contradiction
      . left
        assumption
    . right
      assumption
  . intro h' h''
    rcases h'' with ⟨p, q⟩
    rcases h' with nq | np
    . have c : False := nq q
      contradiction
    . have c : False := np p
      contradiction

theorem demorgan_disj_law : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  . intro h
    constructor
    . intro p
      have pq : P ∨ Q := by
        left
        exact p
      have c : False := h pq
      contradiction
    . intro q
      have pq : P ∨ Q := by
        right
        exact q
      have c : False := h pq
      contradiction
  . intro h' h''
    rcases h' with ⟨np, nq⟩
    rcases h'' with p | q
    . have c : False := np p
      contradiction
    . have c : False := nq q
      contradiction


------------------------------------------------
-- Distributivity laws between ∨,∧
------------------------------------------------

-- x9.1
theorem distr_conj_disj : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  intro h
  rcases h with ⟨p, qr⟩
  rcases qr with q | r
  . left
    constructor
    . assumption
    . assumption
  . right
    constructor
    . assumption
    . assumption

-- x9.2
theorem distr_conj_disj_converse : (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R) := by
  intro h
  rcases h with pq | pr
  . rcases pq with ⟨p, q⟩
    constructor
    . assumption
    . left
      assumption
  . rcases pr with ⟨p, r⟩
    constructor
    . assumption
    . right
      assumption

-- x9.3
theorem distr_disj_conj : P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R) := by
  intro h
  rcases h with p | qr
  . constructor
    . left
      assumption
    . left
      assumption
  . rcases qr with ⟨q, r⟩
    constructor
    . right
      assumption
    . right
      assumption

-- x9.4
theorem distr_disj_conj_converse : (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R) := by
  intro h
  rcases h with ⟨pq, pr⟩
  rcases pq with p | q
  . left
    assumption
  . rcases pr with p | r
    . left
      assumption
    . right
      constructor
      . assumption
      . assumption


------------------------------------------------
-- Currying
------------------------------------------------

-- x10.1
theorem curry_prop : ((P ∧ Q) → R) → (P → (Q → R)) := by
  intro pqr p q
  have pq : P ∧ Q := by
    constructor
    . assumption
    . assumption
  have r : R := pqr pq
  exact r

-- x10.2
theorem uncurry_prop : (P → (Q → R)) → ((P ∧ Q) → R) := by
  intro pqr pq
  rcases pq with ⟨p, q⟩
  have qr : Q → R := pqr p
  apply qr
  assumption


------------------------------------------------
-- Reflexivity of →
------------------------------------------------

-- x11.1
theorem impl_refl : P → P := by
  intro p
  exact p


------------------------------------------------
-- Weakening and contraction
------------------------------------------------

-- x12.1
theorem weaken_disj_right : P → (P ∨ Q) := by
  intro p
  left
  assumption

-- x12.2
theorem weaken_disj_left : Q → (P ∨ Q) := by
  intro q
  right
  assumption

-- x12.3
theorem weaken_conj_right : (P ∧ Q) → P := by
  intro pq
  rcases pq with ⟨p, q⟩
  assumption

-- x12.4
theorem weaken_conj_left : (P ∧ Q) → Q := by
  intro pq
  rcases pq with ⟨p, q⟩
  assumption


------------------------------------------------
-- Idempotence of ∨,∧
------------------------------------------------

theorem disj_idem : (P ∨ P) ↔ P := by
  constructor
  . intro pp
    rcases pp with p | p
    . assumption
    . assumption
  . intro p
    left
    assumption

theorem conj_idem : (P ∧ P) ↔ P := by
  constructor
  . intro pp
    rcases pp with ⟨p, p⟩
    assumption
  . intro p
    constructor
    . assumption
    . assumption


------------------------------------------------
-- Bottom, Top
------------------------------------------------

theorem false_bottom : False → P := by
  intro
  contradiction

theorem true_top : P → True  := by
  intro p
  trivial


end propositional


------------------------------------------------


section predicate

variable (U : Type)
variable (P Q : U → Prop)


------------------------------------------------
-- De Morgan laws for ∃,∀
------------------------------------------------

-- x13.3
theorem demorgan_exists : ¬(∃ x, P x) → (∀ x, ¬P x) := by
  intro h
  intro a
  intro pa
  have ep : ∃ x, P x := by
    exists a
  apply h ep

-- x13.4
theorem demorgan_exists_converse : (∀ x, ¬P x) → ¬(∃ x, P x) := by
  intro h' h''
  obtain ⟨a, pa⟩ := h''
  have npa : ¬P a := h' a
  apply npa pa

-- x13.1
theorem demorgan_forall : ¬(∀ x, P x) → (∃ x, ¬P x) := by
  intro h
  sorry

-- x13.2
theorem demorgan_forall_converse : (∃ x, ¬P x) → ¬(∀ x, P x) := by
  intro h' h''
  obtain ⟨a, npa⟩ := h'
  have pa : P a := h'' a
  apply npa pa

theorem demorgan_forall_law : ¬(∀ x, P x) ↔ (∃ x, ¬P x) := by
  constructor
  . intro h
    sorry
  . intro h' h''
    obtain ⟨a, npa⟩ := h'
    have pa : P a := h'' a
    apply npa pa

theorem demorgan_exists_law : ¬(∃ x, P x) ↔ (∀ x, ¬P x) := by
  constructor
  . intro h
    intro a
    intro pa
    have ep : ∃ x, P x := by
      exists a
    apply h ep
  . intro h' h''
    obtain ⟨a, pa⟩ := h''
    have npa : ¬P a := h' a
    apply npa pa


------------------------------------------------
-- Interdefinability of ∃,∀
------------------------------------------------

-- x14.1
theorem exists_as_neg_forall : (∃ x, P x) → ¬(∀ x, ¬P x) := by
  intro h' h''
  obtain ⟨a, pa⟩ := h'
  have npa : ¬P a := h'' a
  have c : False := npa pa
  assumption

-- x14.3
theorem forall_as_neg_exists : (∀ x, P x) → ¬(∃ x, ¬P x) := by
  intro h' h''
  obtain ⟨a, npa⟩ := h''
  have pa : P a := h' a
  apply npa pa

-- x14.4
theorem forall_as_neg_exists_converse : ¬(∃ x, ¬P x) → (∀ x, P x) := by
  sorry

-- x14.2
theorem exists_as_neg_forall_converse : ¬(∀ x, ¬P x) → (∃ x, P x) := by
  sorry

theorem forall_as_neg_exists_law : (∀ x, P x) ↔ ¬(∃ x, ¬P x) := by
  sorry

theorem exists_as_neg_forall_law : (∃ x, P x) ↔ ¬(∀ x, ¬P x) := by
  sorry


end predicate


------------------------------------------------
