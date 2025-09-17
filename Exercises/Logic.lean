section propositional

variable (P Q R : Prop)


------------------------------------------------
-- Double negation
------------------------------------------------

theorem doubleneg_intro :  -- Proved
  P → ¬ ¬ P  := by
  sorry

theorem doubleneg_elim :  -- Proved
  ¬ ¬ P → P  := by
  sorry

theorem doubleneg_law :  -- Proved
  ¬ ¬ P ↔ P  := by
  sorry


------------------------------------------------
-- Commutativity of ∨,∧
------------------------------------------------

theorem disj_comm :  -- Proved
  (P ∨ Q) → (Q ∨ P)  := by
  sorry

theorem conj_comm :  -- Proved
  (P ∧ Q) → (Q ∧ P)  := by
  sorry


------------------------------------------------
-- Interdefinability of →,∨
------------------------------------------------

theorem impl_as_disj_converse :  -- Proved
  (¬ P ∨ Q) → (P → Q)  := by
  sorry

theorem disj_as_impl :  -- Proved
  (P ∨ Q) → (¬ P → Q)  := by
  sorry


------------------------------------------------
-- Contrapositive
------------------------------------------------

theorem impl_as_contrapositive :  -- Proved
  (P → Q) → (¬ Q → ¬ P)  := by
  sorry

theorem impl_as_contrapositive_converse :  -- Proved
  (¬ Q → ¬ P) → (P → Q)  := by
  sorry

theorem contrapositive_law :  -- Proved
  (P → Q) ↔ (¬ Q → ¬ P)  := by
  sorry


------------------------------------------------
-- Irrefutability of LEM[P]
------------------------------------------------

theorem lem_irrefutable :  -- Proved
  ¬ ¬ (P ∨ ¬ P)  := by
  sorry


------------------------------------------------
-- Peirce's law
------------------------------------------------

theorem peirce_law_weak :  -- Proved
  ((P → Q) → P) → ¬ ¬ P  := by
  sorry


------------------------------------------------
-- Linearity of →
------------------------------------------------

theorem impl_linear :  -- Proved
  (P → Q) ∨ (Q → P)  := by
  sorry


------------------------------------------------
-- Interdefinability of ∨,∧
------------------------------------------------

theorem disj_as_negconj :  -- Proved
  P ∨ Q → ¬ (¬ P ∧ ¬ Q)  := by
  sorry

theorem conj_as_negdisj :  -- Proved
  P ∧ Q → ¬ (¬ P ∨ ¬ Q)  := by
  sorry


------------------------------------------------
-- De Morgan laws for ∨,∧
------------------------------------------------

theorem demorgan_disj :  -- Proved
  ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)  := by
  sorry

theorem demorgan_disj_converse :  -- Proved
  (¬ P ∧ ¬ Q) → ¬ (P ∨ Q)  := by
  sorry

theorem demorgan_conj :  -- Proved
  ¬ (P ∧ Q) → (¬ Q ∨ ¬ P)  := by
  sorry

theorem demorgan_conj_converse :  -- Proved
  (¬ Q ∨ ¬ P) → ¬ (P ∧ Q)  := by
  sorry

theorem demorgan_conj_law :  -- Proved
  ¬ (P ∧ Q) ↔ (¬ Q ∨ ¬ P)  := by
  sorry

theorem demorgan_disj_law :  -- Proved
  ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)  := by
  sorry


------------------------------------------------
-- Distributivity laws between ∨,∧
------------------------------------------------

theorem distr_conj_disj :  -- Proved
  P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  := by
  sorry

theorem distr_conj_disj_converse :  -- Proved
  (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  := by
  sorry

theorem distr_disj_conj :  -- Proved
  P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  := by
  sorry

theorem distr_disj_conj_converse :  -- Proved
  (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  := by
  sorry


------------------------------------------------
-- Currying
------------------------------------------------

theorem curry_prop :  -- Proved
  ((P ∧ Q) → R) → (P → (Q → R))  := by
  sorry

theorem uncurry_prop :  -- Proved
  (P → (Q → R)) → ((P ∧ Q) → R)  := by
  sorry


------------------------------------------------
-- Reflexivity of →
------------------------------------------------

theorem impl_refl :  -- Proved
  P → P  := by
  sorry


------------------------------------------------
-- Weakening and contraction
------------------------------------------------

theorem weaken_disj_right :  -- Proved
  P → (P ∨ Q)  := by
  sorry

theorem weaken_disj_left :  -- Proved
  Q → (P ∨ Q)  := by
  sorry

theorem weaken_conj_right :  -- Proved
  (P ∧ Q) → P  := by
  sorry

theorem weaken_conj_left :  -- Proved
  (P ∧ Q) → Q  := by
  sorry


------------------------------------------------
-- Idempotence of ∨,∧
------------------------------------------------

theorem disj_idem :  -- Proved
  (P ∨ P) ↔ P  := by
  sorry

theorem conj_idem :  -- Proved
  (P ∧ P) ↔ P := by
  sorry


------------------------------------------------
-- Bottom, Top
------------------------------------------------

theorem false_bottom :  -- Proved
  False → P := by
  sorry

theorem true_top :  -- Proved
  P → True  := by
  sorry


end propositional

----------------------------------------------------------------

section predicate

variable (U : Type)
variable (P Q : U → Prop)


------------------------------------------------
-- De Morgan laws for ∃,∀
------------------------------------------------

theorem demorgan_exists :  -- Proved
  ¬ (∃ x, P x) → (∀ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_converse :  -- Proved
  (∀ x, ¬ P x) → ¬ (∃ x, P x)  := by
  sorry

theorem demorgan_forall :  -- Sorry
  ¬ (∀ x, P x) → (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_forall_converse :  -- Proved
  (∃ x, ¬ P x) → ¬ (∀ x, P x)  := by
  sorry

theorem demorgan_forall_law :  -- Sorry
  ¬ (∀ x, P x) ↔ (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_law :  -- Proved
  ¬ (∃ x, P x) ↔ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
-- Interdefinability of ∃,∀
------------------------------------------------

theorem exists_as_neg_forall :  -- Proved
  (∃ x, P x) → ¬ (∀ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists :  -- Proved
  (∀ x, P x) → ¬ (∃ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists_converse :  -- Sorry
  ¬ (∃ x, ¬ P x) → (∀ x, P x)  := by
  sorry

theorem exists_as_neg_forall_converse :  -- Sorry
  ¬ (∀ x, ¬ P x) → (∃ x, P x)  := by
  sorry

theorem forall_as_neg_exists_law :  -- Sorry
  (∀ x, P x) ↔ ¬ (∃ x, ¬ P x)  := by
  sorry

theorem exists_as_neg_forall_law :  -- Sorry
  (∃ x, P x) ↔ ¬ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
--  Distributivity between quantifiers
------------------------------------------------

theorem exists_conj_as_conj_exists :  -- Proved
  (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists :  -- Proved
  (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists_converse :  -- Proved
  (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x)  := by
  sorry

theorem forall_conj_as_conj_forall :  -- Proved
  (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x)  := by
  sorry

theorem forall_conj_as_conj_forall_converse :  -- Proved
  (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x)  := by
  sorry

theorem forall_disj_as_disj_forall_converse :
  (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x)  := by
  sorry


end predicate

------------------------------------------------

section bonus

------------------------------------------------
--  Drinker's paradox
------------------------------------------------

variable (D : U → Prop)

-- There is a person p such that:
-- if p drinks, then everybody drinks
-- p: «person»
-- D x: «x drinks»
theorem drinker :
  ∃ p, (D p → ∀ x, D x)  := by
  sorry

------------------------------------------------
--  Russell's paradox
------------------------------------------------

variable (S : U → U → Prop)

-- It is impossible to have a barber b such that
-- b shaves exactly those people who do not shave themselves
-- b: «barber»
-- S x y: «x shaves y»
theorem russell :
  ¬ ∃ b, ∀ x, (S b x ↔ ¬ S x x)  := by
  sorry


end bonus


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)  := by
  sorry

theorem exists_conj_as_conj_exists_converse :
  (∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)  := by
  sorry

---------------------------------------------- -/
