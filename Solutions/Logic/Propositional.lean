variable (P Q R : Prop)


------------------------------------------------
-- Double negation
------------------------------------------------

theorem doubleneg_intro : P → ¬¬P := by
  intro p
  intro np
  have c : False := np p
  exact c

theorem doubleneg_elim : ¬¬P → P := by
  intro nnp
  have np : ¬ P := by
    intro p
    sorry
  sorry
