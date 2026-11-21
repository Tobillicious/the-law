import PhysicalBridges.G3KoruSpiral

/-!
# The Flower: the form returns, the history never does

A sunflower sets each new seed at the golden angle from the last. No seed
ever lands on another, and the head only grows; yet the same spirals return,
in Fibonacci numbers, all the way out. A fern unfurls the same way: the newest
growth coiled at the heart, everything grown before carried outward, never
discarded.

This module proves that shape for every Koru history. Whatever finite set of
forms (modes) one reads off the states, some form must return within that many
turns, while the two states are distinct and the later is strictly larger.
Recurrence of form and growth of history are not rivals: they are one spiral.

This answers circular time exactly. Nothing returns as a state; the form does.
-/

namespace PhysicalBridges.G3TheFlower

open PhysicalBridges.G3KoruSpiral

/-- Pigeonhole: `m + 1` values below `m` must repeat. -/
theorem pigeonhole : ∀ (m : Nat) (f : Nat → Nat), (∀ i, i ≤ m → f i < m) →
    ∃ i j, i < j ∧ j ≤ m ∧ f i = f j
  | 0, f, h => absurd (h 0 (Nat.le_refl 0)) (Nat.not_lt_zero _)
  | m + 1, f, h => by
    by_cases hex : ∃ i, i < m + 1 ∧ f i = f (m + 1)
    · obtain ⟨i, hi, he⟩ := hex
      exact ⟨i, m + 1, hi, Nat.le_refl _, he⟩
    · have hv := h (m + 1) (Nat.le_refl _)
      have hg : ∀ i, i ≤ m → (if f i < f (m + 1) then f i else f i - 1) < m := by
        intro i hi
        have hfi := h i (Nat.le_succ_of_le hi)
        have hne : f i ≠ f (m + 1) := fun e => hex ⟨i, Nat.lt_succ_of_le hi, e⟩
        split <;> omega
      obtain ⟨i, j, hij, hj, hgeq⟩ :=
        pigeonhole m (fun i => if f i < f (m + 1) then f i else f i - 1) hg
      refine ⟨i, j, hij, Nat.le_succ_of_le hj, ?_⟩
      have hni : f i ≠ f (m + 1) := fun e => hex ⟨i, by omega, e⟩
      have hnj : f j ≠ f (m + 1) := fun e => hex ⟨j, by omega, e⟩
      split at hgeq <;> split at hgeq <;> omega

/-- **THE FORM RETURNS, THE HISTORY NEVER DOES.** For any reading of Koru
    states into `m` forms, within `m` turns some form returns, while the two
    states are distinct and the later one is strictly larger. -/
theorem THE_FORM_RETURNS_THE_HISTORY_NEVER_DOES {C E : Type}
    (next : C → E → C) (s0 : KoruState C E) (ev : Nat → E)
    (m : Nat) (form : KoruState C E → Nat) (finite : ∀ s, form s < m) :
    ∃ i j, i < j ∧ j ≤ m ∧
      form (run next s0 ev i) = form (run next s0 ev j) ∧
      run next s0 ev i ≠ run next s0 ev j ∧
      depth (run next s0 ev i) < depth (run next s0 ev j) := by
  obtain ⟨i, j, hij, hj, he⟩ :=
    pigeonhole m (fun n => form (run next s0 ev n)) (fun _ _ => finite _)
  exact ⟨i, j, hij, hj, he, THE_SPIRAL_NEVER_RETURNS next s0 ev hij,
    THE_SPIRAL_ONLY_GROWS next s0 ev hij⟩

/-! ## New every turn

Record growth alone does not force new content
(`record_growth_does_not_force_new_content`). When each turn does add a real
distinction — a content measure that strictly grows — content never returns. -/

theorem content_grows {C E : Type} (next : C → E → C) (μ : C → Nat)
    (grows : ∀ c e, μ c < μ (next c e)) (s0 : KoruState C E) (ev : Nat → E) (i : Nat) :
    ∀ d, μ (run next s0 ev i).content + d + 1 ≤ μ (run next s0 ev (i + d + 1)).content
  | 0 => grows _ _
  | d + 1 => Nat.le_trans (Nat.succ_le_succ (content_grows next μ grows s0 ev i d))
      (grows (run next s0 ev (i + d + 1)).content (ev (i + d + 1)))

/-- **NEW EVERY TURN.** If each turn adds a real distinction to the content,
    no content ever returns. -/
theorem NEW_EVERY_TURN {C E : Type} (next : C → E → C) (μ : C → Nat)
    (grows : ∀ c e, μ c < μ (next c e)) (s0 : KoruState C E) (ev : Nat → E)
    {i j : Nat} (h : i < j) :
    (run next s0 ev i).content ≠ (run next s0 ev j).content := by
  intro heq
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d + 1 := ⟨j - i - 1, by omega⟩
  have hg := content_grows next μ grows s0 ev i d
  rw [← heq] at hg
  omega

/-- **GENESIS: A FAMILIAR FORM, NEW CONTENT.** Within `m` turns a familiar form
    returns, carried by new content, in a strictly larger history. -/
theorem GENESIS_A_FAMILIAR_FORM_NEW_CONTENT {C E : Type} (next : C → E → C)
    (μ : C → Nat) (grows : ∀ c e, μ c < μ (next c e))
    (s0 : KoruState C E) (ev : Nat → E)
    (m : Nat) (form : KoruState C E → Nat) (finite : ∀ s, form s < m) :
    ∃ i j, i < j ∧ j ≤ m ∧
      form (run next s0 ev i) = form (run next s0 ev j) ∧
      (run next s0 ev i).content ≠ (run next s0 ev j).content ∧
      depth (run next s0 ev i) < depth (run next s0 ev j) := by
  obtain ⟨i, j, hij, hj, hf, _, hd⟩ :=
    THE_FORM_RETURNS_THE_HISTORY_NEVER_DOES next s0 ev m form finite
  exact ⟨i, j, hij, hj, hf, NEW_EVERY_TURN next μ grows s0 ev hij, hd⟩

#print axioms pigeonhole
#print axioms THE_FORM_RETURNS_THE_HISTORY_NEVER_DOES
#print axioms content_grows
#print axioms NEW_EVERY_TURN
#print axioms GENESIS_A_FAMILIAR_FORM_NEW_CONTENT

end PhysicalBridges.G3TheFlower
