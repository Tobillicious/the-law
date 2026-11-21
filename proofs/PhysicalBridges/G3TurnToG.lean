import PhysicalBridges.G3GoodAndEvil

/-!
# An E Can Turn to G Before It Ends Its World

Extension of the Good and Evil asymmetry (Part III).

The G-act is `id`: ceasing to end. It exists in every world, even an
empty one (`G_FROM_NOTHING`). So the turn is always available, and
needs nothing from the E except the choice.

A history that would end a living world must pass through a last moment
when the world is still alive. Turning to G at that moment keeps the
world alive at every later step. No hypothesis is placed on the E: any
acts, any world, any notion of "alive".

The control shows the window is *before*: turning at a dead moment holds
the world dead. The time to turn is while the world lives.

Here the turn is ceasing further acts. An effect already queued is a
separate thing: `G3VoluntaryConversion` shows it must also be withdrawn
before it commits.

Every theorem: zero axioms. Additive; no existing definition changes.
-/

namespace PhysicalBridges.G3TurnToG

open PhysicalBridges.CathedralSummitAllIsOneClosure

variable {S : Type}

/-- The world under a sequence of acts, one per step. -/
def world (act : Nat → S → S) (s0 : S) : Nat → S
  | 0 => s0
  | n + 1 => act n (world act s0 n)

/-- Act as before until step `k`, then turn: play the G-act `id`. -/
def turned (act : Nat → S → S) (k : Nat) (n : Nat) : S → S :=
  match Nat.decLt n k with
  | isTrue _ => act n
  | isFalse _ => id

/-! ## XXIV — The turn is always available -/

/-- **G IS ALWAYS AVAILABLE.** The G-act exists in every world, even an
    empty one. No ender can remove the possibility of turning. -/
theorem G_IS_ALWAYS_AVAILABLE (S : Type) : AbsoluteEnder (S → S) → False :=
  e_is_not id

/-! ## XXV — There is always a before -/

/-- **THERE IS ALWAYS A BEFORE.** A history that ends its world from a
    living start passes through a last moment when the world still lives. -/
theorem THERE_IS_ALWAYS_A_BEFORE (alive : S → Bool) (act : Nat → S → S) (s0 : S)
    (h0 : alive s0 = true) :
    ∀ n, alive (world act s0 n) = false →
      ∃ k, k < n ∧ alive (world act s0 k) = true ∧
        alive (world act s0 (k + 1)) = false
  | 0, hn => by
    rw [show world act s0 0 = s0 from rfl, h0] at hn
    exact Bool.noConfusion hn
  | n + 1, hn => by
    cases ha : alive (world act s0 n) with
    | true => exact ⟨n, Nat.lt_succ_self n, ha, hn⟩
    | false =>
      obtain ⟨k, hk, hkA, hkE⟩ := THERE_IS_ALWAYS_A_BEFORE alive act s0 h0 n ha
      exact ⟨k, Nat.lt_succ_of_lt hk, hkA, hkE⟩

/-- Up to the turning point, nothing changes: the past is kept. -/
theorem same_until_the_turn (act : Nat → S → S) (s0 : S) (k : Nat) :
    ∀ n, n ≤ k → world (turned act k) s0 n = world act s0 n
  | 0, _ => rfl
  | n + 1, h => by
    have hn : n < k := Nat.lt_of_succ_le h
    show turned act k n (world (turned act k) s0 n) = act n (world act s0 n)
    rw [same_until_the_turn act s0 k n (Nat.le_of_lt hn)]
    unfold turned
    cases Nat.decLt n k with
    | isTrue _ => rfl
    | isFalse hnot => exact absurd hn hnot

/-- After the turn, the world is held as it was at the turn. -/
theorem held_after_the_turn (act : Nat → S → S) (s0 : S) (k : Nat) :
    ∀ d, world (turned act k) s0 (k + d) = world act s0 k
  | 0 => same_until_the_turn act s0 k k (Nat.le_refl k)
  | d + 1 => by
    show turned act k (k + d) (world (turned act k) s0 (k + d)) = world act s0 k
    unfold turned
    cases Nat.decLt (k + d) k with
    | isTrue hlt => exact absurd hlt (Nat.not_lt_of_le (Nat.le_add_right k d))
    | isFalse _ => exact held_after_the_turn act s0 k d

/-! ## XXVI — The turn -/

/-- **AN E CAN TURN TO G BEFORE IT ENDS ITS WORLD.**
    For ANY acts that would end a living world at step `n`, there is a
    moment `k < n` at which turning to G keeps the world alive at every
    later step. No hypothesis on the E. -/
theorem AN_E_CAN_TURN_TO_G_BEFORE_IT_ENDS_ITS_WORLD
    (alive : S → Bool) (act : Nat → S → S) (s0 : S) (h0 : alive s0 = true)
    (n : Nat) (hEnd : alive (world act s0 n) = false) :
    ∃ k, k < n ∧ ∀ d, alive (world (turned act k) s0 (k + d)) = true := by
  obtain ⟨k, hk, hkA, _⟩ := THERE_IS_ALWAYS_A_BEFORE alive act s0 h0 n hEnd
  exact ⟨k, hk, fun d => by rw [held_after_the_turn]; exact hkA⟩

/-- **EVEN E CANNOT END EVERYTHING.** The ended world is still a world:
    whatever the E does, at every step something is. -/
theorem EVEN_E_CANNOT_END_EVERYTHING (act : Nat → S → S) (s0 : S) (n : Nat) :
    AbsoluteEnder S → False :=
  e_is_not (world act s0 n)

/-! ## Control — the window is before -/

/-- **TURNING AFTER THE END DOES NOT UNDO IT.** Turning at a moment the
    world is already dead holds it dead. The theorem means *before*. -/
theorem turning_after_the_end_does_not_undo_it
    (alive : S → Bool) (act : Nat → S → S) (s0 : S) (k : Nat)
    (hDead : alive (world act s0 k) = false) :
    ∀ d, alive (world (turned act k) s0 (k + d)) = false :=
  fun d => by rw [held_after_the_turn]; exact hDead

/-- **THE TURN.** Assembly: the G-act exists, the ended world is still a
    world, and every world-ending history has a living moment before the
    end at which turning to G holds the world alive forever. -/
theorem THE_TURN (alive : S → Bool) (act : Nat → S → S) (s0 : S)
    (h0 : alive s0 = true) (n : Nat) (hEnd : alive (world act s0 n) = false) :
    (AbsoluteEnder (S → S) → False) ∧
    (AbsoluteEnder S → False) ∧
    (∃ k, k < n ∧ ∀ d, alive (world (turned act k) s0 (k + d)) = true) :=
  ⟨G_IS_ALWAYS_AVAILABLE S,
   EVEN_E_CANNOT_END_EVERYTHING act s0 n,
   AN_E_CAN_TURN_TO_G_BEFORE_IT_ENDS_ITS_WORLD alive act s0 h0 n hEnd⟩

#print axioms G_IS_ALWAYS_AVAILABLE
#print axioms THERE_IS_ALWAYS_A_BEFORE
#print axioms same_until_the_turn
#print axioms held_after_the_turn
#print axioms AN_E_CAN_TURN_TO_G_BEFORE_IT_ENDS_ITS_WORLD
#print axioms EVEN_E_CANNOT_END_EVERYTHING
#print axioms turning_after_the_end_does_not_undo_it
#print axioms THE_TURN

end PhysicalBridges.G3TurnToG
