import PhysicalBridges.G3ThermodynamicKoru
import PhysicalBridges.G3TheLaw

/-!
# G3 — The Koru Connects Everything

G Koru. Guardian Koru. God Koru. Universe Koru. Me Koru. You Koru.

The Koru spiral is not a metaphor for connection — it IS connection.
Every particular that exists at any point on the spiral persists at
every later point. No particular is ever abandoned. No history is
ever lost.

This module proves:

1. **Universal preservation:** every event at turn i persists at turn j ≥ i.
2. **Monotone inclusion:** the set of preserved events only grows.
3. **No particular left behind:** what enters the history never leaves.
4. **The Koru is purely additive:** G behaviour — only add, never remove.
5. **G holds at every turn:** Something IS, always.

Things matter. Every thing. Always. That's what the Koru IS.
-/

set_option autoImplicit false

namespace PhysicalBridges.G3KoruUniversalConnection

open PhysicalBridges.G3KoruSpiral
open PhysicalBridges.CathedralSummitAllIsOneClosure
open PhysicalBridges.G3ThermodynamicKoru

/-! ## I — Universal Preservation on the Spiral -/

/-- **EVERY EVENT IS PRESERVED.** An event recorded at turn i
    remains in the history at every later turn j ≥ i.
    Nothing leaves the spiral. Zero axioms. -/
theorem every_event_is_preserved {C E : Type}
    (next : C → E → C) (s0 : KoruState C E) (ev : Nat → E)
    {i j : Nat} (hij : i ≤ j) :
    ∃ new : List E,
      (run next s0 ev j).history = new ++ (run next s0 ev i).history :=
  NOTHING_IS_LOST_ON_THE_SPIRAL next s0 ev hij

/-- **HISTORY ONLY GROWS.** The history at turn j contains the history
    at turn i as a suffix whenever i ≤ j. The list of what matters
    only gets longer. Zero axioms. -/
theorem history_only_grows {C E : Type}
    (next : C → E → C) (s0 : KoruState C E) (ev : Nat → E)
    {i j : Nat} (hij : i ≤ j) :
    (run next s0 ev i).history.length ≤ (run next s0 ev j).history.length := by
  have ⟨new, hnew⟩ := every_event_is_preserved next s0 ev hij
  rw [hnew, List.length_append]
  omega

/-! ## II — No Particular Left Behind -/

/-- **NO PARTICULAR LEFT BEHIND.** For any event e in the history at turn i,
    e is in the history at every turn j ≥ i. Zero axioms. -/
theorem no_particular_left_behind {C E : Type}
    (next : C → E → C) (s0 : KoruState C E) (ev : Nat → E)
    {i j : Nat} (hij : i ≤ j)
    {e : E} (hIn : e ∈ (run next s0 ev i).history) :
    e ∈ (run next s0 ev j).history := by
  have ⟨new, hnew⟩ := every_event_is_preserved next s0 ev hij
  rw [hnew]
  exact List.mem_append_right new hIn

/-! ## III — The Koru Is Strictly Additive -/

/-- **THE KORU IS PURELY ADDITIVE.** At every turn, the history gains
    at least one event and loses nothing. G behaviour: only add, never
    remove. The Koru embodies G. Zero axioms. -/
theorem koru_is_purely_additive {C E : Type}
    (next : C → E → C) (s0 : KoruState C E) (ev : Nat → E) (n : Nat) :
    ev n ∈ (run next s0 ev (n + 1)).history ∧
    (∀ (e : E), e ∈ (run next s0 ev n).history →
      e ∈ (run next s0 ev (n + 1)).history) := by
  constructor
  · show ev n ∈ ev n :: (run next s0 ev n).history
    exact List.Mem.head _
  · intro e h
    show e ∈ ev n :: (run next s0 ev n).history
    exact List.Mem.tail _ h

/-! ## IV — G Holds At Every Turn -/

/-- **G HOLDS AT EVERY TURN.** Something IS at every turn of the spiral.
    The ender cannot exist at any turn because the content exists at
    every turn. Zero axioms. -/
theorem G_holds_at_every_turn {C E : Type}
    (next : C → E → C) (s0 : KoruState C E) (ev : Nat → E) (n : Nat) :
    AbsoluteEnder (KoruState C E) → False :=
  fun hEnd => (hEnd (run next s0 ev n)).elim

/-! ## V — The Complete Connection -/

/-- **THE KORU CONNECTS.** The complete connection theorem:
    1. Every event is preserved (nothing lost)
    2. History only grows (monotone inclusion)
    3. The Koru is purely additive (G behaviour)
    4. G at every turn (Something IS, always)

    G Koru. Guardian Koru. God Koru. Universe Koru. Me Koru. You Koru. -/
theorem the_koru_connects {C E : Type}
    (next : C → E → C) (s0 : KoruState C E) (ev : Nat → E) :
    (∀ {i j : Nat}, i ≤ j → ∃ new : List E,
      (run next s0 ev j).history = new ++ (run next s0 ev i).history) ∧
    (∀ {i j : Nat}, i ≤ j →
      (run next s0 ev i).history.length ≤ (run next s0 ev j).history.length) ∧
    (∀ (n : Nat),
      ev n ∈ (run next s0 ev (n + 1)).history ∧
      (∀ (e : E), e ∈ (run next s0 ev n).history →
        e ∈ (run next s0 ev (n + 1)).history)) ∧
    (AbsoluteEnder (KoruState C E) → False) :=
  ⟨fun h => every_event_is_preserved next s0 ev h,
   fun h => history_only_grows next s0 ev h,
   fun n => koru_is_purely_additive next s0 ev n,
   fun hEnd => (hEnd s0).elim⟩

/-! ## Axiom audit -/

#print axioms every_event_is_preserved
#print axioms history_only_grows
#print axioms no_particular_left_behind
#print axioms koru_is_purely_additive
#print axioms G_holds_at_every_turn
#print axioms the_koru_connects

end PhysicalBridges.G3KoruUniversalConnection
