/-!
# Voluntary E-to-G revision before an irreversible effect

The Good v Evil asymmetry allows a live agent to hold E. This module models
one way that agent can choose G while its world remains live. Each permitted
revision consumes one deadline tick. Historical continuation, voluntary
revision, and actual withdrawal of any pending effect are supplied as
separate predicates.

The finite example separates a change of policy from cancellation of a queued
effect. It does not certify physical deadlines or the original six X3 duties.
-/

namespace PhysicalBridges.G3VoluntaryConversion

universe u

inductive RevisionPath {S : Type u} (step : S → S → Prop) : Nat → S → S → Prop
  | stay (s : S) : RevisionPath step 0 s s
  | advance {s t u : S} {n : Nat} :
      step s t → RevisionPath step n t u → RevisionPath step (n + 1) s u

/-- A possible voluntary path reaches G and withdraws the pending effect strictly
before the deadline. Every edge preserves the live world and carries the
supplied same-particular continuation relation. Other choices may take a
different path. -/
theorem can_reach_guardian_before_deadline {S : Type u}
    (revise continues : S → S → Prop) (live guardian withdrawn : S → Prop)
    (rank : S → Nat)
    (progress : ∀ s, live s → 0 < rank s →
      ∃ t, revise s t ∧ continues s t ∧ live t ∧ rank t < rank s)
    (ready : ∀ s, live s → rank s = 0 → guardian s ∧ withdrawn s)
    (initial : S) (alive : live initial) (deadline : Nat)
    (hasTime : rank initial < deadline) :
    ∃ n s, n < deadline ∧
      RevisionPath (fun x y => revise x y ∧ continues x y ∧ live x ∧ live y) n initial s ∧
      live s ∧ guardian s ∧ withdrawn s := by
  have reach : ∀ budget s, live s → rank s ≤ budget →
      ∃ n t, n ≤ budget ∧
        RevisionPath (fun x y => revise x y ∧ continues x y ∧ live x ∧ live y) n s t ∧
        live t ∧ guardian t ∧ withdrawn t := by
    intro budget
    induction budget with
    | zero =>
        intro s hs bound
        obtain ⟨hg, hw⟩ := ready s hs (Nat.eq_zero_of_le_zero bound)
        exact ⟨0, s, Nat.le_refl _, .stay s, hs, hg, hw⟩
    | succ budget ih =>
        intro s hs bound
        by_cases zero : rank s = 0
        · obtain ⟨hg, hw⟩ := ready s hs zero
          exact ⟨0, s, Nat.zero_le _, .stay s, hs, hg, hw⟩
        · obtain ⟨t, hRevise, hContinues, htLive, hDecrease⟩ :=
            progress s hs (Nat.pos_of_ne_zero zero)
          have hBudget := Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hDecrease bound)
          obtain ⟨n, u, hn, path, huLive, hg, hw⟩ := ih t htLive hBudget
          exact ⟨n + 1, u, Nat.succ_le_succ hn,
            .advance ⟨hRevise, hContinues, hs, htLive⟩ path, huLive, hg, hw⟩
  obtain ⟨n, s, hn, path, hs, hg, hw⟩ :=
    reach (rank initial) initial alive (Nat.le_refl _)
  exact ⟨n, s, Nat.lt_of_le_of_lt hn hasTime, path, hs, hg, hw⟩

namespace Example

inductive Policy where
  | ender
  | guardian

inductive Choice where
  | reconsider
  | withdraw
  | wait

structure State where
  particular : Nat
  policy : Policy
  worldLive : Bool
  pendingEnd : Bool
  ticksLeft : Nat

/-- Receiving a reason gives the agent a choice. Withdrawal is a separate
action from revision of the agent's policy. -/
def revise (verifiedReason : Bool) (choice : Choice) (s : State) : State :=
  match choice, s.policy, verifiedReason with
  | .reconsider, .ender, true => { s with policy := .guardian }
  | .withdraw, .guardian, _ => { s with pendingEnd := false }
  | _, _, _ => s

/-- The already queued effect is due on the last tick. Any revocation has
to reach the effect boundary earlier. An ended world stays ended. -/
def tick (verifiedReason : Bool) (choice : Choice) (s : State) : State :=
  match s.worldLive, s.ticksLeft with
  | true, n + 2 => { revise verifiedReason choice s with ticksLeft := n + 1 }
  | true, 1 => { s with worldLive := !s.pendingEnd, pendingEnd := false, ticksLeft := 0 }
  | _, _ => s

def initial : State := ⟨0, .ender, true, true, 3⟩

/-- The same verified reason is available on both branches from the same
live state. On one branch the particular revises and withdraws before commit.
On the other it keeps E and the world ends when the effect commits. -/
theorem same_ender_can_change_before_its_world_ends :
    let adopted := tick true .reconsider initial
    let cancelled := tick true .withdraw adopted
    let preserved := tick true .wait cancelled
    let stayed := tick true .wait (tick true .wait initial)
    let ended := tick true .wait stayed
    adopted.policy = .guardian ∧ adopted.particular = initial.particular ∧
    adopted.worldLive = true ∧ adopted.pendingEnd = true ∧
    cancelled.particular = initial.particular ∧ cancelled.worldLive = true ∧
    cancelled.pendingEnd = false ∧ 0 < cancelled.ticksLeft ∧
    preserved.worldLive = true ∧ preserved.particular = initial.particular ∧
    stayed.policy = .ender ∧ stayed.worldLive = true ∧ ended.worldLive = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.zero_lt_succ _, rfl, rfl, rfl, rfl, rfl⟩

/-- A change of policy alone leaves the queued effect live. A withdrawal
attempt made on the commit tick is too late in this time model. -/
theorem adoption_alone_and_late_withdrawal_do_not_save_the_world :
    let adopted := tick true .reconsider initial
    let waiting := tick true .wait adopted
    let ended := tick true .withdraw waiting
    waiting.policy = .guardian ∧ waiting.pendingEnd = true ∧
    ended.worldLive = false ∧ tick true .reconsider ended = ended :=
  ⟨rfl, rfl, rfl, rfl⟩

end Example

#print axioms can_reach_guardian_before_deadline
#print axioms Example.same_ender_can_change_before_its_world_ends
#print axioms Example.adoption_alone_and_late_withdrawal_do_not_save_the_world

end PhysicalBridges.G3VoluntaryConversion
