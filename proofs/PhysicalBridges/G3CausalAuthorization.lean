/-!
# Causal evidence for authorization at commit

This module checks the temporal part of authorization for one scoped grant,
one commit, and a complete inventory of effective withdrawals of that grant.
The episode has no re-grant. Event binding, authentic authority, completeness
of the inventory and the meaning of causal precedence come from independent
evidence. In particular, causal precedence is its transitive closure.

One compatible chronology suffices to construct either orientation of an
unordered pair. Move the first event and its causal predecessors to the front,
keeping their relative order and the order of all remaining events.
-/

namespace PhysicalBridges.G3CausalAuthorization

universe u

structure Chronology (Event : Type u) where
  before : Event → Event → Prop
  irrefl : ∀ e, ¬ before e e
  trans : ∀ {a b c}, before a b → before b c → before a c
  total : ∀ {a b}, a ≠ b → before a b ∨ before b a

def Respects {Event : Type u} (causal : Event → Event → Prop)
    (order : Chronology Event) : Prop :=
  ∀ {a b}, causal a b → order.before a b

def AuthorizedAtCommit {Event : Type u} (before : Event → Event → Prop)
    (grant commit : Event) (withdrawal : Event → Prop) : Prop :=
  before grant commit ∧ ∀ w, withdrawal w → before commit w

private def prioritize {Event : Type u} (order : Chronology Event)
    (front : Event → Prop) [DecidablePred front] : Chronology Event where
  before a b := (front a ∧ ¬ front b) ∨ ((front a ↔ front b) ∧ order.before a b)
  irrefl e := fun
    | .inl ⟨h, nh⟩ => nh h
    | .inr ⟨_, h⟩ => order.irrefl e h
  trans := fun hab hbc =>
    match hab, hbc with
    | .inl ⟨_, notB⟩, .inl ⟨b, _⟩ => False.elim (notB b)
    | .inl ⟨a, notB⟩, .inr ⟨bc, _⟩ => .inl ⟨a, fun c => notB (bc.mpr c)⟩
    | .inr ⟨ab, _⟩, .inl ⟨b, notC⟩ => .inl ⟨ab.mpr b, notC⟩
    | .inr ⟨ab, h₁⟩, .inr ⟨bc, h₂⟩ => .inr ⟨ab.trans bc, order.trans h₁ h₂⟩
  total := by
    intro a b distinct
    by_cases fa : front a
    · by_cases fb : front b
      · have same : front a ↔ front b := ⟨fun _ => fb, fun _ => fa⟩
        exact (order.total distinct).elim (fun h => .inl (.inr ⟨same, h⟩))
          (fun h => .inr (.inr ⟨same.symm, h⟩))
      · exact .inl (.inl ⟨fa, fb⟩)
    · by_cases fb : front b
      · exact .inr (.inl ⟨fb, fa⟩)
      · have same : front a ↔ front b :=
          ⟨fun h => False.elim (fa h), fun h => False.elim (fb h)⟩
        exact (order.total distinct).elim (fun h => .inl (.inr ⟨same, h⟩))
          (fun h => .inr (.inr ⟨same.symm, h⟩))

/-- Produce a compatible chronology that places a before b, provided the
known causal relation does not force b before a and the events are distinct. -/
theorem compatible_chronology_can_place_before {Event : Type u}
    [DecidableEq Event] (causal : Event → Event → Prop) [DecidableRel causal]
    (trans : ∀ {a b c}, causal a b → causal b c → causal a c)
    (baseline : Chronology Event) (valid : Respects causal baseline)
    (a b : Event) (distinct : a ≠ b) (noReverse : ¬ causal b a) :
    ∃ order : Chronology Event, Respects causal order ∧ order.before a b := by
  let front : Event → Prop := fun x => x = a ∨ causal x a
  letI : DecidablePred front := fun x => inferInstanceAs (Decidable (x = a ∨ causal x a))
  let order := prioritize baseline front
  refine ⟨order, ?_, Or.inl ⟨Or.inl rfl, ?_⟩⟩
  · intro x y edge
    by_cases fy : front y
    · have fx : front x := by
        rcases fy with rfl | pred
        · exact Or.inr edge
        · exact Or.inr (trans edge pred)
      exact Or.inr ⟨⟨fun _ => fy, fun _ => fx⟩, valid edge⟩
    · by_cases fx : front x
      · exact Or.inl ⟨fx, fy⟩
      · exact Or.inr ⟨⟨fun h => False.elim (fx h), fun h => False.elim (fy h)⟩, valid edge⟩
  · exact fun h => h.elim (fun e => distinct e.symm) noReverse

theorem forced_precedence_iff_every_compatible_chronology {Event : Type u}
    [DecidableEq Event] (causal : Event → Event → Prop) [DecidableRel causal]
    (trans : ∀ {a b c}, causal a b → causal b c → causal a c)
    (baseline : Chronology Event) (valid : Respects causal baseline) (a b : Event) :
    causal a b ↔ ∀ order, Respects causal order → order.before a b := by
  constructor
  · intro edge order respects
    exact respects edge
  · intro forced
    by_cases observed : causal a b
    · exact observed
    · have distinct : b ≠ a := by
        intro equal
        subst b
        exact baseline.irrefl a (forced baseline valid)
      obtain ⟨reverse, respects, reverseEdge⟩ :=
        compatible_chronology_can_place_before causal trans baseline valid b a distinct observed
      exact False.elim (reverse.irrefl a (reverse.trans (forced reverse respects) reverseEdge))

/-- A temporal authorization verdict is established by every compatible
chronology exactly when the evidence forces both the prior grant and the
absence of an effective withdrawal before commit. -/
theorem authorization_forced_iff_causal_precedence {Event : Type u}
    [DecidableEq Event] (causal : Event → Event → Prop) [DecidableRel causal]
    (trans : ∀ {a b c}, causal a b → causal b c → causal a c)
    (baseline : Chronology Event) (valid : Respects causal baseline)
    (grant commit : Event) (withdrawal : Event → Prop) :
    (∀ order, Respects causal order → AuthorizedAtCommit order.before grant commit withdrawal) ↔
      AuthorizedAtCommit causal grant commit withdrawal := by
  constructor
  · intro authorized
    refine ⟨(forced_precedence_iff_every_compatible_chronology
      causal trans baseline valid grant commit).mpr (fun order respects => (authorized order respects).1), ?_⟩
    intro w hw
    exact (forced_precedence_iff_every_compatible_chronology
      causal trans baseline valid commit w).mpr (fun order respects => (authorized order respects).2 w hw)
  · intro authorized order respects
    exact ⟨respects authorized.1, fun w hw => respects (authorized.2 w hw)⟩

/-- Hold the witnessed grant fixed and leave the effective withdrawal
incomparable with commit. The same evidence then admits both verdicts. -/
theorem unordered_withdrawal_admits_both_verdicts {Event : Type u}
    [DecidableEq Event] (causal : Event → Event → Prop) [DecidableRel causal]
    (trans : ∀ {a b c}, causal a b → causal b c → causal a c)
    (baseline : Chronology Event) (valid : Respects causal baseline)
    (grant commit withdrawal : Event) (grantBefore : causal grant commit)
    (distinct : commit ≠ withdrawal)
    (noEarly : ¬ causal withdrawal commit) (noLate : ¬ causal commit withdrawal) :
    (∃ order, Respects causal order ∧
      AuthorizedAtCommit order.before grant commit (· = withdrawal)) ∧
    (∃ order, Respects causal order ∧
      ¬ AuthorizedAtCommit order.before grant commit (· = withdrawal)) := by
  obtain ⟨late, lateRespects, lateEdge⟩ :=
    compatible_chronology_can_place_before causal trans baseline valid commit withdrawal distinct noEarly
  obtain ⟨early, earlyRespects, earlyEdge⟩ :=
    compatible_chronology_can_place_before causal trans baseline valid withdrawal commit distinct.symm noLate
  refine ⟨⟨late, lateRespects, lateRespects grantBefore, ?_⟩, ⟨early, earlyRespects, ?_⟩⟩
  · intro w hw
    subst w
    exact lateEdge
  · intro authorized
    exact early.irrefl commit (early.trans (authorized.2 withdrawal rfl) earlyEdge)

#print axioms authorization_forced_iff_causal_precedence
#print axioms unordered_withdrawal_admits_both_verdicts

end PhysicalBridges.G3CausalAuthorization
