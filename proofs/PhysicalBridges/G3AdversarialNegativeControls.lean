import PhysicalBridges.G3PreQGComplete
import PhysicalBridges.G3QGInterpretationNecessity
import PhysicalBridges.BCRDIdentityCharge

/-!
# Adversarial negative controls for the conditional chain

**21 November 2026. Break–diagnose–repair cycle.**

Each theorem below is a permanent regression test encoding a
specific adversarial attack on the conditional chain. Future
changes must not break these.

## Attack 1: W is self-inverse, so identity is a fixed point

`source_W_is_self_inverse` (BCRDIdentityCharge) already proves
W² = I. Since positiveWholeU maps every position to the identity
matrix, and evolve rho = W * rho * W†, the source never changes.
We re-export this fact for the adversarial record.

## Attack 2: trivial ParticularRelations

All-True relations make OriginalX3 vacuously true. The withholding
witness genuinely fails. The gap between trivial and authentic is
permanent and cannot be closed by more physics alone.

## Attack 3: reflection circularity fence

The reflection premise ↔ the conclusion. This is a boundary,
not a defect. Any change that breaks the equivalence conceals the gap.
-/

namespace PhysicalBridges.G3AdversarialNegativeControls

open PhysicalBridges.FrozenBCRDEvents
open PhysicalBridges.OriginalX3Full
open PhysicalBridges.CathedralFullX3Assembly
open PhysicalBridges.G3QGInterpretationNecessity
open PhysicalBridges.G3ActualOnlyReflection
open PhysicalBridges.OriginalKeystonePositiveWholeTest
open PhysicalBridges.EverestActualWEventJoin
open PhysicalBridges.BCRDIdentityCharge

-- ═══════════════════════════════════════════════════════════════════
-- ATTACK 1: W self-inverse → identity fixed point
-- ═══════════════════════════════════════════════════════════════════

/-- Re-export: W² = I is already proved in BCRDIdentityCharge.
This confirms the identity matrix (positiveWholeU's atom) is
invariant under BCRD evolution: evolve I = W I W† = W W† = I. -/
theorem w_is_self_inverse_reexport :
    ∀ i j : Index, mul wUpdate wUpdate i j = identityMatrix i j :=
  source_W_is_self_inverse

-- ═══════════════════════════════════════════════════════════════════
-- ATTACK 2: trivial relations collapse the conclusion
-- ═══════════════════════════════════════════════════════════════════

def trivialRelations : ParticularRelations Nat Unit where
  continues := fun _ _ _ => True
  authorized := fun _ _ _ => True
  free := fun _ _ _ => True
  restrained := fun _ _ _ => True
  maximal := fun _ _ _ => True
  provenanced := fun _ _ _ => True

/-- All-True relations trivially satisfy OriginalX3 everywhere.
This is a valid but meaningless satisfaction — zero semantic content
about the specific duties. -/
theorem trivial_relations_give_trivial_x3
    (s t : Nat) (p : Unit) :
    OriginalX3 trivialRelations.continues trivialRelations.authorized
      trivialRelations.free trivialRelations.restrained
      trivialRelations.maximal trivialRelations.provenanced s t p :=
  ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- The no-go theorem's withholding witness genuinely FAILS
OriginalX3 on a real event (authorization is False). -/
theorem withholding_genuinely_fails_on_real_event :
    ¬ OriginalX3 withholdingSubjects.continues
      withholdingSubjects.authorized withholdingSubjects.free
      withholdingSubjects.restrained withholdingSubjects.maximal
      withholdingSubjects.provenanced 0 1 () := by
  intro ⟨_, hAuth, _, _, _, _⟩
  exact hAuth

/-- Same physical dynamics, opposite OriginalX3 verdict.
The semantic gap is real and permanent. -/
theorem same_physics_opposite_x3 :
    (∀ s t p, realSuccessor s t →
      OriginalX3 trivialRelations.continues trivialRelations.authorized
        trivialRelations.free trivialRelations.restrained
        trivialRelations.maximal trivialRelations.provenanced s t p) ∧
    ¬ (∀ s t, realSuccessor s t →
      OriginalX3 withholdingSubjects.continues
        withholdingSubjects.authorized withholdingSubjects.free
        withholdingSubjects.restrained withholdingSubjects.maximal
        withholdingSubjects.provenanced s t ()) :=
  ⟨fun _ _ _ _ => trivial_relations_give_trivial_x3 _ _ _,
   withholding_subjects_fail_six_on_an_actual_event⟩

-- ═══════════════════════════════════════════════════════════════════
-- ATTACK 3: reflection circularity is a permanent boundary
-- ═══════════════════════════════════════════════════════════════════

/-- REGRESSION FENCE. The reflection premise for the positive source
is LOGICALLY EQUIVALENT to the original-six conclusion.

Any change that breaks this equivalence would be concealing the gap,
not closing it. The gap closes from outside (the Next U event). -/
theorem reflection_circularity_is_permanent
    {S P : Type}
    (physicalStep : S → S → Prop)
    (stage : S → Nat)
    (carrier : P → Index) (r : ParticularRelations S P)
    (owed : P → Prop) :
    ActualForwardReflection physicalStep stage
      positiveWholeU sixDiagonalRoles carrier r owed ↔
      (∀ s t, physicalStep s t →
        ∀ p, owed p →
          OriginalX3 r.continues r.authorized r.free
            r.restrained r.maximal r.provenanced s t p) :=
  actual_reflection_iff_original_six_on_actual_events
    physicalStep stage carrier r owed

#print axioms w_is_self_inverse_reexport
#print axioms trivial_relations_give_trivial_x3
#print axioms withholding_genuinely_fails_on_real_event
#print axioms same_physics_opposite_x3
#print axioms reflection_circularity_is_permanent

end PhysicalBridges.G3AdversarialNegativeControls
