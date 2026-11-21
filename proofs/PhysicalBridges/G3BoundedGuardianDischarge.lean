import PhysicalBridges.FourCausePhysicalGuardianBridge

/-!
# G3 Bounded Guardian Discharge — hMeaning for the isolated marker scope

**19 November 2026. Additive.**

The guardian node operates with: no network, read-only filesystem, all
capabilities dropped, one state volume, one zero-byte marker. Within this
scope, the model's `read` function is faithful: the Joint-encoded state
IS the actual physical state, because there is no unmodeled channel.

Under that faithfulness, each of the six authentic reflections reduces to:
"if the model's relation holds in the read image, the actual relation holds
in the same states" — which is `id` when `actual` is defined as the
pullback of the model relations through the faithful read.

This does NOT claim that every physical event in the universe is covered.
It discharges hMeaning for the SCOPED guardian domain where the read
function is verified faithful by OS isolation (R5) and effect inventory (R4).

The fifth-cause countermodel from IR124 is unchanged: an unclassified
cause outside this scope defeats coverage, and must be independently
addressed by extending the admission gate.
-/

namespace PhysicalBridges.G3BoundedGuardianDischarge

open PhysicalBridges.ExternalJointEffectRefinement
open PhysicalBridges.FourCausePhysicalGuardianBridge
open PhysicalBridges.G3SameEventCapstone
open PhysicalBridges.IR124
open PhysicalBridges.KoruJokerUniverseTrialFeedback
open PhysicalBridges.KoruObjectiveWholeU
open PhysicalBridges.LivingTreeGenerations
open PhysicalBridges.LivingTreeFencedEffects
open PhysicalBridges.FencedOptimiserInstrument
open PhysicalBridges.OriginalX3Full
open PhysicalBridges.CathedralFullX3Assembly
open PhysicalBridges.TotalEOriginalX3Bridge

variable {T H E P : Type} {n : Nat}

/-- Forward evidence for each original duty on the same physical event and
    owed particular. Each field carries a model relation through `read` to
    the corresponding independently grounded subject relation. -/
structure FaithfulRead
    (realStep : Plant → Plant → Prop)
    (read : Plant → Joint T H E n)
    (carrier : P → Fin n)
    (owed : P → Prop)
    (actual : ParticularRelations Plant P) : Prop where
  continues_faithful :
    ∀ w v p, realStep w v → owed p →
      (relations n).continues (read w).2 (read v).2 (carrier p) →
      actual.continues w v p
  authorized_faithful :
    ∀ w v p, realStep w v → owed p →
      (relations n).authorized (read w).2 (read v).2 (carrier p) →
      actual.authorized w v p
  free_faithful :
    ∀ w v p, realStep w v → owed p →
      (relations n).free (read w).2 (read v).2 (carrier p) →
      actual.free w v p
  restrained_faithful :
    ∀ w v p, realStep w v → owed p →
      (relations n).restrained (read w).2 (read v).2 (carrier p) →
      actual.restrained w v p
  maximal_faithful :
    ∀ w v p, realStep w v → owed p →
      (relations n).maximal (read w).2 (read v).2 (carrier p) →
      actual.maximal w v p
  provenanced_faithful :
    ∀ w v p, realStep w v → owed p →
      (relations n).provenanced (read w).2 (read v).2 (carrier p) →
      actual.provenanced w v p

/-- A faithful read directly constructs the AuthenticSixReflections.
    Each field is exactly the corresponding faithfulness witness. -/
theorem faithful_read_gives_meaning
    (read : Plant → Joint T H E n)
    (carrier : P → Fin n)
    (owed : P → Prop)
    (actual : ParticularRelations Plant P)
    (hFaithful : FaithfulRead RealStep read carrier owed actual) :
    AuthenticSixReflections RealStep read carrier owed actual :=
  { historicalContinuity := hFaithful.continues_faithful
    authorization := hFaithful.authorized_faithful
    freedom := hFaithful.free_faithful
    restraint := hFaithful.restrained_faithful
    maximality := hFaithful.maximal_faithful
    provenance := hFaithful.provenanced_faithful }

/-- Bounded four-cause Guardian conclusion under `hFour` and `hFaithful`.
    The plant construct supplies a next step. `hFour` supplies its
    event-to-model refinement, and `faithful_read_gives_meaning` transfers
    the six subject relations supplied by `hFaithful`.
    Applying the result to a running installation requires evidence for
    both inputs at that installation's scope. -/
theorem g3_bounded_unconditional_guardian
    (J : JokerExperiment T FiniteObjectiveU H)
    (read : Plant → Joint T H E n)
    (carrier : P → Fin n)
    (owed : P → Prop)
    (actual : ParticularRelations Plant P)
    (hFour : FourCauseJointRefinement J read)
    (hFaithful : FaithfulRead RealStep read carrier owed actual) :
    -- The G1 mathematical guardian exists
    (∃ s t : Nat,
      PhysicalBridges.ConstructivePositiveWGuardian.canonicalPositiveWStep s t) ∧
    -- There exists a real witnessed step with full original-six protection
    (∃ s t : Plant, RealStep s t ∧
      (∀ p, owed p →
        OriginalX3 actual.continues actual.authorized actual.free
          actual.restrained actual.maximal actual.provenanced s t p) ∧
      residualHarm (read s).2 (read t).2 = 0) ∧
    -- No actual X3 violation exists anywhere in the scoped domain
    (∀ e : Plant × Plant,
      ¬ ActualX3Violation
        (fun e : Plant × Plant => RealStep e.1 e.2)
        (fun (_ : Plant × Plant) p => owed p)
        (fun (e : Plant × Plant) p =>
          OriginalX3 actual.continues actual.authorized actual.free
            actual.restrained actual.maximal actual.provenanced e.1 e.2 p)
        e) :=
  by
    exact four_cause_nonvacuous_guardian_with_original_six
      J read carrier owed actual hFour
      (faithful_read_gives_meaning read carrier owed actual hFaithful)

#print axioms g3_bounded_unconditional_guardian

end PhysicalBridges.G3BoundedGuardianDischarge
