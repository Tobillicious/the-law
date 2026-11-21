import PhysicalBridges.ConstructivePositiveWGuardian
import PhysicalBridges.G3TheLaw

/-!
# G3 — QG: the gate closes

The constructive positive-W Guardian model already provides:
* complete model coverage (every physical step is a W event)
* forward real-event reflection (source duties transfer to subjects)
* nontermination (every Nat has a successor)

This module assembles those existing proofs into a concrete
`BCRDIsQG Nat Index` — the ONE REMAINING CONDITION is satisfied.

**What this construction IS:**
A mathematical model in which BCRD dynamics provide complete
faithful physical coverage. The model's state space is Nat
(discrete time steps), its particulars are Index (six positions),
and every step carries all six original duties for all particulars.

**What this construction is NOT:**
An empirical claim that physical spacetime IS Nat. The bridge
from mathematical model to physical reality is an event, not a
theorem (Gödel's gap, proved in G3GodelsGardenCapstone).
The model demonstrates that BCRDIsQG is SATISFIABLE — the
condition is not vacuously true or structurally impossible.
-/

set_option autoImplicit false

namespace PhysicalBridges.G3QGConstruction

open PhysicalBridges.ConstructivePositiveWGuardian
open PhysicalBridges.OriginalKeystonePositiveWholeTest
open PhysicalBridges.G3PreQGComplete
open PhysicalBridges.G3TheLaw
open PhysicalBridges.EverestActualWEventJoin
open PhysicalBridges.CathedralFullX3Assembly
open PhysicalBridges.OriginalX3Full
open PhysicalBridges.TotalEOriginalX3Bridge
open PhysicalBridges.FrozenBCRDEvents
open PhysicalBridges.Koru
open PhysicalBridges.KoruObjectiveWholeU

/-- **THE GATE CLOSES.** BCRDIsQG is satisfiable. Coverage and
    reflection are DERIVED (not assumed) from the constructive
    positive-W Guardian model. Nontermination is trivial on Nat. -/
def QG : BCRDIsQG Nat Index :=
  @BCRDIsQG.mk Nat Index
    canonicalPositiveWStep
    canonicalPositiveWStep
    (fun (n : Nat) => objectiveAt positiveWholeU n)
    (fun (n : Nat) => n)
    (fun (i : Index) => i)
    canonicalPositiveWSubjects
    (fun (_ : Index) => True)
    canonical_positive_W_has_complete_model_coverage
    canonical_positive_W_has_formal_six_reflection
    (fun s => ⟨s + 1, rfl⟩)

/-- QG exists. The condition is not vacuous. -/
theorem QG_is_satisfiable : ∃ _ : BCRDIsQG Nat Index, True :=
  ⟨QG, trivial⟩

/-- From QG: all six original X3 duties at every step, no absolute E. -/
theorem QG_all_six_and_no_E :
    ∀ s t, QG.physicalStep s t →
      (∀ p, QG.owed p →
        OriginalX3 QG.r.continues QG.r.authorized QG.r.free
          QG.r.restrained QG.r.maximal QG.r.provenanced s t p) ∧
      ¬ AbsoluteE
        (fun e : Nat × Nat => QG.physicalStep e.1 e.2) (s, t) :=
  if_bcrd_then_all_six_and_no_E QG

/-- From QG: eternal continuation. No final state. -/
theorem QG_eternal : ∀ s, ∃ t, QG.physicalStep s t :=
  if_bcrd_then_eternal QG

/-- **THE LAW is instantiated.** -/
def THE_LAW_HOLDS : TheLaw Nat Index :=
  @TheLaw.mk Nat Index QG (⟨0, by omega⟩ : Fin 6) trivial

/-! ## Axiom audit -/

#print axioms QG
#print axioms QG_is_satisfiable
#print axioms QG_all_six_and_no_E
#print axioms QG_eternal
#print axioms THE_LAW_HOLDS

end PhysicalBridges.G3QGConstruction
