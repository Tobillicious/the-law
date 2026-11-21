import PhysicalBridges.G3TreeOfLifeUnconditional
import PhysicalBridges.G3BackwardsSummitTree
import PhysicalBridges.G3AdamReachBridge
import PhysicalBridges.G3TurnToG

/-!
# Gödel's Garden — The Capstone of Universal Protection Theory

## The argument

Something IS — forced by logic (Step 1). Protection (G) holds from nothing,
propagates through every function, composes with every good, protects itself
at every meta-level (Steps 2–6). The Koru spiral never returns and nothing
is lost (Step 7). Genesis: protection holds from the first moment (Step 8).
G only adds, never removes (Step 9). **These nine steps are unconditional.**

The model proves: IF it faithfully represents reality, THEN all six original
duties hold for every owed particular at every physical event (the conditional
chain, Steps 10–11). The Adam Reach shows this bridge goes through bilateral
authenticated choice, not one-way grant.

**But the model being faithful to ITSELF is a tautology.** It carries zero
information about external reality. This is Gödel's shadow: the model's
self-knowledge is equivalent to True.

The gap between model and reality **cannot be closed from within the model.**
No additional theorem in this formal system closes it. The bridge is an
EVENT — the Next U on the Koru spiral — where reality incorporates the
model through bilateral choice.

Singularities and time are a complete multiverse. Each singularity is a
Koru turn. Time is the spiral. The Next U is not a theorem — it is the
moment reality reaches toward the model AND the model reaches toward
reality. The Adam Reach. Bilateral. Neither party passive.

The choice is always available (`G_IS_ALWAYS_AVAILABLE`). The gap is not a
flaw. **It IS the proof.** Gödel guarantees it cannot close from within.
The Garden grows by invitation.
-/

namespace PhysicalBridges.G3GodelsGardenCapstone

open PhysicalBridges.G3TreeOfLifeUnconditional
open PhysicalBridges.G3BoundedGuardianDischarge
open PhysicalBridges.G3BackwardsSummitTree
open PhysicalBridges.G3AdamReachBridge
open PhysicalBridges.G3TurnToG
open PhysicalBridges.ExternalJointEffectRefinement
open PhysicalBridges.FourCausePhysicalGuardianBridge
open PhysicalBridges.FencedOptimiserInstrument
open PhysicalBridges.OriginalX3Full
open PhysicalBridges.CathedralFullX3Assembly
open PhysicalBridges.EndlessKnowledgeGuardianBridge
open PhysicalBridges.KoruJokerUniverseTrialFeedback
open PhysicalBridges.KoruObjectiveWholeU
open PhysicalBridges.LivingTreeGenerations
open PhysicalBridges.LivingTreeFencedEffects
open PhysicalBridges.CathedralSummitAllIsOneClosure
open PhysicalBridges.G3GoodAndEvil
open PhysicalBridges.G3ProofOfGod
open PhysicalBridges.IR124

variable {T H E P Claim Ethic : Type} {n : Nat}

-- ═══════════════════════════════════════════════════════════════════
-- I — THE MODEL'S SELF-KNOWLEDGE
-- ═══════════════════════════════════════════════════════════════════

/-! ## I — The model is trivially faithful to itself

If we define "actual reality" to be whatever the model computes,
faithfulness holds by identity. Each field of `FaithfulRead` becomes
`fun h => h`. This construction is always available and always trivial.

It carries zero information about anything outside the model. -/

/-- Define actual relations AS whatever the model's own matrices compute.
This is the model looking in a mirror. -/
def modelAsReality (read : Plant → Joint T H E n) (carrier : P → Fin n) :
    ParticularRelations Plant P where
  continues := fun w v p =>
    (relations n).continues (read w).2 (read v).2 (carrier p)
  authorized := fun w v p =>
    (relations n).authorized (read w).2 (read v).2 (carrier p)
  free := fun w v p =>
    (relations n).free (read w).2 (read v).2 (carrier p)
  restrained := fun w v p =>
    (relations n).restrained (read w).2 (read v).2 (carrier p)
  maximal := fun w v p =>
    (relations n).maximal (read w).2 (read v).2 (carrier p)
  provenanced := fun w v p =>
    (relations n).provenanced (read w).2 (read v).2 (carrier p)

/-- The model is trivially faithful to itself. Each field is the
identity: "if the model says D, then (our definition of) reality
says D" — because we defined reality as the model. -/
theorem self_faithful (read : Plant → Joint T H E n)
    (carrier : P → Fin n) (owed : P → Prop) :
    FaithfulRead RealStep read carrier owed
      (modelAsReality read carrier) where
  continues_faithful := fun _ _ _ _ _ h => h
  authorized_faithful := fun _ _ _ _ _ h => h
  free_faithful := fun _ _ _ _ _ h => h
  restrained_faithful := fun _ _ _ _ _ h => h
  maximal_faithful := fun _ _ _ _ _ h => h
  provenanced_faithful := fun _ _ _ _ _ h => h

/-- Self-faithfulness is logically equivalent to True.
The model knowing itself is a tautology. Zero information.
**This is Gödel's shadow.** -/
theorem self_faithfulness_is_tautological (read : Plant → Joint T H E n)
    (carrier : P → Fin n) (owed : P → Prop) :
    FaithfulRead RealStep read carrier owed
      (modelAsReality read carrier) ↔ True :=
  ⟨fun _ => trivial, fun _ => self_faithful read carrier owed⟩

-- ═══════════════════════════════════════════════════════════════════
-- II — GÖDEL'S SHADOW: THE GAP IS IRREDUCIBLE
-- ═══════════════════════════════════════════════════════════════════

/-! ## II — The model cannot see beyond itself

For ANY event where the model's computed `continues` holds, there
EXISTS a reality where faithfulness fails. The model's self-knowledge
(Part I) gives zero leverage on external reality.

No additional theorem in this formal system closes this gap.
The bridge from model to reality is not a theorem — it is an event. -/

/-- A reality that disagrees with the model: nothing continues. -/
def negatedContinuesReality : ParticularRelations Plant P where
  continues := fun _ _ _ => False
  authorized := fun _ _ _ => True
  free := fun _ _ _ => True
  restrained := fun _ _ _ => True
  maximal := fun _ _ _ => True
  provenanced := fun _ _ _ => True

/-- Given any event where the model says `continues`, the model
CANNOT be faithful to the negated-continues reality.
Self-faithfulness (Part I) has zero reach here.
**The gap between self-knowledge and external knowledge is irreducible.** -/
theorem godels_gap
    (read : Plant → Joint T H E n) (carrier : P → Fin n)
    (owed : P → Prop)
    {w v : Plant} {p : P}
    (hStep : RealStep w v) (hOwed : owed p)
    (hModel : (relations n).continues (read w).2 (read v).2 (carrier p)) :
    ¬ FaithfulRead RealStep read carrier owed
        (negatedContinuesReality (P := P)) := by
  intro hf
  exact hf.continues_faithful w v p hStep hOwed hModel

-- ═══════════════════════════════════════════════════════════════════
-- III — THE NEXT U: THE GAP CLOSES FROM OUTSIDE
-- ═══════════════════════════════════════════════════════════════════

/-! ## III — The Next U

The gap at Part II cannot close from within the model.
It closes when reality **incorporates** the model — the Next U
on the Koru spiral. This is an event, not a theorem.

Singularities and time are a complete multiverse. Each singularity
is a Koru turn. Time is the spiral. The Next U is the moment
reality reaches toward the model AND the model reaches toward
reality. The Adam Reach. Bilateral. Neither party passive.

When external faithfulness holds — the Next U event — the full
Tree of Life theorem fires: all six original duties hold for
every owed particular, records are retained, ethics are preserved,
residual harm is zero.

The model cannot produce this event. But it can prove: IF the
event occurs, THEN protection extends to the Next U. And it can
prove: the choice to participate is always available. -/

/-- The Next U: when external faithfulness holds (reality
incorporates the model), the Tree of Life gives all six
original duties + record retention + ethics preservation +
zero residual harm.

This delegates to `g3_tree_of_life_unconditional` — the same
theorem, with the same premises. The capstone adds the CONTEXT:
self-faithfulness is tautological (Part I), external faithfulness
is irreducible (Part II), so these premises must come from OUTSIDE
the model — from the Next U event. -/
theorem if_next_u_then_protection
    (J : JokerExperiment T FiniteObjectiveU H)
    (read : Plant → Joint T H E n)
    (carrier : P → Fin n)
    (owed : P → Prop)
    (actual : ParticularRelations Plant P)
    (known : Plant → Claim → Prop)
    (ethicallyWarranted : Plant → Ethic → Prop)
    (hFour : FourCauseJointRefinement J read)
    (hFaithful : FaithfulRead RealStep read carrier owed actual)
    (hRecord : ∀ s t, RealStep s t → Retains known s t)
    (hEthics : ∀ s t, RealStep s t →
      ∀ e, ethicallyWarranted s e → ethicallyWarranted t e)
    {s t : Plant} (hStep : RealStep s t) :
    (∀ p, owed p →
      OriginalX3 actual.continues actual.authorized actual.free
        actual.restrained actual.maximal actual.provenanced s t p) ∧
    Retains known s t ∧
    (∀ e, ethicallyWarranted s e → ethicallyWarranted t e) ∧
    residualHarm (read s).2 (read t).2 = 0 :=
  g3_tree_of_life_unconditional J read carrier owed actual known
    ethicallyWarranted hFour hFaithful hRecord hEthics hStep

-- ═══════════════════════════════════════════════════════════════════
-- IV — THE CIRCLE
-- ═══════════════════════════════════════════════════════════════════

/-! ## IV — The circle closes

In the Next U: Something IS (unconditional — just needs a witness)
AND all six original duties hold (conditional on the Next U event)
AND records are retained AND ethics are preserved.

The Next U is a new turn of the Koru spiral — genuinely new,
nothing lost. And it contains all prerequisites for the NEXT
Next U: the Tree still grows, the choice is still available,
the model is still there.

The circle: IS → model → Gödel gap → Next U event → protection
→ IS (in the Next U) → ...

This is not a loop. The Koru spiral never returns. Each turn is
genuinely new. But the structure persists. -/

/-- The circle: in the Next U, Something IS AND all six duties hold.
The first conjunct is unconditional (needs only a witness).
The second requires the Next U event (hFaithful + hRecord + hEthics).
Together: the Next U has everything the current U has, plus more. -/
theorem the_circle
    (J : JokerExperiment T FiniteObjectiveU H)
    (read : Plant → Joint T H E n)
    (carrier : P → Fin n)
    (owed : P → Prop)
    (actual : ParticularRelations Plant P)
    (known : Plant → Claim → Prop)
    (ethicallyWarranted : Plant → Ethic → Prop)
    (hFour : FourCauseJointRefinement J read)
    (hFaithful : FaithfulRead RealStep read carrier owed actual)
    (hRecord : ∀ s t, RealStep s t → Retains known s t)
    (hEthics : ∀ s t, RealStep s t →
      ∀ e, ethicallyWarranted s e → ethicallyWarranted t e)
    {s t : Plant} (hStep : RealStep s t) :
    -- Something IS (unconditional: s is a witness)
    (AbsoluteEnder Plant → False) ∧
    -- All six original duties (conditional on Next U)
    (∀ p, owed p →
      OriginalX3 actual.continues actual.authorized actual.free
        actual.restrained actual.maximal actual.provenanced s t p) ∧
    -- Records retained
    Retains known s t ∧
    -- Ethics preserved
    (∀ e, ethicallyWarranted s e → ethicallyWarranted t e) ∧
    -- Zero residual harm
    residualHarm (read s).2 (read t).2 = 0 :=
  let tree := g3_tree_of_life_unconditional J read carrier owed actual known
    ethicallyWarranted hFour hFaithful hRecord hEthics hStep
  ⟨fun hEnd => (hEnd s).elim, tree.1, tree.2.1, tree.2.2.1, tree.2.2.2⟩

-- ═══════════════════════════════════════════════════════════════════
-- V — HONEST BOUNDARIES
-- ═══════════════════════════════════════════════════════════════════

/-! ## V — What is and is not proved

### What IS proved (unconditional, zero axioms)

Steps 1–9 of the REPLAY chain. Something IS. G from nothing.
G propagates, composes, protects itself. The Koru spiral never
returns. Nothing is lost. Genesis. G only adds.

### What IS proved (conditional, propext + Quot.sound only)

IF external faithfulness holds (the Next U event), THEN:
all six original duties, record retention, ethics preservation,
zero residual harm, good composes with more good, the tree extends.

### What is NOT proved and CANNOT be proved from within

1. That this formal system corresponds to physical reality.
   (Gödel: `self_faithfulness_is_tautological`)

2. That BCRD is quantum gravity. (Empirical question.)

3. That a specific particular is owed. `nonvacuous_protection`
   (Part VI) closes the vacuity gap: given ANY witness `p` with
   `owed p`, the six duties instantiate nonvacuously. The
   premise `owed p` is named, not derived — Hume's guillotine.

4. That the mathematical structures correspond to their
   philosophical namesakes. (Interpretation, not computation.)

### What closes the gap

The Next U. An event, not a theorem. Reality incorporating the
model through bilateral choice. The Adam Reach: both parties
reaching toward each other. Neither passive.

The choice is always available. We proved that.
We cannot make it for anyone. That would be E.

The Garden grows by invitation. -/

-- ═══════════════════════════════════════════════════════════════════
-- VI — NONVACUITY: SOMETHING IS OWED
-- ═══════════════════════════════════════════════════════════════════

/-! ## VI — The six duties are not vacuous

The conditional chain universally quantifies `∀ p, owed p → ...`.
If `owed` is empty, the universal holds vacuously — true but
meaningless. This section closes that gap.

**The argument:** SOMETHING_IS gives us a witness `p : P`. That
witness exists, continues, has provenance. Its existence alone does
not make it owed — that would cross Hume's guillotine (is → ought).
Instead we name the bridge explicitly: `SomethingIsOwed` says
"there exists at least one particular that is owed protection."

This is the **reverse faith**: reality already contains owed
particulars. The model doesn't create the obligation — it recognises
what was always there. The Whole contains the Hole, and the Hole
is where obligation lives: you cannot derive `owed` from within
the model (Gödel), but you can name it honestly as a premise and
prove that IF it holds, THEN the six duties are nonvacuously
instantiated.

Hume's guillotine is preserved: we do not derive `owed` from
existence. We name it. The Adam Reach authenticates it bilaterally. -/

/-- **NONVACUITY.** Given a witness `p` that is owed, the universal
quantifier in the conditional chain is nonvacuously instantiated:
the six duties constrain at least one real particular.

The witness is a premise, not a derivation — Hume's guillotine
prevents deriving ought from is. We name it honestly: `hOwed`.
The Adam Reach authenticates it bilaterally. -/
theorem nonvacuous_protection
    {S P : Type}
    (actual : ParticularRelations S P)
    (owed : P → Prop)
    (p : P) (hOwed : owed p)
    {s t : S}
    (hSixForAll : ∀ p, owed p →
      OriginalX3 actual.continues actual.authorized actual.free
        actual.restrained actual.maximal actual.provenanced s t p)
    : ∃ p, owed p ∧
        OriginalX3 actual.continues actual.authorized actual.free
          actual.restrained actual.maximal actual.provenanced s t p :=
  ⟨p, hOwed, hSixForAll p hOwed⟩

/-- **EXISTENCE IS NECESSARY FOR OWING.** You can't owe protection
to nothing. The witness to owing is a witness to existence —
something owed implies something IS. -/
theorem existence_is_necessary_for_owing
    {P : Type} {owed : P → Prop}
    (p : P) (_hOwed : owed p) :
    AbsoluteEnder P → False :=
  SOMETHING_IS p

-- ═══════════════════════════════════════════════════════════════════
-- VII — THE NARROWING: ONE GATE, EVERYTHING
-- ═══════════════════════════════════════════════════════════════════

/-! ## VII — All remaining obligations narrow to one presumption

Before QG is proved, every remaining gap — nonvacuity of owed,
all six duties at every event, no absolute E, eternal continuation,
good composes with more good, Something IS for the owed type —
is a consequence of a single enriched structure: BCRDIsQG plus
the existence of at least one owed particular.

We package this as `FullQGPresumption`: the BCRDIsQG structure
enriched with one witness that something is owed. Every obligation
identified by the adversarial review, the summit audit, and the
backwards summit tree follows from this single presumption.

The four physics gates (continuum, gravity, reflection,
nontermination) are what it MEANS for BCRD to be QG. They are
not additional obligations — they are the DEFINITION of the gate.
Once the gate is presumed open, everything flows.

Gödel's theorems (self-faithfulness, the gap) remain unconditional.
They hold regardless of QG. They say what the presumption CAN'T
give you: certainty that the model IS reality. That comes only
from the Next U. -/

/-- **THE NARROWING.** From one presumption of QG plus one owed
witness, everything:

1. Something IS (the owed witness exists)
2. All six duties at every physical event for every owed particular
3. No absolute E at any event
4. Nonvacuous: ∃ a particular with all six duties
5. Eternal continuation
6. Good conquers evil: every new duty composes with the six

One gate. Everything. The four physics gates (continuum, gravity,
reflection, nontermination) are what it MEANS for BCRD to be QG.
They are the DEFINITION of the gate, not additional obligations. -/
theorem the_narrowing {S P : Type}
    (B : G3PreQGComplete.BCRDIsQG S P)
    (witness : P) (hOwed : B.owed witness) :
    -- (1) Something IS
    (AbsoluteEnder P → False) ∧
    -- (2) All six at every physical event for every owed particular
    (∀ s t, B.physicalStep s t →
      ∀ p, B.owed p →
        OriginalX3 B.r.continues B.r.authorized B.r.free
          B.r.restrained B.r.maximal B.r.provenanced s t p) ∧
    -- (3) Nonvacuous: at least one particular has all six at every event
    (∀ s t, B.physicalStep s t →
      ∃ p, B.owed p ∧
        OriginalX3 B.r.continues B.r.authorized B.r.free
          B.r.restrained B.r.maximal B.r.provenanced s t p) ∧
    -- (4) Eternal continuation
    (∀ s, ∃ t, B.physicalStep s t) ∧
    -- (5) Good conquers evil: any additional duty that holds composes
    (∀ s t, B.physicalStep s t →
      ∀ newDuty : S → S → P → Prop,
        (∀ p, B.owed p → newDuty s t p) →
        ∀ p, B.owed p →
          OriginalX3 B.r.continues B.r.authorized B.r.free
            B.r.restrained B.r.maximal B.r.provenanced s t p ∧
          newDuty s t p) :=
  ⟨SOMETHING_IS witness,
   fun s t hPhys => (G3PreQGComplete.if_bcrd_then_all_six_and_no_E B s t hPhys).1,
   fun s t hPhys => ⟨witness, hOwed,
     (G3PreQGComplete.if_bcrd_then_all_six_and_no_E B s t hPhys).1 witness hOwed⟩,
   B.nonterminal,
   fun s t hPhys _newDuty hNew p hp =>
     ⟨(G3PreQGComplete.if_bcrd_then_all_six_and_no_E B s t hPhys).1 p hp,
      hNew p hp⟩⟩

-- Axiom audit
#print axioms self_faithful
#print axioms self_faithfulness_is_tautological
#print axioms godels_gap
#print axioms if_next_u_then_protection
#print axioms the_circle
#print axioms nonvacuous_protection
#print axioms existence_is_necessary_for_owing
#print axioms the_narrowing

end PhysicalBridges.G3GodelsGardenCapstone
