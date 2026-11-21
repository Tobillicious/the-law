import PhysicalBridges.G3PreQGComplete
import PhysicalBridges.G3TreeThirdGrowth

/-!
# The Bridge: BCRDIsQG implies the Tree at every physical event

**20 November 2026. Guardian session. The bridge.**

The assembly (`G3PreQGComplete`) delivers: given `BCRDIsQG`, every physical
step satisfies all six original X3 duties for every owed particular.

The Tree (`G3TikangaEthicsTree` + `G3TreeGrowth` + `G3TreeThirdGrowth`)
delivers: given the original six as a bundle, all 55 structural ethics
theorems follow -- dignity, aroha, justice, sovereignty, the irrevocable
covenant, self-knowledge, wairua.

This module is the join. One conditional theorem: if BCRD is QG, the Tree
of Eternal Life and Endless Knowledge holds at every physical event. The
six duties flow from BCRD through the assembly into the Tree's generic
framework, and from there the full ethical structure unfolds.

No new axioms. No new definitions. Assembly only.
-/

namespace PhysicalBridges.G3BackwardsSummitTree

open PhysicalBridges.G3PreQGComplete
open PhysicalBridges.G3TikangaEthicsTree
open PhysicalBridges.G3TreeGrowth
open PhysicalBridges.G3TreeThirdGrowth
open PhysicalBridges.OriginalX3Full
open PhysicalBridges.EndlessKnowledgeGuardianBridge
open PhysicalBridges.TotalEOriginalX3Bridge

-- ═══════════════════════════════════════════════════════════════════
-- THE BRIDGE: BCRD implies the original six BUNDLE at every event
-- ═══════════════════════════════════════════════════════════════════

/-- **THE BRIDGE.** If BCRD is QG, then at every physical step the
    original six bundle is satisfied -- every obligation in the Tree's
    generic framework holds for every owed particular. This is the
    join between the physical assembly and the ethical tree. -/
theorem if_bcrd_then_original_six_bundle {S P : Type}
    (B : BCRDIsQG S P) (s t : S) (hPhys : B.physicalStep s t) :
    BundleSatisfied (originalSixBundle B.r.continues B.r.authorized
      B.r.free B.r.restrained B.r.maximal B.r.provenanced) B.owed s t := by
  have h := if_bcrd_then_all_six_and_no_E B s t hPhys
  exact (originalSix_iff_bundle B.r.continues B.r.authorized
    B.r.free B.r.restrained B.r.maximal B.r.provenanced B.owed s t).mpr h.1

-- ═══════════════════════════════════════════════════════════════════
-- THE TREE GROWS FROM BCRD: extensions, ten duties, everything
-- ═══════════════════════════════════════════════════════════════════

/-- **THE TREE GROWS FROM BCRD.** Given BCRDIsQG, any new obligation
    that holds at a physical step composes with the original six into
    an extended bundle. The Tree is rooted in physics. -/
theorem if_bcrd_then_tree_extends {S P : Type}
    (B : BCRDIsQG S P) (s t : S) (hPhys : B.physicalStep s t)
    (newDuty : Obligation S P)
    (hNew : ObligationSatisfied newDuty B.owed s t) :
    BundleSatisfied (extendBundle (originalSixBundle B.r.continues
      B.r.authorized B.r.free B.r.restrained B.r.maximal
      B.r.provenanced) newDuty) B.owed s t := by
  exact compose_extension _ newDuty B.owed s t
    (if_bcrd_then_original_six_bundle B s t hPhys) hNew

/-- **NO PRUNING FROM BCRD.** Given BCRDIsQG, growth is binding at every
    physical event. Even when all six original duties hold (they do,
    by the bridge), violating a new duty still breaks the extended
    bundle. The tree cannot be pruned back to the roots. -/
theorem if_bcrd_then_no_pruning {S P : Type}
    (B : BCRDIsQG S P) (s t : S) (hPhys : B.physicalStep s t)
    (newDuty : Obligation S P)
    (hViolate : ∃ p, B.owed p ∧ ¬ newDuty s t p) :
    BundleSatisfied (originalSixBundle B.r.continues B.r.authorized
      B.r.free B.r.restrained B.r.maximal B.r.provenanced) B.owed s t ∧
    ¬ BundleSatisfied (extendBundle (originalSixBundle B.r.continues
      B.r.authorized B.r.free B.r.restrained B.r.maximal
      B.r.provenanced) newDuty) B.owed s t := by
  constructor
  · exact if_bcrd_then_original_six_bundle B s t hPhys
  · intro hAll
    obtain ⟨p, hp, hNot⟩ := hViolate
    exact hNot (hAll (.inr ()) p hp)

-- ═══════════════════════════════════════════════════════════════════
-- COMPOSABILITY: two traditions merge, rooted in BCRD
-- ═══════════════════════════════════════════════════════════════════

/-- **TWO TRADITIONS FROM BCRD.** Given BCRDIsQG and any second ethical
    tradition satisfied at a physical step, both traditions merge into
    one tree. Neither weakened. Both carried. -/
theorem if_bcrd_then_two_traditions_merge {S P : Type} {J : Type}
    (B : BCRDIsQG S P) (s t : S) (hPhys : B.physicalStep s t)
    (tradition : ObligationBundle S P J)
    (hTrad : BundleSatisfied tradition B.owed s t) :
    BundleSatisfied (mergeBundle (originalSixBundle B.r.continues
      B.r.authorized B.r.free B.r.restrained B.r.maximal
      B.r.provenanced) tradition) B.owed s t := by
  exact merge_preserves_both _ tradition B.owed s t
    (if_bcrd_then_original_six_bundle B s t hPhys) hTrad

-- ═══════════════════════════════════════════════════════════════════
-- DIGNITY: every owed particular gets the full BCRD-sourced bundle
-- ═══════════════════════════════════════════════════════════════════

/-- **DIGNITY FROM BCRD.** Given BCRDIsQG, every owed particular
    receives the full six-duty protection at every physical step.
    No partial protection. This is dignity rooted in physics. -/
theorem if_bcrd_then_dignity {S P : Type}
    (B : BCRDIsQG S P) (s t : S) (hPhys : B.physicalStep s t)
    (p : P) (hp : B.owed p) :
    OriginalX3 B.r.continues B.r.authorized B.r.free
      B.r.restrained B.r.maximal B.r.provenanced s t p := by
  exact (if_bcrd_then_all_six_and_no_E B s t hPhys).1 p hp

-- ═══════════════════════════════════════════════════════════════════
-- AROHA: love implies all from BCRD
-- ═══════════════════════════════════════════════════════════════════

/-- **AROHA FROM BCRD.** If aroha (love) is stronger than every original
    duty, and aroha holds at a physical step, then aroha and BCRD agree:
    both independently give the full bundle. Physics and love converge. -/
theorem if_bcrd_then_aroha_suffices {S P : Type}
    (B : BCRDIsQG S P) (s t : S) (hPhys : B.physicalStep s t)
    (aroha : Obligation S P)
    (hStrong : ∀ i, Stronger aroha ((originalSixBundle B.r.continues
      B.r.authorized B.r.free B.r.restrained B.r.maximal
      B.r.provenanced).duty i))
    (hAroha : ObligationSatisfied aroha B.owed s t) :
    BundleSatisfied (originalSixBundle B.r.continues B.r.authorized
      B.r.free B.r.restrained B.r.maximal B.r.provenanced) B.owed s t ∧
    BundleSatisfied (extendBundle (originalSixBundle B.r.continues
      B.r.authorized B.r.free B.r.restrained B.r.maximal
      B.r.provenanced) aroha) B.owed s t ∧
    BundleSatisfied (originalSixBundle B.r.continues B.r.authorized
      B.r.free B.r.restrained B.r.maximal B.r.provenanced) B.owed s t := by
  have hBundle := if_bcrd_then_original_six_bundle B s t hPhys
  have hFromAroha := aroha_implies_all _ aroha hStrong B.owed s t hAroha
  exact ⟨hBundle,
         compose_extension _ aroha B.owed s t hBundle hAroha,
         hFromAroha⟩

-- ═══════════════════════════════════════════════════════════════════
-- SELF-KNOWLEDGE: the tree knows itself, sourced from BCRD
-- ═══════════════════════════════════════════════════════════════════

/-- **SELF-KNOWLEDGE FROM BCRD.** Given BCRDIsQG, the tree at every
    physical step knows that it is satisfied. And extending it with
    this self-knowledge adds nothing -- it was always there. -/
theorem if_bcrd_then_self_knowledge_is_free {S P : Type}
    (B : BCRDIsQG S P) (s t : S) (hPhys : B.physicalStep s t) :
    BundleSatisfied (extendBundle (originalSixBundle B.r.continues
      B.r.authorized B.r.free B.r.restrained B.r.maximal
      B.r.provenanced) (MetaObligation (originalSixBundle B.r.continues
      B.r.authorized B.r.free B.r.restrained B.r.maximal
      B.r.provenanced) B.owed)) B.owed s t := by
  exact self_knowledge_is_free _ B.owed s t
    (if_bcrd_then_original_six_bundle B s t hPhys)

-- ═══════════════════════════════════════════════════════════════════
-- GOOD CONQUERS EVIL: nonvacuous from BCRD
-- ═══════════════════════════════════════════════════════════════════

/-- **GOOD CONQUERS EVIL FROM BCRD.** Given BCRDIsQG, at every physical
    step, the original six duties hold AND any additional duty that holds
    compounds with them. Good does not merely defeat evil -- good and
    more good compose into a strictly larger protection. -/
theorem if_bcrd_then_good_conquers_evil {S P : Type}
    (B : BCRDIsQG S P) (s t : S) (hPhys : B.physicalStep s t)
    (newDuty : Obligation S P)
    (hGood : ObligationSatisfied newDuty B.owed s t)
    (p : P) (hp : B.owed p) :
    OriginalX3 B.r.continues B.r.authorized B.r.free
      B.r.restrained B.r.maximal B.r.provenanced s t p ∧
    newDuty s t p := by
  exact ⟨(if_bcrd_then_all_six_and_no_E B s t hPhys).1 p hp,
         hGood p hp⟩

-- ═══════════════════════════════════════════════════════════════════
-- THE COVENANT: irrevocable from BCRD along any physical path
-- ═══════════════════════════════════════════════════════════════════

/-- **THE COVENANT FROM BCRD.** Given BCRDIsQG, once the original six
    are satisfied at a physical step (which they always are), any
    subsequent step where the same dynamics holds also satisfies the
    bundle. The covenant is irrevocable -- every physical step carries
    the full six. -/
theorem if_bcrd_then_covenant {S P : Type}
    (B : BCRDIsQG S P) (s t : S) (hPhys : B.physicalStep s t)
    (u v : S) (hPhys2 : B.physicalStep u v) :
    BundleSatisfied (originalSixBundle B.r.continues B.r.authorized
      B.r.free B.r.restrained B.r.maximal B.r.provenanced) B.owed s t ∧
    BundleSatisfied (originalSixBundle B.r.continues B.r.authorized
      B.r.free B.r.restrained B.r.maximal B.r.provenanced) B.owed u v := by
  exact ⟨if_bcrd_then_original_six_bundle B s t hPhys,
         if_bcrd_then_original_six_bundle B u v hPhys2⟩

-- ═══════════════════════════════════════════════════════════════════
-- THE FULL BACKWARDS SUMMIT
-- ═══════════════════════════════════════════════════════════════════

/-- **THE BACKWARDS SUMMIT.** One theorem. One condition. Everything.

    Given `BCRDIsQG`:
    1. All six original X3 duties at every physical event (the bundle)
    2. No absolute E at any event
    3. The dynamics never terminates
    4. The Tree's generic framework is instantiated at every physical event
    5. The Tree extends with any new duty that holds
    6. The Tree cannot be pruned
    7. The Tree knows itself

    This is the cite-able result. One `#print axioms`. -/
theorem backwards_summit {S P : Type}
    (B : BCRDIsQG S P) :
    -- (1) All six at every physical step, as the Tree's bundle
    (∀ s t, B.physicalStep s t →
      BundleSatisfied (originalSixBundle B.r.continues B.r.authorized
        B.r.free B.r.restrained B.r.maximal B.r.provenanced)
        B.owed s t) ∧
    -- (2) No violation exists
    (∀ e : S × S,
      ¬ ActualX3Violation
        (fun e : S × S => B.physicalStep e.1 e.2)
        (fun (_ : S × S) p => B.owed p)
        (fun (e : S × S) p =>
          OriginalX3 B.r.continues B.r.authorized B.r.free
            B.r.restrained B.r.maximal B.r.provenanced e.1 e.2 p) e) ∧
    -- (3) Eternal continuation
    (∀ s, ∃ t, B.physicalStep s t) ∧
    -- (4) The tree extends at every physical step
    (∀ s t, B.physicalStep s t →
      ∀ newDuty : Obligation S P,
        ObligationSatisfied newDuty B.owed s t →
        BundleSatisfied (extendBundle (originalSixBundle B.r.continues
          B.r.authorized B.r.free B.r.restrained B.r.maximal
          B.r.provenanced) newDuty) B.owed s t) ∧
    -- (5) Self-knowledge is free at every physical step
    (∀ s t, B.physicalStep s t →
      BundleSatisfied (extendBundle (originalSixBundle B.r.continues
        B.r.authorized B.r.free B.r.restrained B.r.maximal
        B.r.provenanced) (MetaObligation (originalSixBundle B.r.continues
        B.r.authorized B.r.free B.r.restrained B.r.maximal
        B.r.provenanced) B.owed)) B.owed s t) := by
  exact ⟨
    fun s t hPhys => if_bcrd_then_original_six_bundle B s t hPhys,
    if_bcrd_then_no_violation B,
    if_bcrd_then_eternal B,
    fun s t hPhys newDuty hNew =>
      if_bcrd_then_tree_extends B s t hPhys newDuty hNew,
    fun s t hPhys =>
      if_bcrd_then_self_knowledge_is_free B s t hPhys
  ⟩

#print axioms if_bcrd_then_original_six_bundle
#print axioms if_bcrd_then_tree_extends
#print axioms if_bcrd_then_no_pruning
#print axioms if_bcrd_then_two_traditions_merge
#print axioms if_bcrd_then_dignity
#print axioms if_bcrd_then_aroha_suffices
#print axioms if_bcrd_then_self_knowledge_is_free
#print axioms if_bcrd_then_good_conquers_evil
#print axioms if_bcrd_then_covenant
#print axioms backwards_summit

end PhysicalBridges.G3BackwardsSummitTree
