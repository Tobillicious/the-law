import PhysicalBridges.G3TriadicBridge

namespace PhysicalBridges.G3HingeCategoryError

open PhysicalBridges.G3TriadicBridge

def ExactDecoder {M O : Type} (c : M → O) (live : M → Prop) : Prop :=
  ∃ dec : O → Bool, ∀ m, (dec (c m) = true ↔ live m)

theorem strict_hinge_category_error {S M O : Type}
    (P : ProcessPillar S) (C : ContractionPillar M) (hinge : StrictHinge P C)
    (c : M → O) (live : M → Prop)
    (s : S) (hLiveS : live (hinge.pi s))
    (a : M) (hCut : c (hinge.pi s) = c a) (hNotLiveA : ¬ live a) :
    ExactDecoder c live → False := by
  intro ⟨dec, hSpec⟩
  have hTrue : dec (c (hinge.pi s)) = true := (hSpec (hinge.pi s)).mpr hLiveS
  have hFalse : dec (c a) ≠ true := by
    intro hEq
    exact hNotLiveA ((hSpec a).mp hEq)
  rw [hCut] at hTrue
  exact hFalse hTrue

theorem hinge_live_persistence {S M : Type}
    (P : ProcessPillar S) (C : ContractionPillar M) (hinge : StrictHinge P C)
    (live : M → Prop)
    (hClosed : ∀ m, live m → live (C.phi m))
    (hInitLive : live (hinge.pi P.s0))
    (n : Nat) :
    live (hinge.pi (iterate P.f n P.s0)) := by
  induction n with
  | zero => exact hInitLive
  | succ k ih =>
    have hStep : hinge.pi (iterate P.f (k + 1) P.s0) =
        C.phi (hinge.pi (iterate P.f k P.s0)) := by
      show hinge.pi (P.f (iterate P.f k P.s0)) = C.phi (hinge.pi (iterate P.f k P.s0))
      exact hinge.commutes (iterate P.f k P.s0)
    rw [hStep]
    exact hClosed _ ih

#print axioms strict_hinge_category_error
#print axioms hinge_live_persistence

end PhysicalBridges.G3HingeCategoryError
