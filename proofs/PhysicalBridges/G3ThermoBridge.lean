import PhysicalBridges.CathedralSummitAllIsOneClosure

namespace PhysicalBridges.G3ThermoBridge

def iterate {α : Type} (g : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => g (iterate g n x)

structure ThermoBridge (S M : Type) where
  f : S → S
  phi : M → M
  dist : M → M → Nat
  kNum : Nat
  kDen : Nat
  kLt : kNum < kDen
  contracts : ∀ x y, dist (phi x) (phi y) * kDen ≤ kNum * dist x y
  pi : S → M
  energy : S → Nat
  conserves : ∀ s, energy (f s) = energy s
  entropy : S → Nat
  monotoneEntropy : ∀ s, entropy s ≤ entropy (f s)

theorem koru_thermo_bridge {S M : Type}
    (B : ThermoBridge S M) (G : M) (hG : B.phi G = G)
    (s0 : S) (hPos : B.energy s0 ≠ 0) :
    ((S → Empty) → False) ∧
    (∀ n, iterate B.phi n G = G) ∧
    (∀ n, B.energy (iterate B.f n s0) = B.energy s0 ∧
          B.energy (iterate B.f n s0) ≠ 0) ∧
    (∀ n, B.entropy s0 ≤ B.entropy (iterate B.f n s0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ender; exact nomatch (ender s0)
  · intro n
    induction n with
    | zero => rfl
    | succ k ih =>
      show B.phi (iterate B.phi k G) = G
      rw [ih, hG]
  · intro n
    have hEq : B.energy (iterate B.f n s0) = B.energy s0 := by
      induction n with
      | zero => rfl
      | succ k ih =>
        show B.energy (B.f (iterate B.f k s0)) = B.energy s0
        rw [B.conserves, ih]
    exact ⟨hEq, by rw [hEq]; exact hPos⟩
  · intro n
    induction n with
    | zero => exact Nat.le_refl _
    | succ k ih =>
      exact Nat.le_trans ih (B.monotoneEntropy (iterate B.f k s0))

#print axioms koru_thermo_bridge

end PhysicalBridges.G3ThermoBridge
