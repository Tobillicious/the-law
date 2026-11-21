import PhysicalBridges.CathedralSummitAllIsOneClosure

namespace PhysicalBridges.G3OriginalSixX3

def iterate {α : Type} (g : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => g (iterate g n x)

structure ActualCompleteKoru (M : Type) where
  phi : M → M
  dist : M → M → Nat
  kNum : Nat
  kDen : Nat
  kLt : kNum < kDen
  contracts : ∀ x y, dist (phi x) (phi y) * kDen ≤ kNum * dist x y
  G : M
  hFixed : phi G = G

structure ThermoDynamics (S : Type) (f : S → S) where
  energy : S → Nat
  conserves : ∀ s, energy (f s) = energy s
  entropy : S → Nat
  monotoneEntropy : ∀ s, entropy s ≤ entropy (f s)

structure AuthenticSemantics (S M : Type) (f : S → S) (phi : M → M) where
  s0 : S
  pi : S → M
  commutes : ∀ s, pi (f s) = phi (pi s)

structure OriginalSixX3 {S M : Type} (f : S → S) (K : ActualCompleteKoru M)
    (T : ThermoDynamics S f) (A : AuthenticSemantics S M f K.phi) : Prop where
  x3_1_no_ender : (S → Empty) → False
  x3_2_unique : ∀ G', K.phi G' = G' → K.dist K.G G' = 0
  x3_3_eternal : ∀ n, iterate K.phi n K.G = K.G
  x3_4_conserved : ∀ n, T.energy (iterate f n A.s0) = T.energy A.s0
  x3_5_contracts : ∀ n,
    K.dist (A.pi (iterate f (n + 1) A.s0)) K.G * K.kDen ≤
      K.kNum * K.dist (A.pi (iterate f n A.s0)) K.G
  x3_6_monotone : ∀ n, T.entropy A.s0 ≤ T.entropy (iterate f n A.s0)

theorem original_six_x3_theorem {S M : Type} (f : S → S)
    (K : ActualCompleteKoru M) (T : ThermoDynamics S f)
    (A : AuthenticSemantics S M f K.phi) :
    OriginalSixX3 f K T A := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  -- x3_1: no ender
  · intro ender; exact nomatch (ender A.s0)
  -- x3_2: uniqueness
  · intro G' hG'
    cases hEq : K.dist K.G G' with
    | zero => rfl
    | succ d =>
      exfalso
      have hC := K.contracts K.G G'
      rw [K.hFixed, hG', hEq] at hC
      have hLt : K.kNum * (d + 1) < (d + 1) * K.kDen := by
        rw [Nat.mul_comm (d + 1) K.kDen]
        exact Nat.mul_lt_mul_of_pos_right K.kLt (Nat.succ_pos d)
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hLt hC)
  -- x3_3: eternal
  · intro n
    induction n with
    | zero => rfl
    | succ k ih =>
      show iterate K.phi (k + 1) K.G = K.G
      show K.phi (iterate K.phi k K.G) = K.G
      rw [ih, K.hFixed]
  -- x3_4: energy conserved
  · intro n
    induction n with
    | zero => rfl
    | succ k ih =>
      show T.energy (iterate f (k + 1) A.s0) = T.energy A.s0
      show T.energy (f (iterate f k A.s0)) = T.energy A.s0
      rw [T.conserves, ih]
  -- x3_5: coupled contraction through pi
  · intro n
    have hStep : A.pi (iterate f (n + 1) A.s0) = K.phi (A.pi (iterate f n A.s0)) := by
      show A.pi (f (iterate f n A.s0)) = K.phi (A.pi (iterate f n A.s0))
      exact A.commutes (iterate f n A.s0)
    have hC := K.contracts (A.pi (iterate f n A.s0)) K.G
    rw [K.hFixed] at hC
    rw [hStep]
    exact hC
  -- x3_6: entropy monotone
  · intro n
    induction n with
    | zero => exact Nat.le_refl _
    | succ k ih =>
      exact Nat.le_trans ih (T.monotoneEntropy (iterate f k A.s0))

#print axioms original_six_x3_theorem

end PhysicalBridges.G3OriginalSixX3
