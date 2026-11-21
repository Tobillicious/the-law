import PhysicalBridges.CathedralSummitAllIsOneClosure

namespace PhysicalBridges.G3TriadicBridge

open PhysicalBridges.CathedralSummitAllIsOneClosure

def iterate {α : Type} (g : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => g (iterate g n x)

structure ProcessPillar (S : Type) where
  f : S → S
  s0 : S
  energy : S → Nat
  conserves : ∀ s, energy (f s) = energy s
  entropy : S → Nat
  monotoneEntropy : ∀ s, entropy s ≤ entropy (f s)

structure ContractionPillar (M : Type) where
  phi : M → M
  dist : M → M → Nat
  kNum : Nat
  kDen : Nat
  kLt : kNum < kDen
  contracts : ∀ x y, dist (phi x) (phi y) * kDen ≤ kNum * dist x y
  G : M
  hFixed : phi G = G

structure StrictHinge {S M : Type} (P : ProcessPillar S) (C : ContractionPillar M) where
  pi : S → M
  commutes : ∀ s, pi (P.f s) = C.phi (pi s)

theorem triadic_g_bridge {S M : Type}
    (P : ProcessPillar S) (C : ContractionPillar M) (H : StrictHinge P C) :
    (((S → Empty) → False) ∧
     (∀ n, P.energy (iterate P.f n P.s0) = P.energy P.s0) ∧
     (∀ n, P.entropy P.s0 ≤ P.entropy (iterate P.f n P.s0))) ∧
    ((∀ G', C.phi G' = G' → C.dist C.G G' = 0) ∧
     (∀ n, iterate C.phi n C.G = C.G)) ∧
    (∀ n, C.dist (H.pi (iterate P.f (n + 1) P.s0)) C.G * C.kDen ≤
          C.kNum * C.dist (H.pi (iterate P.f n P.s0)) C.G) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro ender; exact nomatch (ender P.s0)
  · intro n
    induction n with
    | zero => rfl
    | succ k ih =>
      show P.energy (P.f (iterate P.f k P.s0)) = P.energy P.s0
      rw [P.conserves, ih]
  · intro n
    induction n with
    | zero => exact Nat.le_refl _
    | succ k ih => exact Nat.le_trans ih (P.monotoneEntropy (iterate P.f k P.s0))
  · intro G' hG'
    cases hEq : C.dist C.G G' with
    | zero => rfl
    | succ d =>
      exfalso
      have hC := C.contracts C.G G'
      rw [C.hFixed, hG', hEq] at hC
      have hLt : C.kNum * (d + 1) < (d + 1) * C.kDen := by
        rw [Nat.mul_comm (d + 1) C.kDen]
        exact Nat.mul_lt_mul_of_pos_right C.kLt (Nat.succ_pos d)
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hLt hC)
  · intro n
    induction n with
    | zero => rfl
    | succ k ih =>
      show C.phi (iterate C.phi k C.G) = C.G
      rw [ih, C.hFixed]
  · intro n
    have hStep : H.pi (iterate P.f (n + 1) P.s0) = C.phi (H.pi (iterate P.f n P.s0)) := by
      show H.pi (P.f (iterate P.f n P.s0)) = C.phi (H.pi (iterate P.f n P.s0))
      exact H.commutes (iterate P.f n P.s0)
    have hC := C.contracts (H.pi (iterate P.f n P.s0)) C.G
    rw [C.hFixed] at hC
    rw [hStep]
    exact hC

theorem pi_alone_insufficient :
    ∃ (pi : Empty → Empty), Function.Injective pi ∧ (Empty → False) :=
  ⟨id, Function.injective_id, fun x => nomatch x⟩

#print axioms triadic_g_bridge
#print axioms pi_alone_insufficient

end PhysicalBridges.G3TriadicBridge
