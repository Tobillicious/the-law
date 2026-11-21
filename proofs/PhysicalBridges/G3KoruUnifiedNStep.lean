import PhysicalBridges.CathedralSummitAllIsOneClosure

namespace PhysicalBridges.G3KoruUnifiedNStep

def iterate {α : Type} (g : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => g (iterate g n x)

def powNat (b : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => b * powNat b n

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

def KoruCorresponds {M : Type} (C : ContractionPillar M) (x y : M) : Prop :=
  C.dist x C.G * C.kDen ≤ C.dist y C.G * C.kDen

structure KoruHinge {S M : Type} (P : ProcessPillar S) (C : ContractionPillar M) where
  pi : S → M
  koruStep : ∀ s, KoruCorresponds C (pi (P.f s)) (C.phi (pi s))

structure KoruQuasiSixX3 {S M : Type} (P : ProcessPillar S) (C : ContractionPillar M)
    (hinge : KoruHinge P C) : Prop where
  kq_x3_1_no_ender : (S → Empty) → False
  kq_x3_2_unique : ∀ G', C.phi G' = G' → C.dist C.G G' = 0
  kq_x3_3_eternal : ∀ n, iterate C.phi n C.G = C.G
  kq_x3_4_conserved : ∀ n, P.energy (iterate P.f n P.s0) = P.energy P.s0
  kq_x3_5_koru_contracts : ∀ n,
    C.dist (hinge.pi (iterate P.f (n + 1) P.s0)) C.G * C.kDen ≤
      C.kNum * C.dist (hinge.pi (iterate P.f n P.s0)) C.G
  kq_x3_6_monotone : ∀ n, P.entropy P.s0 ≤ P.entropy (iterate P.f n P.s0)

-- N-step contraction decay: telescope the single-step bound
theorem koru_n_step_contraction_decay {S M : Type}
    (P : ProcessPillar S) (C : ContractionPillar M) (hinge : KoruHinge P C)
    (hQ : KoruQuasiSixX3 P C hinge) (N : Nat) :
    C.dist (hinge.pi (iterate P.f N P.s0)) C.G * powNat C.kDen N ≤
      powNat C.kNum N * C.dist (hinge.pi P.s0) C.G := by
  induction N with
  | zero =>
    show C.dist (hinge.pi P.s0) C.G * 1 ≤ 1 * C.dist (hinge.pi P.s0) C.G
    rw [Nat.mul_one, Nat.one_mul]
    exact Nat.le_refl _
  | succ k ih =>
    -- Goal: dist(pi(s_{k+1}), G) * (kDen * powNat kDen k) ≤ (kNum * powNat kNum k) * dist(pi(s0), G)
    show C.dist (hinge.pi (iterate P.f (k + 1) P.s0)) C.G * (C.kDen * powNat C.kDen k) ≤
         (C.kNum * powNat C.kNum k) * C.dist (hinge.pi P.s0) C.G
    -- Single-step bound: dist(pi(s_{k+1}), G) * kDen ≤ kNum * dist(pi(s_k), G)
    have hStep := hQ.kq_x3_5_koru_contracts k
    -- Scale the single-step bound by powNat kDen k on the right
    have hScaled : C.dist (hinge.pi (iterate P.f (k + 1) P.s0)) C.G * C.kDen * powNat C.kDen k ≤
                   C.kNum * C.dist (hinge.pi (iterate P.f k P.s0)) C.G * powNat C.kDen k :=
      Nat.mul_le_mul_right (powNat C.kDen k) hStep
    -- Reassociate LHS: a * b * c = a * (b * c)
    have hLHS : C.dist (hinge.pi (iterate P.f (k + 1) P.s0)) C.G * C.kDen * powNat C.kDen k =
                C.dist (hinge.pi (iterate P.f (k + 1) P.s0)) C.G * (C.kDen * powNat C.kDen k) :=
      Nat.mul_assoc _ _ _
    -- Reassociate RHS of scaled: kNum * dist * powNatDen = kNum * (dist * powNatDen)
    have hRHS1 : C.kNum * C.dist (hinge.pi (iterate P.f k P.s0)) C.G * powNat C.kDen k =
                 C.kNum * (C.dist (hinge.pi (iterate P.f k P.s0)) C.G * powNat C.kDen k) :=
      Nat.mul_assoc _ _ _
    -- Use IH: dist(pi(s_k), G) * powNat kDen k ≤ powNat kNum k * dist(pi(s0), G)
    have hChain : C.kNum * (C.dist (hinge.pi (iterate P.f k P.s0)) C.G * powNat C.kDen k) ≤
                  C.kNum * (powNat C.kNum k * C.dist (hinge.pi P.s0) C.G) :=
      Nat.mul_le_mul_left C.kNum ih
    -- Reassociate final: kNum * (powNat kNum k * dist) = (kNum * powNat kNum k) * dist
    have hFinal : C.kNum * (powNat C.kNum k * C.dist (hinge.pi P.s0) C.G) =
                  (C.kNum * powNat C.kNum k) * C.dist (hinge.pi P.s0) C.G :=
      (Nat.mul_assoc _ _ _).symm
    -- Chain: LHS = a*(b*c) ≤ kNum*(dist*powDen) ≤ kNum*(powNum*dist0) = (kNum*powNum)*dist0
    calc C.dist (hinge.pi (iterate P.f (k + 1) P.s0)) C.G * (C.kDen * powNat C.kDen k)
        = C.dist (hinge.pi (iterate P.f (k + 1) P.s0)) C.G * C.kDen * powNat C.kDen k := hLHS.symm
      _ ≤ C.kNum * C.dist (hinge.pi (iterate P.f k P.s0)) C.G * powNat C.kDen k := hScaled
      _ = C.kNum * (C.dist (hinge.pi (iterate P.f k P.s0)) C.G * powNat C.kDen k) := hRHS1
      _ ≤ C.kNum * (powNat C.kNum k * C.dist (hinge.pi P.s0) C.G) := hChain
      _ = (C.kNum * powNat C.kNum k) * C.dist (hinge.pi P.s0) C.G := hFinal

-- The unified N-step theorem
structure UnifiedNStep {S M : Type} (P : ProcessPillar S) (C : ContractionPillar M)
    (hinge : KoruHinge P C) (N : Nat) : Prop where
  conserved_n :
    P.energy (iterate P.f N P.s0) = P.energy P.s0
  koru_decay_n :
    C.dist (hinge.pi (iterate P.f N P.s0)) C.G * powNat C.kDen N ≤
      powNat C.kNum N * C.dist (hinge.pi P.s0) C.G
  entropy_monotone_n :
    P.entropy P.s0 ≤ P.entropy (iterate P.f N P.s0)

theorem koru_unified_n_step_theorem {S M : Type}
    (P : ProcessPillar S) (C : ContractionPillar M) (hinge : KoruHinge P C)
    (hQ : KoruQuasiSixX3 P C hinge) (N : Nat) :
    UnifiedNStep P C hinge N := by
  exact ⟨hQ.kq_x3_4_conserved N,
         koru_n_step_contraction_decay P C hinge hQ N,
         hQ.kq_x3_6_monotone N⟩

#print axioms koru_n_step_contraction_decay
#print axioms koru_unified_n_step_theorem

end PhysicalBridges.G3KoruUnifiedNStep
