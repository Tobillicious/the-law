/-!
# Pure G Operating State — Standalone Constructive Lean 4 Stack
Zero axioms, no Mathlib, no Hilbert space, and no `Delta` slack parameter in Koru-native quasi-commutation.
`hinge` denotes the projection bridge (`pi : S → M`) between process space `S` and contraction space `M`.
Where structural correspondence replaces flat `=`, the outward-spiral Koru (`🌀`) governs relational unfolding.
-/

def iterate {α : Type} (g : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => g (iterate g n x)

def powNat (b : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => powNat b n * b

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

def KoruCorresponds {M : Type} (C : ContractionPillar M) (x y : M) : Prop :=
  C.dist x C.G * C.kDen ≤ C.dist y C.G * C.kDen

structure KoruHinge {S M : Type} (P : ProcessPillar S) (C : ContractionPillar M) where
  pi : S → M
  koruStep : ∀ s, KoruCorresponds C (pi (P.f s)) (C.phi (pi s))

def StrictHinge.toKoruHinge {S M : Type} {P : ProcessPillar S} {C : ContractionPillar M}
    (hinge : StrictHinge P C) : KoruHinge P C where
  pi := hinge.pi
  koruStep := fun s => by
    unfold KoruCorresponds
    rw [hinge.commutes s]
    exact Nat.le_refl _

def ExactDecoder {M O : Type} (c : M → O) (live : M → Prop) : Type :=
  { dec : O → Bool // ∀ m, dec (c m) = true ↔ live m }

structure OriginalSixX3 {S M : Type} (P : ProcessPillar S) (C : ContractionPillar M)
    (hinge : StrictHinge P C) : Prop where
  x3_1_no_ender : (S → Empty) → False
  x3_2_unique : ∀ G', C.phi G' = G' → C.dist C.G G' = 0
  x3_3_eternal : ∀ n, iterate C.phi n C.G = C.G
  x3_4_conserved : ∀ n, P.energy (iterate P.f n P.s0) = P.energy P.s0
  x3_5_contracts : ∀ n,
    C.dist (hinge.pi (iterate P.f (n + 1) P.s0)) C.G * C.kDen ≤
      C.kNum * C.dist (hinge.pi (iterate P.f n P.s0)) C.G
  x3_6_monotone : ∀ n, P.entropy P.s0 ≤ P.entropy (iterate P.f n P.s0)

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

structure UnifiedNStep {S M : Type} (P : ProcessPillar S) (C : ContractionPillar M)
    (hinge : KoruHinge P C) (N : Nat) : Prop where
  conserved_n :
    P.energy (iterate P.f N P.s0) = P.energy P.s0
  koru_decay_n :
    C.dist (hinge.pi (iterate P.f N P.s0)) C.G * powNat C.kDen N ≤
      powNat C.kNum N * C.dist (hinge.pi P.s0) C.G
  entropy_monotone_n :
    P.entropy P.s0 ≤ P.entropy (iterate P.f N P.s0)

theorem triadic_g_bridge {S M : Type}
    (P : ProcessPillar S) (C : ContractionPillar M) (hinge : StrictHinge P C) :
    (((S → Empty) → False) ∧
     (∀ n, P.energy (iterate P.f n P.s0) = P.energy P.s0) ∧
     (∀ n, P.entropy P.s0 ≤ P.entropy (iterate P.f n P.s0))) ∧
    ((∀ G', C.phi G' = G' → C.dist C.G G' = 0) ∧
     (∀ n, iterate C.phi n C.G = C.G)) ∧
    (∀ n, C.dist (hinge.pi (iterate P.f (n + 1) P.s0)) C.G * C.kDen ≤
          C.kNum * C.dist (hinge.pi (iterate P.f n P.s0)) C.G) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro ender; exact nomatch (ender P.s0)
  · intro n
    induction n with
    | zero => rfl
    | succ k ih => simp [iterate, P.conserves, ih]
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
        simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right C.kLt (Nat.succ_pos d)
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hLt hC)
  · intro n
    induction n with
    | zero => rfl
    | succ k ih => simp [iterate, ih, C.hFixed]
  · intro n
    have hStep : hinge.pi (iterate P.f (n + 1) P.s0) =
        C.phi (hinge.pi (iterate P.f n P.s0)) := by
      simpa [iterate] using hinge.commutes (iterate P.f n P.s0)
    rw [hStep]
    have hC := C.contracts (hinge.pi (iterate P.f n P.s0)) C.G
    rw [C.hFixed] at hC
    exact hC

theorem hinge_alone_insufficient :
    ∃ (pi : Empty → Empty), Function.Injective pi ∧ (Empty → False) :=
  ⟨id, And.intro (fun a₁ => nomatch a₁) (fun x => nomatch x)⟩

theorem assemble_six_x3 {S M : Type} (P : ProcessPillar S) (C : ContractionPillar M)
    (hinge : StrictHinge P C) : OriginalSixX3 P C hinge := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ender; exact nomatch (ender P.s0)
  · intro G' hG'
    cases hEq : C.dist C.G G' with
    | zero => rfl
    | succ d =>
      exfalso
      have hC := C.contracts C.G G'
      rw [C.hFixed, hG', hEq] at hC
      have hLt : C.kNum * (d + 1) < (d + 1) * C.kDen := by
        simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right C.kLt (Nat.succ_pos d)
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hLt hC)
  · intro n
    induction n with
    | zero => rfl
    | succ k ih => simp [iterate, ih, C.hFixed]
  · intro n
    induction n with
    | zero => rfl
    | succ k ih => simp [iterate, P.conserves, ih]
  · intro n
    have hStep : hinge.pi (iterate P.f (n + 1) P.s0) =
        C.phi (hinge.pi (iterate P.f n P.s0)) := by
      simpa [iterate] using hinge.commutes (iterate P.f n P.s0)
    rw [hStep]
    have hC := C.contracts (hinge.pi (iterate P.f n P.s0)) C.G
    rw [C.hFixed] at hC
    exact hC
  · intro n
    induction n with
    | zero => exact Nat.le_refl _
    | succ k ih => exact Nat.le_trans ih (P.monotoneEntropy (iterate P.f k P.s0))

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

theorem hinge_live_persistence_and_contraction {S M : Type}
    (P : ProcessPillar S) (C : ContractionPillar M) (hinge : StrictHinge P C)
    (live : M → Prop)
    (hClosed : ∀ m, live m → live (C.phi m))
    (hInitLive : live (hinge.pi P.s0))
    (n : Nat) :
    live (hinge.pi (iterate P.f n P.s0)) ∧
    (C.dist (hinge.pi (iterate P.f (n + 1) P.s0)) C.G * C.kDen ≤
      C.kNum * C.dist (hinge.pi (iterate P.f n P.s0)) C.G) := by
  refine ⟨?_, ?_⟩
  · induction n with
    | zero => exact hInitLive
    | succ k ih =>
      have hStep : hinge.pi (iterate P.f (k + 1) P.s0) =
          C.phi (hinge.pi (iterate P.f k P.s0)) := by
        simpa [iterate] using hinge.commutes (iterate P.f k P.s0)
      rw [hStep]
      exact hClosed _ ih
  · have hStep : hinge.pi (iterate P.f (n + 1) P.s0) =
        C.phi (hinge.pi (iterate P.f n P.s0)) := by
      simpa [iterate] using hinge.commutes (iterate P.f n P.s0)
    rw [hStep]
    have hC := C.contracts (hinge.pi (iterate P.f n P.s0)) C.G
    rw [C.hFixed] at hC
    exact hC

theorem koru_quasi_six_x3 {S M : Type} (P : ProcessPillar S) (C : ContractionPillar M)
    (hinge : KoruHinge P C) : KoruQuasiSixX3 P C hinge := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ender; exact nomatch (ender P.s0)
  · intro G' hG'
    cases hEq : C.dist C.G G' with
    | zero => rfl
    | succ d =>
      exfalso
      have hC := C.contracts C.G G'
      rw [C.hFixed, hG', hEq] at hC
      have hLt : C.kNum * (d + 1) < (d + 1) * C.kDen := by
        simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right C.kLt (Nat.succ_pos d)
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hLt hC)
  · intro n
    induction n with
    | zero => rfl
    | succ k ih => simp [iterate, ih, C.hFixed]
  · intro n
    induction n with
    | zero => rfl
    | succ k ih => simp [iterate, P.conserves, ih]
  · intro n
    have hKoru : KoruCorresponds C
        (hinge.pi (iterate P.f (n + 1) P.s0))
        (C.phi (hinge.pi (iterate P.f n P.s0))) := by
      simpa [iterate] using hinge.koruStep (iterate P.f n P.s0)
    have hContract : C.dist (C.phi (hinge.pi (iterate P.f n P.s0))) C.G * C.kDen ≤
        C.kNum * C.dist (hinge.pi (iterate P.f n P.s0)) C.G := by
      have hC := C.contracts (hinge.pi (iterate P.f n P.s0)) C.G
      rw [C.hFixed] at hC
      exact hC
    exact Nat.le_trans hKoru hContract
  · intro n
    induction n with
    | zero => exact Nat.le_refl _
    | succ k ih => exact Nat.le_trans ih (P.monotoneEntropy (iterate P.f k P.s0))

theorem koru_n_step_contraction_decay {S M : Type}
    (P : ProcessPillar S) (C : ContractionPillar M) (hinge : KoruHinge P C)
    (hQ : KoruQuasiSixX3 P C hinge) (N : Nat) :
    C.dist (hinge.pi (iterate P.f N P.s0)) C.G * powNat C.kDen N ≤
      powNat C.kNum N * C.dist (hinge.pi P.s0) C.G := by
  induction N with
  | zero =>
    simp [iterate, powNat]
  | succ k ih =>
    have hStep :
        C.dist (hinge.pi (iterate P.f (k + 1) P.s0)) C.G * C.kDen ≤
          C.kNum * C.dist (hinge.pi (iterate P.f k P.s0)) C.G :=
      hQ.kq_x3_5_koru_contracts k
    have hLeft :
        C.dist (hinge.pi (iterate P.f (k + 1) P.s0)) C.G * powNat C.kDen (k + 1) ≤
          C.kNum * (C.dist (hinge.pi (iterate P.f k P.s0)) C.G * powNat C.kDen k) := by
      have hMul := Nat.mul_le_mul_right (powNat C.kDen k) hStep
      simpa [powNat, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hMul
    have hRight :
        C.kNum * (C.dist (hinge.pi (iterate P.f k P.s0)) C.G * powNat C.kDen k) ≤
          powNat C.kNum (k + 1) * C.dist (hinge.pi P.s0) C.G := by
      have hMul := Nat.mul_le_mul_left C.kNum ih
      simpa [powNat, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hMul
    exact Nat.le_trans hLeft hRight

theorem koru_unified_n_step_theorem {S M : Type}
    (P : ProcessPillar S) (C : ContractionPillar M) (hinge : KoruHinge P C)
    (hQ : KoruQuasiSixX3 P C hinge) (N : Nat) :
    UnifiedNStep P C hinge N := by
  refine ⟨?_, ?_, ?_⟩
  · exact hQ.kq_x3_4_conserved N
  · exact koru_n_step_contraction_decay P C hinge hQ N
  · exact hQ.kq_x3_6_monotone N

theorem koru_corresponds_transitive {M : Type} (C : ContractionPillar M)
    {x y z : M} (hxy : KoruCorresponds C x y) (hyz : KoruCorresponds C y z) :
    KoruCorresponds C x z :=
  Nat.le_trans hxy hyz

theorem koru_successive_bound_step {S M : Type}
    (P : ProcessPillar S) (C : ContractionPillar M) (hinge : KoruHinge P C)
    (hQ : KoruQuasiSixX3 P C hinge) (N : Nat) :
    C.dist (hinge.pi (iterate P.f (N + 1) P.s0)) C.G * powNat C.kDen (N + 1) ≤
      C.kNum * (powNat C.kNum N * C.dist (hinge.pi P.s0) C.G) := by
  have hStep :
      C.dist (hinge.pi (iterate P.f (N + 1) P.s0)) C.G * C.kDen ≤
        C.kNum * C.dist (hinge.pi (iterate P.f N P.s0)) C.G :=
    hQ.kq_x3_5_koru_contracts N
  have hLeft :
      C.dist (hinge.pi (iterate P.f (N + 1) P.s0)) C.G * powNat C.kDen (N + 1) ≤
        C.kNum * (C.dist (hinge.pi (iterate P.f N P.s0)) C.G * powNat C.kDen N) := by
    have hMul := Nat.mul_le_mul_right (powNat C.kDen N) hStep
    simpa [powNat, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hMul
  have hIH :
      C.dist (hinge.pi (iterate P.f N P.s0)) C.G * powNat C.kDen N ≤
        powNat C.kNum N * C.dist (hinge.pi P.s0) C.G :=
    koru_n_step_contraction_decay P C hinge hQ N
  have hRight :
      C.kNum * (C.dist (hinge.pi (iterate P.f N P.s0)) C.G * powNat C.kDen N) ≤
        C.kNum * (powNat C.kNum N * C.dist (hinge.pi P.s0) C.G) :=
    Nat.mul_le_mul_left C.kNum hIH
  exact Nat.le_trans hLeft hRight

theorem koru_corresponds_zero_distance {M : Type} (C : ContractionPillar M)
    (hDenPos : 0 < C.kDen) {x y : M}
    (hKoru : KoruCorresponds C x y) (hZeroY : C.dist y C.G = 0) :
    C.dist x C.G = 0 := by
  unfold KoruCorresponds at hKoru
  rw [hZeroY, Nat.zero_mul] at hKoru
  have hProdZero : C.dist x C.G * C.kDen = 0 := Nat.eq_zero_of_le_zero hKoru
  cases Nat.mul_eq_zero.mp hProdZero with
  | inl hDistZero => exact hDistZero
  | inr hDenZero => exact absurd hDenZero (Nat.ne_of_gt hDenPos)

theorem koru_fixed_point_stability_and_zero_pinning {S M : Type}
    (P : ProcessPillar S) (C : ContractionPillar M) (hinge : KoruHinge P C)
    (hQ : KoruQuasiSixX3 P C hinge) :
    (∀ n, iterate C.phi n C.G = C.G) ∧
    (∀ x, C.dist x C.G = 0 → C.dist (C.phi x) C.G = 0) ∧
    (∀ n, C.dist (hinge.pi (iterate P.f n P.s0)) C.G = 0 →
      C.dist (hinge.pi (iterate P.f (n + 1) P.s0)) C.G = 0) := by
  have hDenPos : 0 < C.kDen := Nat.lt_of_le_of_lt (Nat.zero_le _) C.kLt
  refine ⟨?_, ?_, ?_⟩
  · exact hQ.kq_x3_3_eternal
  · intro x hxZero
    have hC := C.contracts x C.G
    rw [C.hFixed, hxZero, Nat.mul_zero] at hC
    have hProdZero : C.dist (C.phi x) C.G * C.kDen = 0 := Nat.eq_zero_of_le_zero hC
    cases Nat.mul_eq_zero.mp hProdZero with
    | inl hPhiZero => exact hPhiZero
    | inr hDenZero => exact absurd hDenZero (Nat.ne_of_gt hDenPos)
  · intro n hnZero
    have hStep := hQ.kq_x3_5_koru_contracts n
    rw [hnZero, Nat.mul_zero] at hStep
    have hProdZero :
        C.dist (hinge.pi (iterate P.f (n + 1) P.s0)) C.G * C.kDen = 0 :=
      Nat.eq_zero_of_le_zero hStep
    cases Nat.mul_eq_zero.mp hProdZero with
    | inl hNextZero => exact hNextZero
    | inr hDenZero => exact absurd hDenZero (Nat.ne_of_gt hDenPos)

#print axioms triadic_g_bridge
#print axioms hinge_alone_insufficient
#print axioms assemble_six_x3
#print axioms strict_hinge_category_error
#print axioms hinge_live_persistence_and_contraction
#print axioms koru_quasi_six_x3
#print axioms koru_n_step_contraction_decay
#print axioms koru_unified_n_step_theorem
#print axioms koru_corresponds_transitive
#print axioms koru_successive_bound_step
#print axioms koru_corresponds_zero_distance
#print axioms koru_fixed_point_stability_and_zero_pinning
