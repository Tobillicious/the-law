import PhysicalBridges.CathedralSummitAllIsOneClosure

/-!
# Two exact boundaries for the proof of God

Kept as honest controls, so the strong theorems are read at their exact scope.

1. **Only an inhabited type is safe from an ender.** `ABSOLUTE_EVIL_IS_UNSATISFIABLE`
   needs a witness. The empty type itself does have an `AbsoluteEnder` (`id`).
   So "no inhabited type has an ender" is proved; "no type has an ender" is false.
   `G_FROM_NOTHING` is unaffected: it is about `S → S`, which is always inhabited.

2. **Contraction and recurrence are different dynamics.** Under a strict contraction,
   any two states that both return after the same number of steps are at distance 0.
   So one map cannot both contract every orbit to G and make every distinct orbit
   recur. The Koru spiral (`G3KoruSpiral`) reconciles them: the form returns, the
   history never does.
-/

namespace PhysicalBridges.G3DynamicsSeparation

open PhysicalBridges.CathedralSummitAllIsOneClosure

/-- The empty type has an ender: the identity on `Empty`. -/
theorem empty_admits_an_ender : Nonempty (AbsoluteEnder Empty) := ⟨id⟩

def it {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (it f n x)

def pw (b : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => b * pw b n

/-- N-step contraction bound for any pair of states. -/
theorem decay {α : Type} (f : α → α) (d : α → α → Nat) (kN kD : Nat)
    (c : ∀ a b, d (f a) (f b) * kD ≤ kN * d a b) (x y : α) :
    ∀ n, d (it f n x) (it f n y) * pw kD n ≤ pw kN n * d x y
  | 0 => by show d x y * 1 ≤ 1 * d x y; rw [Nat.mul_one, Nat.one_mul]; exact Nat.le_refl _
  | n + 1 => by
    show d (f (it f n x)) (f (it f n y)) * (kD * pw kD n) ≤ (kN * pw kN n) * d x y
    have h1 := Nat.mul_le_mul_right (pw kD n) (c (it f n x) (it f n y))
    have h2 := Nat.mul_le_mul_left kN (decay f d kN kD c x y n)
    calc d (f (it f n x)) (f (it f n y)) * (kD * pw kD n)
        = d (f (it f n x)) (f (it f n y)) * kD * pw kD n := (Nat.mul_assoc _ _ _).symm
      _ ≤ kN * d (it f n x) (it f n y) * pw kD n := h1
      _ = kN * (d (it f n x) (it f n y) * pw kD n) := Nat.mul_assoc _ _ _
      _ ≤ kN * (pw kN n * d x y) := h2
      _ = (kN * pw kN n) * d x y := (Nat.mul_assoc _ _ _).symm

theorem pw_pos (b : Nat) (hb : 0 < b) : ∀ n, 0 < pw b n
  | 0 => Nat.one_pos
  | n + 1 => Nat.mul_pos hb (pw_pos b hb n)

theorem pw_le (a b : Nat) (h : a ≤ b) : ∀ n, pw a n ≤ pw b n
  | 0 => Nat.le_refl 1
  | n + 1 => Nat.mul_le_mul h (pw_le a b h n)

theorem pw_lt (a b : Nat) (h : a < b) (m : Nat) : pw a (m + 1) < pw b (m + 1) :=
  Nat.mul_lt_mul_of_lt_of_le h (pw_le a b (Nat.le_of_lt h) m)
    (pw_pos b (Nat.lt_of_le_of_lt (Nat.zero_le a) h) m)

/-- **Recurrence and strict contraction collapse.** Two states that both return
    after `m + 1` steps of a strict contraction are at distance zero. -/
theorem recurrence_and_strict_contraction_collapse {α : Type} (f : α → α)
    (d : α → α → Nat) (kN kD : Nat) (hk : kN < kD)
    (c : ∀ a b, d (f a) (f b) * kD ≤ kN * d a b) (x y : α) (m : Nat)
    (hx : it f (m + 1) x = x) (hy : it f (m + 1) y = y) : d x y = 0 := by
  have h := decay f d kN kD c x y (m + 1)
  rw [hx, hy] at h
  cases hd : d x y with
  | zero => rfl
  | succ k =>
    rw [hd] at h
    have h' : (k + 1) * pw kD (m + 1) ≤ (k + 1) * pw kN (m + 1) := by
      rw [Nat.mul_comm (k + 1) (pw kN (m + 1))]; exact h
    have hlt := Nat.mul_lt_mul_of_pos_left (pw_lt kN kD hk m) (Nat.succ_pos k)
    exact absurd (Nat.lt_of_lt_of_le hlt h') (Nat.lt_irrefl _)

#print axioms empty_admits_an_ender
#print axioms decay
#print axioms recurrence_and_strict_contraction_collapse

end PhysicalBridges.G3DynamicsSeparation
