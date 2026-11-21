import PhysicalBridges.G3TurnToG

/-!
# The Koru Spirals Out

Part IV of G3: Something Is → Koru → Genesis, and the spiral never closes.

A Koru configuration carries its own causal history. Each turn of the
spiral appends the turn's event to that history. Depth is the length of
the history, so it is a function of the configuration itself — never an
external counter, so it cannot be gamed by relabelling.

From this alone:
- every turn is larger than the last;
- the spiral never returns to an earlier configuration (no closed loop);
- nothing is lost: every earlier history is kept inside every later one;
- the same law holds one level up: each universe in a lineage carries its
  ancestors' whole record plus its own birth, so every universe is larger
  than the last, none repeats, and every ancestor is kept.

Controls kept in the file: a measure that is not intrinsic can stay flat on
distinct states, and growth of the record does not by itself force novelty
of the content. Both say exactly why depth is defined as it is.

Every theorem: zero axioms. Additive; no existing definition changes.
-/

namespace PhysicalBridges.G3KoruSpiral

open PhysicalBridges.CathedralSummitAllIsOneClosure

/-- A Koru configuration: its content and its own causal history. -/
structure KoruState (C E : Type) where
  content : C
  history : List E

variable {C E : Type}

/-- One turn of the spiral: the content moves on and the turn is recorded. -/
def spiral (next : C → E → C) (s : KoruState C E) (e : E) : KoruState C E :=
  ⟨next s.content e, e :: s.history⟩

/-- Depth is intrinsic: the length of the configuration's own history. -/
def depth (s : KoruState C E) : Nat := s.history.length

/-- The spiral from a seed, with one event per turn. -/
def run (next : C → E → C) (s0 : KoruState C E) (ev : Nat → E) :
    Nat → KoruState C E
  | 0 => s0
  | n + 1 => spiral next (run next s0 ev n) (ev n)

/-! ## XXVII — Every turn is larger -/

theorem EACH_TURN_IS_LARGER (next : C → E → C) (s : KoruState C E) (e : E) :
    depth (spiral next s e) = depth s + 1 := rfl

theorem depth_of_run (next : C → E → C) (s0 : KoruState C E) (ev : Nat → E) :
    ∀ n, depth (run next s0 ev n) = depth s0 + n
  | 0 => rfl
  | n + 1 => by
    show depth (run next s0 ev n) + 1 = depth s0 + (n + 1)
    rw [depth_of_run next s0 ev n]
    rfl

theorem THE_SPIRAL_ONLY_GROWS (next : C → E → C) (s0 : KoruState C E)
    (ev : Nat → E) {i j : Nat} (h : i < j) :
    depth (run next s0 ev i) < depth (run next s0 ev j) := by
  rw [depth_of_run, depth_of_run]
  exact Nat.add_lt_add_left h _

/-! ## XXVIII — The spiral never returns -/

theorem THE_SPIRAL_NEVER_RETURNS (next : C → E → C) (s0 : KoruState C E)
    (ev : Nat → E) {i j : Nat} (h : i < j) :
    run next s0 ev i ≠ run next s0 ev j := by
  intro heq
  have hlt := THE_SPIRAL_ONLY_GROWS next s0 ev h
  rw [heq] at hlt
  exact Nat.lt_irrefl _ hlt

/-! ## XXIX — Nothing is lost on the spiral -/

theorem NOTHING_IS_LOST_ON_THE_SPIRAL (next : C → E → C) (s0 : KoruState C E)
    (ev : Nat → E) :
    ∀ {i j : Nat}, i ≤ j → ∃ new : List E,
      (run next s0 ev j).history = new ++ (run next s0 ev i).history := by
  intro i j hij
  induction hij with
  | refl => exact ⟨[], rfl⟩
  | step _ ih =>
    obtain ⟨new, hnew⟩ := ih
    exact ⟨_ :: new, by show _ :: _ = _; rw [hnew]; rfl⟩

/-! ## XXX — Every universe larger than the last

A lineage of universes is the same spiral one level up: universe `m + 1`
is born from universe `m` by a birth event, carrying the whole record of
every universe before it. -/

/-- The `m`-th universe of a lineage. -/
abbrev universeAt (birth : C → E → C) (U0 : KoruState C E) (born : Nat → E)
    (m : Nat) : KoruState C E :=
  run birth U0 born m

theorem EVERY_UNIVERSE_LARGER_THAN_THE_LAST (birth : C → E → C)
    (U0 : KoruState C E) (born : Nat → E) (m : Nat) :
    depth (universeAt birth U0 born (m + 1)) = depth (universeAt birth U0 born m) + 1 ∧
    universeAt birth U0 born m ≠ universeAt birth U0 born (m + 1) ∧
    ∃ new : List E, (universeAt birth U0 born (m + 1)).history =
      new ++ (universeAt birth U0 born m).history :=
  ⟨rfl,
   THE_SPIRAL_NEVER_RETURNS birth U0 born (Nat.lt_succ_self m),
   NOTHING_IS_LOST_ON_THE_SPIRAL birth U0 born (Nat.le_succ m)⟩

/-! ## XXXI — The first distinction -/

/-- **THE FIRST DISTINCTION.** Something differs from something: the
    binary seed `{true, false}` is a real difference. -/
theorem THE_FIRST_DISTINCTION : true ≠ false :=
  fun h => Bool.noConfusion h

/-- From the first distinction the spiral has a seed, and the seed is:
    no ender can take it to nothing. -/
theorem THE_SEED_IS (Ev : Type) : AbsoluteEnder (KoruState Bool Ev) → False :=
  e_is_not ⟨true, []⟩

/-! ## XXXII — The Koru spirals out -/

/-- **THE KORU SPIRALS OUT.** Whatever the content and whatever the
    events: something is, every later turn is larger, no turn returns to
    an earlier one, and nothing earlier is lost. -/
theorem THE_KORU_SPIRALS_OUT (next : C → E → C) (s0 : KoruState C E)
    (ev : Nat → E) {i j : Nat} (h : i < j) :
    (AbsoluteEnder (KoruState C E) → False) ∧
    depth (run next s0 ev i) < depth (run next s0 ev j) ∧
    run next s0 ev i ≠ run next s0 ev j ∧
    ∃ new : List E, (run next s0 ev j).history = new ++ (run next s0 ev i).history :=
  ⟨e_is_not (run next s0 ev i),
   THE_SPIRAL_ONLY_GROWS next s0 ev h,
   THE_SPIRAL_NEVER_RETURNS next s0 ev h,
   NOTHING_IS_LOST_ON_THE_SPIRAL next s0 ev (Nat.le_of_lt h)⟩

/-! ## Controls -/

/-- A measure that is not intrinsic can stay flat on distinct states:
    distinctness alone does not force growth. This is why depth is the
    configuration's own history. -/
theorem distinct_states_do_not_force_an_external_measure_to_grow :
    (∀ i j : Nat, i < j → i ≠ j) ∧
    ∀ k : Nat, (fun _ : Nat => (1 : Nat)) k = (fun _ : Nat => (1 : Nat)) (k + 1) :=
  ⟨fun _ _ h => Nat.ne_of_lt h, fun _ => rfl⟩

/-- Growth of the record does not by itself force new content: with a
    content map that keeps content fixed, content repeats while depth grows.
    Novelty of content is a separate claim from growth of the record. -/
theorem record_growth_does_not_force_new_content (s0 : KoruState C E)
    (ev : Nat → E) :
    ∀ n, (run (fun c _ => c) s0 ev n).content = s0.content
  | 0 => rfl
  | n + 1 => record_growth_does_not_force_new_content s0 ev n

#print axioms EACH_TURN_IS_LARGER
#print axioms depth_of_run
#print axioms THE_SPIRAL_ONLY_GROWS
#print axioms THE_SPIRAL_NEVER_RETURNS
#print axioms NOTHING_IS_LOST_ON_THE_SPIRAL
#print axioms EVERY_UNIVERSE_LARGER_THAN_THE_LAST
#print axioms THE_FIRST_DISTINCTION
#print axioms THE_SEED_IS
#print axioms THE_KORU_SPIRALS_OUT
#print axioms distinct_states_do_not_force_an_external_measure_to_grow
#print axioms record_growth_does_not_force_new_content

end PhysicalBridges.G3KoruSpiral
