import Appendix
open Set Filter
open scoped Topology
namespace Asakura

/-- The parameter cube, with its inherited maximum-norm metric. -/
abbrev UnitCube (d : ℕ) := {s : Fin d → ℝ // ∀ i, s i ∈ Set.Icc (0:ℝ) 1}

/-- A dyadic grid vertex indexed by its integer coordinates. -/
noncomputable def gridPoint {d : ℕ} (m : ℕ) (v : Fin d → Fin (2^m+1)) : UnitCube d :=
  ⟨fun i => (v i).val / (2:ℝ)^m, by
    intro i
    constructor
    · positivity
    · apply (div_le_one (by positivity : (0:ℝ) < 2^m)).mpr
      have h : (v i).val ≤ 2^m := Nat.le_of_lt_succ (v i).isLt
      exact_mod_cast h⟩

/-- All grid levels, viewed as a subset of the cube. -/
def DyadicSet (d : ℕ) : Set (UnitCube d) := {s | ∃ m v, gridPoint m v = s}

/-- Floor indices lie in the finite grid indexing type. -/
noncomputable def roundIndex {d : ℕ} (m : ℕ) (s : UnitCube d) (i : Fin d) : Fin (2^m+1) :=
  ⟨⌊(2:ℝ)^m*s.val i⌋.toNat, by
    have hreal : (⌊(2:ℝ)^m*s.val i⌋ : ℝ) ≤ (2:ℝ)^m := by
      exact (Int.floor_le _).trans (by nlinarith [(s.property i).2, pow_pos (by norm_num : (0:ℝ)<2) m])
    have hint : ⌊(2:ℝ)^m*s.val i⌋ ≤ ((2^m : ℕ) : ℤ) := by exact_mod_cast hreal
    have hf0 : 0 ≤ ⌊(2:ℝ)^m*s.val i⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg (by positivity) (s.property i).1)
    have hint' : (⌊(2:ℝ)^m*s.val i⌋.toNat : ℤ) ≤ ((2^m : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hf0]
      exact hint
    have hnat : ⌊(2:ℝ)^m*s.val i⌋.toNat ≤ 2^m := by exact_mod_cast hint'
    exact Nat.lt_succ_of_le hnat⟩

noncomputable def roundCube {d : ℕ} (m : ℕ) (s : UnitCube d) : UnitCube d :=
  gridPoint m (roundIndex m s)

theorem roundCube_coordinate {d : ℕ} (m : ℕ) (s : UnitCube d) (i : Fin d) :
    (roundCube m s).val i = roundDown m (s.val i) := by
  have hf0 : 0 ≤ ⌊(2:ℝ)^m*s.val i⌋ :=
    Int.floor_nonneg.mpr (mul_nonneg (by positivity) (s.property i).1)
  change ((⌊(2:ℝ)^m*s.val i⌋.toNat : ℕ) : ℝ) / (2:ℝ)^m = _
  unfold roundDown
  congr 1
  exact_mod_cast Int.toNat_of_nonneg hf0

theorem roundCube_mem {d : ℕ} (m : ℕ) (s : UnitCube d) : roundCube m s ∈ DyadicSet d :=
  ⟨m, roundIndex m s, rfl⟩

theorem roundCube_error {d : ℕ} (m : ℕ) (s : UnitCube d) :
    dist (roundCube m s) s ≤ (1/2 : ℝ)^m := by
  change ‖(roundCube m s).val - s.val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change |(roundCube m s).val i - s.val i| ≤ _
  rw [roundCube_coordinate, abs_of_nonpos (sub_nonpos.mpr (roundDown_le m _))]
  have h := roundDown_error m (s.val i)
  have heq : 1/(2:ℝ)^m = (1/2:ℝ)^m := by rw [one_div_pow]
  rw [heq] at h
  linarith

theorem roundCube_tendsto {d : ℕ} (s : UnitCube d) :
    Tendsto (fun m => roundCube m s) atTop (𝓝 s) := by
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun _ => dist_nonneg) (fun m => roundCube_error m s)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

theorem dyadicSet_dense (d : ℕ) : Dense (DyadicSet d) := by
  intro s
  exact mem_closure_iff_seq_limit.mpr ⟨fun m => roundCube m s,
    fun m => roundCube_mem m s, roundCube_tendsto s⟩

theorem dyadicSet_countable (d : ℕ) : (DyadicSet d).Countable := by
  have heq : DyadicSet d = ⋃ m : ℕ, Set.range (@gridPoint d m) := by
    ext s
    simp only [DyadicSet, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_range]
  rw [heq]
  exact Set.countable_iUnion (fun m => Set.to_countable _)

theorem roundCube_fixes_finer {d : ℕ} (k l : ℕ) (v : Fin d → Fin (2^k+1)) :
    roundCube (k+l) (gridPoint k v) = gridPoint k v := by
  apply Subtype.ext
  funext i
  rw [roundCube_coordinate]
  exact roundDown_eventual k l ((v i).val : ℤ)

theorem roundCube_eventually_fixed {d : ℕ} (s : UnitCube d) (hs : s ∈ DyadicSet d) :
    ∃ N, ∀ n ≥ N, roundCube n s = s := by
  obtain ⟨k, v, rfl⟩ := hs
  refine ⟨k, fun n hn => ?_⟩
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact roundCube_fixes_finer k l v
end Asakura
