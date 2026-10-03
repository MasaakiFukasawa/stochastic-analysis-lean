import CubeGrid
import GridCardinality
import FiniteMaximum
open Set MeasureTheory
namespace Asakura

instance gridEdge_nonempty (d N : ℕ) : Nonempty (GridEdge d N) :=
  ⟨⟨(fun _ => ⟨0, Nat.zero_lt_succ _⟩, fun _ => ⟨0, Nat.zero_lt_succ _⟩), by intro i; simp⟩⟩

/-- View a coarse-grid vertex on the next finer grid. -/
def gridLift {d : ℕ} (m : ℕ) (v : Fin d → Fin (2^m+1)) : Fin d → Fin (2^(m+1)+1) :=
  fun i => ⟨2*(v i).val, by
    have h := (v i).isLt
    rw [pow_succ]
    omega⟩

theorem gridPoint_lift {d : ℕ} (m : ℕ) (v : Fin d → Fin (2^m+1)) :
    gridPoint (m+1) (gridLift m v) = gridPoint m v := by
  apply Subtype.ext
  funext i
  change ((2*(v i).val : ℕ) : ℝ)/(2:ℝ)^(m+1) = (v i).val/(2:ℝ)^m
  push_cast
  rw [pow_succ]
  field_simp

/-- Transfer a coordinatewise metric adjacency bound to the integer grid edge type. -/
theorem grid_indices_adjacent {d : ℕ} (m : ℕ) (v w : Fin d → Fin (2^m+1))
    (h : ∀ i, |(gridPoint m v).val i - (gridPoint m w).val i| ≤ 1/(2:ℝ)^m) :
    ∀ i, |((v i).val : ℤ) - ((w i).val : ℤ)| ≤ 1 := by
  intro i
  have hi := h i
  change |((v i).val : ℝ)/(2:ℝ)^m - ((w i).val : ℝ)/(2:ℝ)^m| ≤ 1/(2:ℝ)^m at hi
  rw [← sub_div, abs_div, abs_of_pos (by positivity : (0:ℝ)<2^m)] at hi
  have hr : |((v i).val : ℝ) - ((w i).val : ℝ)| ≤ 1 :=
    (div_le_div_iff_of_pos_right (by positivity : (0:ℝ)<2^m)).mp hi
  exact_mod_cast hr

noncomputable def cubeIncrementMax {d : ℕ} {Ω : Type*}
    (X : UnitCube d → Ω → ℝ) (m : ℕ) : Ω → ℝ :=
  finiteNormMax (fun e : GridEdge d (2^m) =>
    fun ω => X (gridPoint m e.val.1) ω - X (gridPoint m e.val.2) ω)

theorem cubeIncrementMax_measurable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X : UnitCube d → Ω → ℝ) (hX : ∀ s, Measurable (X s)) (m : ℕ) :
    Measurable (cubeIncrementMax X m) :=
  finiteNormMax_measurable _ (fun e => (hX _).sub (hX _))

theorem cubeIncrementMax_nonneg {d : ℕ} {Ω : Type*}
    (X : UnitCube d → Ω → ℝ) (m : ℕ) (ω : Ω) : 0 ≤ cubeIncrementMax X m ω :=
  finiteNormMax_nonneg _ ω

theorem cubeIncrementMax_near {d : ℕ} {Ω : Type*}
    (X : UnitCube d → Ω → ℝ) (m : ℕ) (s t : UnitCube d)
    (h : dist s t ≤ (1/2 : ℝ)^m) (ω : Ω) :
    dist (X (roundCube m s) ω) (X (roundCube m t) ω) ≤ cubeIncrementMax X m ω := by
  have hadj : ∀ i, |((roundIndex m s i).val : ℤ) - ((roundIndex m t i).val : ℤ)| ≤ 1 := by
    apply grid_indices_adjacent
    intro i
    change |(roundCube m s).val i - (roundCube m t).val i| ≤ _
    rw [roundCube_coordinate, roundCube_coordinate]
    apply roundDown_adjacent
    have hi := norm_le_pi_norm (s.val - t.val) i
    have hst : ‖s.val - t.val‖ ≤ 1/(2:ℝ)^m := by
      change ‖s.val - t.val‖ ≤ (1/2 : ℝ)^m at h
      simpa only [one_div_pow] using h
    exact hi.trans hst
  let e : GridEdge d (2^m) := ⟨(roundIndex m s, roundIndex m t), hadj⟩
  exact le_finiteNormMax (fun e : GridEdge d (2^m) => fun ω =>
    X (gridPoint m e.val.1) ω - X (gridPoint m e.val.2) ω) e ω

theorem cubeIncrementMax_step {d : ℕ} {Ω : Type*}
    (X : UnitCube d → Ω → ℝ) (m : ℕ) (s : UnitCube d) (ω : Ω) :
    dist (X (roundCube (m+1) s) ω) (X (roundCube m s) ω) ≤ cubeIncrementMax X (m+1) ω := by
  have hadj : ∀ i, |((roundIndex (m+1) s i).val : ℤ) -
      ((gridLift m (roundIndex m s) i).val : ℤ)| ≤ 1 := by
    apply grid_indices_adjacent
    intro i
    rw [gridPoint_lift]
    change |(roundCube (m+1) s).val i - (roundCube m s).val i| ≤ _
    rw [roundCube_coordinate, roundCube_coordinate]
    exact (roundDown_refinement m (s.val i)).2
  let e : GridEdge d (2^(m+1)) := ⟨(roundIndex (m+1) s, gridLift m (roundIndex m s)), hadj⟩
  have h := le_finiteNormMax
    (fun e : GridEdge d (2^(m+1)) => fun ω =>
      X (gridPoint (m+1) e.val.1) ω - X (gridPoint (m+1) e.val.2) ω) e ω
  dsimp [e] at h
  rw [gridPoint_lift] at h
  exact h
end Asakura
