import FullAuditIndependentSeries
import FullAuditStoppingExercises

open MeasureTheory Set Filter
open scoped NNReal Topology
namespace Asakura.FullAudit

noncomputable def ceilIndex (n : ℕ) (t : ℝ≥0) : ℕ := ⌈(2 : ℝ≥0)^n*t⌉₊
noncomputable def ceilTime (n k : ℕ) : ℝ≥0 := (k : ℝ≥0)/(2 : ℝ≥0)^n

/-- The exact lower-level identity makes the ceiling index a countable-valued stopping time. -/
theorem ceil_index_le_iff (n k : ℕ) (t : ℝ≥0) :
    ceilIndex n t ≤ k ↔ t ≤ ceilTime n k := by
  unfold ceilIndex ceilTime
  rw [Nat.ceil_le,le_div_iff₀ (by positivity : (0 : ℝ≥0) < 2^n)]
  simp only [mul_comm]

theorem ceil_time_mono (n : ℕ) : Monotone (ceilTime n) := by
  intro k l hkl
  exact div_le_div_of_nonneg_right (by exact_mod_cast hkl) (by positivity)

theorem ceil_time_bounds (n : ℕ) (t : ℝ≥0) :
    t ≤ ceilTime n (ceilIndex n t) ∧ ceilTime n (ceilIndex n t) ≤ t+(2 : ℝ≥0)⁻¹^n := by
  constructor
  · exact (ceil_index_le_iff n _ t).mp le_rfl
  · unfold ceilTime ceilIndex
    have h := (Nat.ceil_lt_add_one (show (0 : ℝ≥0) ≤ 2^n*t from zero_le)).le
    apply (div_le_iff₀ (by positivity : (0 : ℝ≥0) < 2^n)).mpr
    calc
      _ ≤ (2 : ℝ≥0)^n*t+1 := h
      _ = (t+(2 : ℝ≥0)⁻¹^n)*2^n := by
        rw [add_mul,inv_pow,inv_mul_cancel₀ (by positivity)]
        rw [mul_comm]

theorem ceil_time_tendsto (t : ℝ≥0) :
    Tendsto (fun n => ceilTime n (ceilIndex n t)) atTop (𝓝 t) := by
  have hz : Tendsto (fun n : ℕ => (2 : ℝ≥0)⁻¹^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  have hu := (tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t)).add hz
  simp only [add_zero] at hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun n => (ceil_time_bounds n t).1) (fun n => (ceil_time_bounds n t).2)

/-- A finite NNReal stopping time becomes an integer-valued stopping time at each mesh. -/
theorem ceil_index_stopping {Ω : Type*} (F : ℝ≥0 → MeasurableSpace Ω)
    (τ : Ω → ℝ≥0) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t}) (n : ℕ) :
    ∀ k, MeasurableSet[F (ceilTime n k)] {ω | ceilIndex n (τ ω) ≤ k} := by
  intro k
  simpa only [ceil_index_le_iff] using hτ (ceilTime n k)

/-- A stopped event for τ remains a stopped event for the rounded index. -/
theorem ceil_stopped_event {Ω : Type*} (m : MeasurableSpace Ω)
    (F : ℝ≥0 → MeasurableSpace Ω) (τ : Ω → ℝ≥0)
    (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (A : Set Ω) (hA : MeasurableSet[Asakura.Chapter1Written.writtenStoppedSpace m F τ hτ] A) (n : ℕ) :
    MeasurableSet[Asakura.Chapter1Written.writtenStoppedSpace m (fun k => F (ceilTime n k))
      (fun ω => ceilIndex n (τ ω)) (ceil_index_stopping F τ hτ n)] A := by
  refine ⟨hA.1,?_⟩
  intro k
  simpa only [ceil_index_le_iff] using hA.2 (ceilTime n k)
end Asakura.FullAudit
