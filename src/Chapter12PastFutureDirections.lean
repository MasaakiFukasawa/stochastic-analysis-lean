import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set Filter
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- Deterministic past and future directions are orthogonal in the actual
L2 time space; this includes the half-open endpoint convention. -/
theorem past_future_time_orthogonal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (μ : Measure ℝ) (a : ℝ)
    (u v : Lp H 2 μ)
    (hu : ∀ᵐ t ∂μ, a < t → u t = 0)
    (hv : ∀ᵐ t ∂μ, t ≤ a → v t = 0) : ⟪u,v⟫ = 0 := by
  rw [L2.inner_def]
  have hz : (fun t => inner ℝ (u t) (v t)) =ᵐ[μ] (fun _ => (0:ℝ)) := by
    filter_upwards [hu,hv] with t hut hvt
    by_cases ht : t ≤ a
    · rw [hvt ht,inner_zero_right]
    · rw [hut (lt_of_not_ge ht),inner_zero_left]
  rw [integral_congr_ae hz,integral_zero]

/-- Brownian coordinates at times s ≤ a have directions 1_[0,s] e_j,
whereas the increment test has direction 1_(a,b] e_i. -/
theorem past_coordinate_future_increment_orthogonal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (μ : Measure ℝ) [IsFiniteMeasure μ]
    (s a b : ℝ) (hsa : s ≤ a) (e f : H) :
    ⟪((memLp_const (μ := μ) (p := 2) e).indicator measurableSet_Icc).toLp ((Icc 0 s).indicator (fun _ : ℝ => e)),
      ((memLp_const (μ := μ) (p := 2) f).indicator measurableSet_Ioc).toLp ((Ioc a b).indicator (fun _ : ℝ => f))⟫ = 0 := by
  apply past_future_time_orthogonal μ a
  · filter_upwards [((memLp_const (μ := μ) (p := 2) e).indicator (s := Icc 0 s) measurableSet_Icc).coeFn_toLp] with t ht
    intro hat
    rw [ht]
    exact indicator_of_notMem (by intro h; exact (not_le.mpr (hsa.trans_lt hat)) h.2) _
  · filter_upwards [((memLp_const (μ := μ) (p := 2) f).indicator (s := Ioc a b) measurableSet_Ioc).coeFn_toLp] with t ht
    intro hta
    rw [ht]
    exact indicator_of_notMem (by intro h; exact (not_lt.mpr hta) h.1) _

end Asakura.Chapter12
