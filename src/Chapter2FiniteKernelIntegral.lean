import Chapter2FiniteKernelProduct
import Mathlib.Probability.Kernel.MeasurableIntegral

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- Measurability of integration against pointwise finite kernels, without
a deterministic bound on their masses. No atomlessness or path continuity
assumption is used. -/
theorem finite_kernel_integral_measurable
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (κ : Kernel Ω S) (hκ : ∀ ω, IsFiniteMeasure (κ ω))
    (H : Ω × S → ℝ) (hH : Measurable H) :
    Measurable (fun ω => ∫ r, H (ω,r) ∂κ ω) := by
  classical
  let B := fun n : ℕ => {ω | κ ω univ ≤ (n:ℝ≥0∞)}
  have hBm n : MeasurableSet (B n) := measurableSet_le (κ.measurable_coe MeasurableSet.univ) measurable_const
  let K := fun n => Kernel.piecewise (hBm n) κ 0
  have hKn n : IsFiniteKernel (K n) := by
    refine ⟨(n:ℝ≥0∞),by simp,?_⟩
    intro ω
    change (Kernel.piecewise (hBm n) κ 0) ω univ ≤ (n:ℝ≥0∞)
    rw [Kernel.piecewise_apply']
    by_cases hω : ω ∈ B n
    · rw [if_pos hω]
      exact hω
    · simp [if_neg hω]
  have hm n : Measurable (fun ω => ∫ r, H (ω,r) ∂K n ω) := by
    letI := hKn n
    exact hH.stronglyMeasurable.integral_kernel_prod_right'.measurable
  apply measurable_of_tendsto_metrizable hm
  apply tendsto_pi_nhds.mpr
  intro ω
  obtain ⟨n,hn⟩ := ENNReal.exists_nat_gt (hκ ω).measure_univ_lt_top.ne
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with j hj
  have hb : ω ∈ B j := hn.le.trans (by exact_mod_cast hj)
  have he : K j ω = κ ω := by
    change Kernel.piecewise (hBm j) κ 0 ω = κ ω
    rw [Kernel.piecewise_apply,if_pos hb]
  rw [he]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.finite_kernel_integral_measurable
