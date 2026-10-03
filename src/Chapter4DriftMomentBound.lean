import Chapter4DriftMaximalBound
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter4

/-- The stochastic drift estimate is obtained from the pathwise supremum
bound and Fubini, with square integrability derived rather than assumed. -/
theorem drift_path_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ) (hT : 0 ≤ T)
    (H : Ω × ℝ → ℝ) (hHm : Measurable H)
    (hH : MemLp H 2 (P.prod (volume.restrict (Ioc 0 T))))
    (D : Ω → C(Icc (0:ℝ) T,ℝ)) (hDm : AEStronglyMeasurable D P)
    (hD : ∀ᵐ ω ∂P, ∀ t, D ω t = ∫ r in 0..t.val, H (ω,r)) :
    MemLp D 2 P ∧ (∫ ω, ‖D ω‖^2 ∂P) ≤
      T * ∫ r in 0..T, (∫ ω, H (ω,r)^2 ∂P) := by
  let μ := volume.restrict (Ioc (0:ℝ) T)
  have hi : Integrable (fun z => H z^2) (P.prod μ) :=
    (memLp_two_iff_integrable_sq hH.aestronglyMeasurable).1 hH
  have hs : ∀ᵐ ω ∂P, MemLp (fun r => H (ω,r)) 2 μ := by
    filter_upwards [hi.prod_right_ae] with ω hω
    exact (memLp_two_iff_integrable_sq
      (hHm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).2 hω
  have hb : ∀ᵐ ω ∂P, ‖D ω‖^2 ≤ T * ∫ r, H (ω,r)^2 ∂μ := by
    filter_upwards [hs,hD] with ω hω hDω
    simpa only [intervalIntegral.integral_of_le hT,μ] using
      drift_path_square_bound T hT (fun r => H (ω,r)) hω (D ω) hDω
  have hdom : Integrable (fun ω => T * ∫ r, H (ω,r)^2 ∂μ) P :=
    hi.integral_prod_left.const_mul T
  have hnorm : Integrable (fun ω => ‖D ω‖^2) P := by
    apply hdom.mono' (hDm.norm.pow 2)
    filter_upwards [hb] with ω hω
    simpa only [Pi.pow_apply,Real.norm_eq_abs,abs_sq] using hω
  refine ⟨(memLp_two_iff_integrable_sq_norm hDm).2 hnorm,?_⟩
  calc
    _ ≤ ∫ ω, T * ∫ r, H (ω,r)^2 ∂μ ∂P := integral_mono_ae hnorm hdom hb
    _ = _ := by
      rw [integral_const_mul,integral_integral_swap hi,intervalIntegral.integral_of_le hT]

end Asakura.Chapter4
