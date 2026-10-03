import Chapter6UniformStepL1
import Chapter6UniformStepIntegral

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- Ordinary time integrals of continuous random functions are L1 limits
of the actual uniform left-endpoint Riemann sums. -/
theorem uniform_riemann_L1_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (R : ℝ) (hR : 0<R)
    (H : Ω × ℝ → ℝ) (hHm : Measurable H)
    (hHc : ∀ w,ContinuousOn (fun r => H (w,r)) (Icc 0 R))
    (K : Ω → ℝ) (hK : Integrable K P) (hbound : ∀ w r,r∈Icc 0 R → |H (w,r)|≤K w) :
    Tendsto (fun n => ∫ w,‖(∫ r in 0..R,H (w,r))-
      ∑ k∈range (n+1),(R/((n:ℝ)+1))*H (w,(k:ℝ)*(R/((n:ℝ)+1)))‖ ∂P) atTop (𝓝 0) := by
  let ν := volume.restrict (Ioc (0:ℝ) R)
  let S := fun n (z : Ω × ℝ) => uniformLeftStep R n (fun r => H (z.1,r)) z.2
  let D := fun n (z : Ω × ℝ) => H z-S n z
  obtain ⟨hDi,hlim⟩ := uniform_step_L1_error_limit P R hR H hHm hHc K hK hbound
  have hiH w : Integrable (fun r => H (w,r)) ν :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mp ((hHc w).intervalIntegrable_of_Icc hR.le)
  have he n w : (∫ r in 0..R,H (w,r))-
      ∑ k∈range (n+1),(R/((n:ℝ)+1))*H (w,(k:ℝ)*(R/((n:ℝ)+1))) = ∫ r,D n (w,r) ∂ν := by
    rw [intervalIntegral.integral_of_le hR.le,←uniform_left_step_integral R hR n (fun r => H (w,r))]
    symm
    apply integral_sub (hiH w)
    apply integrable_finsetSum
    intro k _
    change Integrable ((Ioc ((k:ℝ)*(R/(n+1))) (((k:ℝ)+1)*(R/(n+1)))).indicator (fun _ => H (w,(k:ℝ)*(R/(n+1))))) ν
    exact (integrable_const _).indicator measurableSet_Ioc
  have hb n : (∫ w,‖(∫ r in 0..R,H (w,r))-
      ∑ k∈range (n+1),(R/((n:ℝ)+1))*H (w,(k:ℝ)*(R/((n:ℝ)+1)))‖ ∂P)≤∫ z,‖D n z‖ ∂P.prod ν := by
    simp_rw [he]
    rw [integral_prod _ (hDi n).norm]
    exact integral_mono ((hDi n).integral_prod_left.norm) ((hDi n).norm.integral_prod_left)
      (fun w => norm_integral_le_integral_norm _)
  exact squeeze_zero (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hb hlim

end Asakura.Chapter6
