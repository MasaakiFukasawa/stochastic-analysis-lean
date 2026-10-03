import Chapter6WeightedStepIntegral
import Chapter6UniformStepL1
import Chapter6BoundedIntegrand

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

theorem uniform_weighted_riemann_L1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (R : ℝ) (hR : 0<R)
    (H β : Ω × ℝ → ℝ) (hHm : Measurable H) (hβm : Measurable β)
    (hHc : ∀ w,ContinuousOn (fun r => H (w,r)) (Icc 0 R))
    (K L : ℝ) (hK : 0≤K) (hL : 0≤L)
    (hHb : ∀ w r,r∈Icc 0 R → |H (w,r)|≤K) (hβb : ∀ z,|β z|≤L) :
    Tendsto (fun n => ∫ w,‖(∫ r in 0..R,H (w,r)*β (w,r))-
      ∑ k∈range (n+1),H (w,(k:ℝ)*(R/((n:ℝ)+1)))*
        (∫ r in (k:ℝ)*(R/((n:ℝ)+1))..((k:ℝ)+1)*(R/((n:ℝ)+1)),β (w,r))‖ ∂P) atTop (𝓝 0) := by
  let ν := volume.restrict (Ioc (0:ℝ) R)
  let S := fun n (z : Ω × ℝ) => uniformLeftStep R n (fun r => H (z.1,r)) z.2
  let D := fun n (z : Ω × ℝ) => H z-S n z
  obtain ⟨hDi,hlim⟩ := uniform_step_L1_error_limit P R hR H hHm hHc (fun _ => K) (integrable_const _) hHb
  have hFi n : Integrable (fun z => D n z*β z) (P.prod ν) := by
    simpa only [mul_comm] using (hDi n).bdd_mul hβm.aestronglyMeasurable (ae_of_all _ hβb)
  have hflim : Tendsto (fun n => ∫ z,‖D n z*β z‖ ∂P.prod ν) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg (fun _ => norm_nonneg _))
      (fun n => (integral_mono (hFi n).norm ((hDi n).norm.const_mul L) (fun z => by
        rw [norm_mul,Real.norm_eq_abs (β z)]
        exact (mul_le_mul_of_nonneg_left (hβb z) (norm_nonneg _)).trans_eq (mul_comm _ _))))
    simpa only [integral_const_mul,mul_zero] using hlim.const_mul L
  have hβi w := bounded_time_integrable _ (hβm.comp measurable_prodMk_left) L (fun r => hβb (w,r)) R hR.le
  have hiH w : Integrable (fun r => H (w,r)*β (w,r)) ν := by
    have hb' : ∀ᵐ r ∂ν,|H (w,r)|≤K := (ae_restrict_mem measurableSet_Ioc).mono (fun r hr => hHb w r ⟨hr.1.le,hr.2⟩)
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mp (hβi w)).bdd_mul
      (hHm.comp measurable_prodMk_left).aestronglyMeasurable hb'
  have hiS n w : Integrable (fun r => S n (w,r)*β (w,r)) ν := by
    have hb' : ∀ᵐ r ∂ν,|S n (w,r)|≤K := (ae_restrict_mem measurableSet_Ioc).mono (fun r hr => uniform_left_step_abs_le R hR n _ K (hHb w) r hr)
    have hm : Measurable (fun r => S n (w,r)) := by
      apply Finset.measurable_sum
      intro k _
      change Measurable ((Ioc ((k:ℝ)*(R/(n+1))) (((k:ℝ)+1)*(R/(n+1)))).indicator (fun _ : ℝ => H (w,(k:ℝ)*(R/(n+1)))))
      exact measurable_const.indicator measurableSet_Ioc
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mp (hβi w)).bdd_mul hm.aestronglyMeasurable hb'
  have he n w : (∫ r in 0..R,H (w,r)*β (w,r))-
      ∑ k∈range (n+1),H (w,(k:ℝ)*(R/((n:ℝ)+1)))*
        (∫ r in (k:ℝ)*(R/((n:ℝ)+1))..((k:ℝ)+1)*(R/((n:ℝ)+1)),β (w,r)) = ∫ r,D n (w,r)*β (w,r) ∂ν := by
    rw [intervalIntegral.integral_of_le hR.le,←uniform_weighted_step_integral R hR n (fun r => H (w,r)) (fun r => β (w,r)) (hβi w)]
    symm
    simpa only [D,sub_mul] using integral_sub (hiH w) (hiS n w)
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => norm_nonneg _)) (fun n => ?_) hflim
  simp_rw [he]
  rw [integral_prod _ (hFi n).norm]
  exact integral_mono (hFi n).integral_prod_left.norm (hFi n).norm.integral_prod_left
    (fun w => norm_integral_le_integral_norm _)

end Asakura.Chapter6
