import Chapter6UniformStepLimit
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators ENNReal
namespace Asakura.Chapter6
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Dominated convergence for the actual left-step coefficient errors
in sample--time L2; no stochastic-integral limit is assumed. -/
theorem uniform_step_L1_error_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (R : ℝ) (hR : 0<R)
    (H : Ω × ℝ → ℝ) (hHm : Measurable H)
    (hHc : ∀ w,ContinuousOn (fun r => H (w,r)) (Icc 0 R))
    (K : Ω → ℝ) (hK : Integrable K P) (hbound : ∀ w r,r∈Icc 0 R → |H (w,r)|≤K w) :
    let D := fun n (z : Ω × ℝ) => H z-uniformLeftStep R n (fun r => H (z.1,r)) z.2
    (∀ n,Integrable (D n) (P.prod (volume.restrict (Ioc 0 R)))) ∧
    Tendsto (fun n => ∫ z,‖D n z‖ ∂P.prod (volume.restrict (Ioc 0 R))) atTop (𝓝 0) := by
  let ν := P.prod (volume.restrict (Ioc (0:ℝ) R))
  let S := fun n (z : Ω × ℝ) => uniformLeftStep R n (fun r => H (z.1,r)) z.2
  let D := fun n (z : Ω × ℝ) => H z-S n z
  have hSm n : Measurable (S n) := by
    apply Finset.measurable_sum
    intro k _
    have hm : Measurable (fun z : Ω × ℝ => H (z.1,(k:ℝ)*(R/(n+1)))) :=
      hHm.comp (measurable_fst.prodMk measurable_const)
    exact hm.indicator (measurableSet_Ioc.preimage measurable_snd)
  have hDm n : Measurable (D n) := hHm.sub (hSm n)
  have hgood : ∀ᵐ z ∂ν,z.2∈Ioc (0:ℝ) R := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_snd)).2
    exact .of_forall (fun _ => ae_restrict_mem measurableSet_Ioc)
  have hDb n : ∀ᵐ z ∂ν,‖D n z‖≤2*K z.1 := by
    filter_upwards [hgood] with z hz
    have hs := uniform_left_step_abs_le R hR n (fun r => H (z.1,r)) (K z.1) (hbound z.1) z.2 hz
    have hh := hbound z.1 z.2 ⟨hz.1.le,hz.2⟩
    exact (norm_sub_le _ _).trans (by simpa only [Real.norm_eq_abs] using add_le_add hh hs |>.trans (le_of_eq (by ring)))
  have hKp : Integrable (fun z : Ω × ℝ => 2*K z.1) ν :=
    (((memLp_one_iff_integrable.mpr hK).comp_fst (volume.restrict (Ioc (0:ℝ) R))).const_mul 2).integrable le_rfl
  have hi n : Integrable (D n) ν := hKp.mono' (hDm n).aestronglyMeasurable (hDb n)
  refine ⟨hi,?_⟩
  have hdom n : ∀ᵐ z ∂ν,‖‖D n z‖‖≤2*K z.1 := by simpa only [norm_norm] using hDb n
  have hlim : ∀ᵐ z ∂ν,Tendsto (fun n => ‖D n z‖) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [hgood] with z hz
    have ht := uniform_left_step_pointwise R hR (fun r => H (z.1,r)) (hHc z.1) z.2 hz
    simpa only [D,S,sub_self,norm_zero] using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => H z) atTop (𝓝 (H z))).sub ht).norm
  have ht := tendsto_integral_of_dominated_convergence (μ := ν) (fun z : Ω × ℝ => 2*K z.1)
    (fun n => (hDm n).norm.aestronglyMeasurable) hKp hdom hlim
  simpa only [integral_zero] using ht

end Asakura.Chapter6
