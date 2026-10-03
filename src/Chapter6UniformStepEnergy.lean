import Chapter6UniformStepLimit
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators ENNReal
namespace Asakura.Chapter6
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Dominated convergence for the actual left-step coefficient errors
in sample--time L2; no stochastic-integral limit is assumed. -/
theorem uniform_step_energy_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (R : ℝ) (hR : 0<R)
    (H : Ω × ℝ → ℝ) (hHm : Measurable H)
    (hHc : ∀ w,ContinuousOn (fun r => H (w,r)) (Icc 0 R))
    (K : ℝ) (hK : 0≤K) (hbound : ∀ w r,r∈Icc 0 R → |H (w,r)|≤K) :
    let D := fun n (z : Ω × ℝ) => H z-uniformLeftStep R n (fun r => H (z.1,r)) z.2
    (∀ n,MemLp (D n) 2 (P.prod (volume.restrict (Ioc 0 R)))) ∧
    Tendsto (fun n => ∫ z,(D n z)^2 ∂P.prod (volume.restrict (Ioc 0 R))) atTop (𝓝 0) := by
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
  have hDb n : ∀ᵐ z ∂ν,‖D n z‖≤2*K := by
    filter_upwards [hgood] with z hz
    have hs := uniform_left_step_abs_le R hR n (fun r => H (z.1,r)) K (hbound z.1) z.2 hz
    have hh := hbound z.1 z.2 ⟨hz.1.le,hz.2⟩
    exact (norm_sub_le _ _).trans (by simpa only [Real.norm_eq_abs] using add_le_add hh hs |>.trans (le_of_eq (by ring)))
  have hi n : MemLp (D n) 2 ν := MemLp.of_bound (hDm n).aestronglyMeasurable (2*K) (hDb n)
  refine ⟨hi,?_⟩
  have hdom n : ∀ᵐ z ∂ν,‖D n z^2‖≤(2*K)^2 := by
    filter_upwards [hDb n] with z hz
    rw [Real.norm_eq_abs,abs_sq]
    simp only [Real.norm_eq_abs] at hz
    nlinarith [le_abs_self (D n z),neg_le_abs (D n z)]
  have hlim : ∀ᵐ z ∂ν,Tendsto (fun n => D n z^2) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [hgood] with z hz
    have ht := uniform_left_step_pointwise R hR (fun r => H (z.1,r)) (hHc z.1) z.2 hz
    simpa only [D,S,sub_self,zero_pow (by decide : (2:ℕ)≠0)] using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => H z) atTop (𝓝 (H z))).sub ht).pow 2
  have ht := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ => (2*K)^2)
    (fun n => (hDm n).pow_const 2 |>.aestronglyMeasurable) (integrable_const _) hdom hlim
  simpa only [integral_zero] using ht

end Asakura.Chapter6
