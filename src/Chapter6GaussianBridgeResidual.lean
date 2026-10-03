import Chapter6FiniteGaussianRegression
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

lemma integral_le_sqrt_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : MemLp X 2 P) :
    (∫ w,X w ∂P)≤Real.sqrt (∫ w,X w^2 ∂P) := by
  have hv := variance_nonneg X P
  rw [variance_eq_sub hX] at hv
  simp only [Pi.pow_apply] at hv
  have hh := Real.sqrt_le_sqrt (show (∫ w,X w ∂P)^2≤∫ w,X w^2 ∂P by linarith)
  rw [Real.sqrt_sq_eq_abs] at hh
  exact (le_abs_self _).trans hh

/-- Centering the intermediate point by s/t times the endpoint gives
an independent Gaussian residual and its exact second moments. -/
theorem gaussian_bridge_residual {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (U V : Ω → Fin d → ℝ) (hUV : HasGaussianLaw (fun w => (U w,V w)) P)
    (s t : ℝ) (ht : 0<t)
    (hU0 : ∀ i,(∫ w,U w i ∂P)=0) (hV0 : ∀ i,(∫ w,V w i ∂P)=0)
    (hUU : ∀ i j,cov[(fun w => U w i),(fun w => U w j);P]=if i=j then s else 0)
    (hVV : ∀ i j,cov[(fun w => V w i),(fun w => V w j);P]=if i=j then t else 0)
    (hUVc : ∀ i j,cov[(fun w => U w i),(fun w => V w j);P]=if i=j then s else 0) :
    let R := fun w i => U w i-(s/t)*V w i
    HasGaussianLaw R P ∧ IndepFun R V P ∧
      (∀ i,(∫ w,R w i ∂P)=0) ∧ (∀ i,(∫ w,R w i^2 ∂P)=s*(t-s)/t) := by
  let L : ((Fin d → ℝ) × (Fin d → ℝ)) →L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearMap.fst ℝ _ _-(s/t) • ContinuousLinearMap.snd ℝ _ _
  let R := fun w i => U w i-(s/t)*V w i
  have hR : HasGaussianLaw R P := hUV.map L
  have hRV : HasGaussianLaw (fun w => (R w,V w)) P :=
    hUV.map (L.prod (ContinuousLinearMap.snd ℝ _ _))
  have hcross i j : cov[(fun w => R w i),(fun w => V w j);P]=0 := by
    change cov[(fun w => U w i-(s/t)*V w i),(fun w => V w j);P]=0
    have he := covariance_sub_left (hUV.fst.eval i).memLp_two ((hUV.snd.eval i).memLp_two.const_mul (s/t)) (hUV.snd.eval j).memLp_two
    simp only [Pi.sub_def] at he
    rw [he,covariance_const_mul_left,hUVc,hVV]
    by_cases hij : i=j <;> simp [hij]
    field_simp [ht.ne']
    ring
  have hind := gaussian_independence_coordinates_written hRV hcross
  have hmean i : (∫ w,R w i ∂P)=0 := by
    change (∫ w,U w i-(s/t)*V w i ∂P)=0
    rw [integral_sub (hUV.fst.eval i).integrable ((hUV.snd.eval i).integrable.const_mul _),integral_const_mul,hU0,hV0]
    ring
  refine ⟨hR,hind,hmean,?_⟩
  intro i
  have hVu : Var[(fun w => U w i);P]=s := by simpa only [covariance_self (hUV.fst.eval i).aemeasurable,ite_true] using hUU i i
  have hVv : Var[(fun w => V w i);P]=t := by simpa only [covariance_self (hUV.snd.eval i).aemeasurable,ite_true] using hVV i i
  have hv := variance_sub (hUV.fst.eval i).memLp_two ((hUV.snd.eval i).memLp_two.const_mul (s/t))
  simp only [Pi.sub_def] at hv
  rw [variance_const_mul,covariance_const_mul_right,hVu,hVv,hUVc,if_pos rfl] at hv
  have hs : Var[(fun w => R w i);P]=s*(t-s)/t := by
    change Var[(fun w => U w i-(s/t)*V w i);P]=_
    rw [hv]
    field_simp [ht.ne']
    ring
  rw [variance_eq_sub (hR.eval i).memLp_two,hmean] at hs
  simpa only [Pi.pow_apply,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero] using hs

end Asakura.Chapter6
