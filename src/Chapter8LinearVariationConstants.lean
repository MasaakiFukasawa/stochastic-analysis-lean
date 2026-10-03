import Chapter8DampedSemigroup
import Chapter8CommonNoiseDifference

open MeasureTheory Set
namespace Asakura.Chapter8
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma operator_exp_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (s t : ℝ) :
    NormedSpace.exp (s • A)*NormedSpace.exp (t • A)=NormedSpace.exp ((s+t) • A) := by
  rw [add_smul]
  exact (NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) (((Commute.refl A).smul_left s).smul_right t)
    (by simp [NormedSpace.expSeries_radius_eq_top]) (by simp [NormedSpace.expSeries_radius_eq_top])).symm

/-- The integrating-factor step, including endpoint continuity, for the
continuous forcing left after the stochastic convolution is subtracted. -/
theorem linear_variation_constants {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (A : E →L[ℝ] E)
    (X f : ℝ → E) (T : ℝ) (hT : 0≤T) (hX : ContinuousOn X (Icc 0 T)) (hf : Continuous f)
    (hd : ∀ t∈Ioo 0 T,HasDerivAt X (A (X t)+f t) t) :
    X T=NormedSpace.exp (T • A) (X 0)+∫ s in 0..T,NormedSpace.exp ((T-s) • A) (f s) := by
  let E : ℝ → _ := fun t => NormedSpace.exp (t • A)
  have hEc : Continuous E := continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_exp_smul_const A t).continuousAt)
  have hEd t : HasDerivAt (fun s => E (-s)) (-(E (-t)*A)) t := by
    have hh := hasDerivAt_exp_smul_const (-A) t
    simpa only [E,smul_neg,neg_smul,mul_neg] using hh
  have hp t (ht : t∈Ioo 0 T) : HasDerivAt (fun s => E (-s) (X s)) (E (-t) (f t)) t := by
    have hh := (hEd t).clm_apply (hd t ht)
    convert hh using 1
    simp only [ContinuousLinearMap.neg_apply,ContinuousLinearMap.mul_apply,map_add]
    abel
  have hc : ContinuousOn (fun s => E (-s) (X s)) (Icc 0 T) :=
    (hEc.comp continuous_neg).continuousOn.clm_apply hX
  have hi : IntervalIntegrable (fun s => E (-s) (f s)) volume 0 T :=
    ((hEc.comp continuous_neg).clm_apply hf).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hc hp hi
  have hzero : E 0=1 := by simp [E]
  simp only [neg_zero,hzero,ContinuousLinearMap.one_apply] at he
  have hh := congrArg (E T) he
  rw [←(E T).intervalIntegral_comp_comm hi] at hh
  have hmul s x : E T (E (-s) x)=E (T-s) x := by
    change (E T*E (-s)) x=_
    rw [operator_exp_add]
    rfl
  simp only [map_sub,hmul,sub_self,hzero,ContinuousLinearMap.one_apply] at hh
  exact (sub_eq_iff_eq_add.mp hh.symm).trans (add_comm _ _)
end Asakura.Chapter8
