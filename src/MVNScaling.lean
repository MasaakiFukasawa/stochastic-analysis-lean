import MVNFutureKernel

open MeasureTheory Set
namespace Asakura

lemma mvn_past_kernel_scale (a t s : ℝ) (ht : 0 < t) (hs : 0 ≤ s) :
    mvnPastKernel a t (t*s) = t^a * mvnPastKernel a 1 s := by
  unfold mvnPastKernel
  rw [show t+t*s = t*(1+s) by ring, Real.mul_rpow ht.le (by linarith),Real.mul_rpow ht.le hs]
  ring

noncomputable def mvnPastVariance (H t : ℝ) : ℝ :=
  ∫ s in Ioi 0, (mvnPastKernel (H-1/2) t s)^2

lemma mvn_past_variance_scale (H t : ℝ) (hH : 0 < H) (ht : 0 ≤ t) :
    mvnPastVariance H t = t^(2*H) * mvnPastVariance H 1 := by
  by_cases ht0 : t = 0
  · subst t
    simp [mvnPastVariance,mvnPastKernel,Real.zero_rpow (by positivity : 2*H ≠ 0)]
  have ht' : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hchange := integral_comp_mul_left_Ioi' (fun s => (mvnPastKernel (H-1/2) t s)^2) 0 ht'
  simp only [mul_zero,smul_eq_mul] at hchange
  unfold mvnPastVariance
  rw [← hchange]
  have hi : (∫ s in Ioi 0, (mvnPastKernel (H-1/2) t (t*s))^2) =
      t^(2*H-1) * ∫ s in Ioi 0, (mvnPastKernel (H-1/2) 1 s)^2 := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    change (mvnPastKernel (H-1/2) t (t*s))^2 = _
    rw [mvn_past_kernel_scale _ _ _ ht' hs.le,mul_pow]
    have he : (t^(H-1/2))^2 = t^(2*H-1) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul ht]
      congr 1; ring
    rw [he]
  rw [hi,← mul_assoc]
  have he : t*t^(2*H-1) = t^(2*H) := by
    calc
      _ = t^(1:ℝ)*t^(2*H-1) := by rw [Real.rpow_one]
      _ = t^(1+(2*H-1)) := (Real.rpow_add ht' _ _).symm
      _ = _ := by congr 1; ring
  rw [he]

noncomputable def mvnVarianceConstant (H : ℝ) : ℝ := 1/(2*H)+mvnPastVariance H 1
noncomputable def mvnNormalization (H : ℝ) : ℝ := (Real.sqrt (mvnVarianceConstant H))⁻¹

lemma mvn_variance_constant_positive (H : ℝ) (hH : 0 < H) : 0 < mvnVarianceConstant H := by
  have hi : 0 ≤ mvnPastVariance H 1 := integral_nonneg (fun s => sq_nonneg _)
  unfold mvnVarianceConstant
  exact add_pos_of_pos_of_nonneg (by positivity) hi

lemma mvn_normalization_positive (H : ℝ) (hH : 0 < H) : 0 < mvnNormalization H :=
  inv_pos.mpr (Real.sqrt_pos.mpr (mvn_variance_constant_positive H hH))

lemma mvn_normalized_variance (H t : ℝ) (hH : 0 < H) (ht : 0 ≤ t) :
    mvnNormalization H ^ 2 *
      ((∫ s in Ioc 0 t, ((t-s)^(H-1/2))^2) + mvnPastVariance H t) = t^(2*H) := by
  rw [mvn_future_variance H t hH ht,mvn_past_variance_scale H t hH ht]
  have hJ := mvn_variance_constant_positive H hH
  have hs : (Real.sqrt (mvnVarianceConstant H))^2 = mvnVarianceConstant H := Real.sq_sqrt hJ.le
  unfold mvnNormalization
  rw [inv_pow,hs]
  have he : t^(2*H)/(2*H)+t^(2*H)*mvnPastVariance H 1 = t^(2*H)*mvnVarianceConstant H := by
    unfold mvnVarianceConstant
    ring
  rw [he]
  field_simp
end Asakura
