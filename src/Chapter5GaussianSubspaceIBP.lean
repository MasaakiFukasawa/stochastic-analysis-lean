import Chapter5GaussianGradientIBP

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Gaussian integration by parts when noise acts only in a linear
subspace; the other coordinates are the frozen past observations. -/
theorem gaussian_subspace_coordinate_ibp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (i : Fin (n+1)) (Q : (Fin (n+1) → ℝ) →L[ℝ] E)
    (D : E → E →L[ℝ] ℝ) (DD : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt D (DD x) x) (hDc : Continuous D) (hDDc : Continuous DD)
    (C K : ℝ) (hD : ∀ x,‖D x‖ ≤ C) (hDD : ∀ x,‖DD x‖ ≤ K)
    (x : E) (t : ℝ) :
    (∫ z,z i*D (x+Real.sqrt t • Q z) (Q (Pi.single i 1)) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) =
      Real.sqrt t*(∫ z,DD (x+Real.sqrt t • Q z) (Q (Pi.single i 1)) (Q (Pi.single i 1))
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) := by
  let e : Fin (n+1) → ℝ := Pi.single i 1
  have he : ‖e‖ = 1 := by simp [e,Pi.norm_single]
  have hQe : ‖Q e‖ ≤ ‖Q‖ := by simpa only [he,mul_one] using Q.le_opNorm e
  have hC : 0 ≤ C := (norm_nonneg (D x)).trans (hD x)
  have hK : 0 ≤ K := (norm_nonneg (DD x)).trans (hDD x)
  have hb y : ‖D y (Q e)‖ ≤ C*‖Q‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hD y) hQe (norm_nonneg _) hC)
  have hbb y : ‖DD y (Q e) (Q e)‖ ≤ K*‖Q‖^2 := by
    calc
      _ ≤ ‖DD y (Q e)‖*‖Q e‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖DD y‖*‖Q e‖)*‖Q e‖ := mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (K*‖Q‖)*‖Q‖ := mul_le_mul
        (mul_le_mul (hDD y) hQe (norm_nonneg _) hK) hQe (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hq : Measurable (fun z => D (x+Real.sqrt t • Q z) (Q e)) :=
    ((hDc.comp (by fun_prop)).clm_apply continuous_const).measurable
  have hqd : Measurable (fun z => Real.sqrt t*(DD (x+Real.sqrt t • Q z) (Q e) (Q e))) :=
    ((((hDDc.comp (by fun_prop)).clm_apply continuous_const).clm_apply continuous_const).const_mul _).measurable
  have hder (v : Fin n → ℝ) (y : ℝ) :
      HasDerivAt (fun u => D (x+Real.sqrt t • Q (i.insertNth u v)) (Q e))
        (Real.sqrt t*(DD (x+Real.sqrt t • Q (i.insertNth y v)) (Q e) (Q e))) y := by
    have hqD := Q.hasFDerivAt.comp_hasDerivAt y (insertNth_hasDerivAt n i v y)
    have hh := ((hd _).comp_hasDerivAt y
      ((hqD.const_smul (Real.sqrt t)).const_add x)).clm_apply (hasDerivAt_const y (Q e))
    convert hh using 1 <;> simp [Function.comp_def,e,map_smul,smul_eq_mul]
  have hh := gaussian_product_coordinate_ibp n i _ _ hq hqd (C*‖Q‖) (Real.sqrt t*(K*‖Q‖^2))
    (fun z => hb _) (fun z => by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg t)]
      exact mul_le_mul_of_nonneg_left (hbb _) (Real.sqrt_nonneg t)) hder
  rw [integral_const_mul] at hh
  exact hh.symm

end Asakura.Chapter5
