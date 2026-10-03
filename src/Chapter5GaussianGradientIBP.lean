import Chapter5GaussianDirections

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 2400000

/-- Apply coordinate Gaussian integration by parts to a component of the
spatial gradient; this is the missing trace term in the multi-dimensional
heat equation. -/
theorem gaussian_gradient_coordinate_ibp
    (n : ℕ) (i : Fin (n+1))
    (D : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (DD : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) →L[ℝ] (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt D (DD x) x) (hDc : Continuous D) (hDDc : Continuous DD)
    (C K : ℝ) (hD : ∀ x,‖D x‖ ≤ C) (hDD : ∀ x,‖DD x‖ ≤ K)
    (x : Fin (n+1) → ℝ) (t : ℝ) :
    (∫ z,z i*(D (x+Real.sqrt t • z) (Pi.single i 1)) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) =
      Real.sqrt t*(∫ z,DD (x+Real.sqrt t • z) (Pi.single i 1) (Pi.single i 1)
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) := by
  let e : Fin (n+1) → ℝ := Pi.single i 1
  have he : ‖e‖ = 1 := by simp [e,Pi.norm_single]
  have hb y : ‖D y e‖ ≤ C := by
    calc
      _ ≤ ‖D y‖*‖e‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ C := by simpa only [he,mul_one] using hD y
  have hbb y : ‖DD y e e‖ ≤ K := by
    calc
      _ ≤ ‖DD y e‖*‖e‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖DD y‖*‖e‖)*‖e‖ := mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ K := by simpa only [he,mul_one] using hDD y
  have hq : Measurable (fun z => D (x+Real.sqrt t • z) e) :=
    ((hDc.comp (by fun_prop)).clm_apply continuous_const).measurable
  have hqd : Measurable (fun z => Real.sqrt t*(DD (x+Real.sqrt t • z) e e)) :=
    ((((hDDc.comp (by fun_prop)).clm_apply continuous_const).clm_apply continuous_const).const_mul _).measurable
  have hder (v : Fin n → ℝ) (y : ℝ) :
      HasDerivAt (fun u => D (x+Real.sqrt t • i.insertNth u v) e)
        (Real.sqrt t*(DD (x+Real.sqrt t • i.insertNth y v) e e)) y := by
    have hh := ((hd _).comp_hasDerivAt y
      (((insertNth_hasDerivAt n i v y).const_smul (Real.sqrt t)).const_add x)).clm_apply (hasDerivAt_const y e)
    convert hh using 1 <;> simp [e,map_smul,smul_eq_mul]
  have hh := gaussian_product_coordinate_ibp n i _ _ hq hqd C (Real.sqrt t*K)
    (fun z => hb _) (fun z => by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg t)]
      exact mul_le_mul_of_nonneg_left (hbb _) (Real.sqrt_nonneg t)) hder
  rw [integral_const_mul] at hh
  exact hh.symm

end Asakura.Chapter5
