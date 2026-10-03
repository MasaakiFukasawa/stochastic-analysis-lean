import Chapter12BasketGreekDirections
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Field

open Matrix Finset
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem bs_scaled_inverse {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.det≠0) (t : ℝ) (ht : t≠0) : (t • A)⁻¹=t⁻¹ • A⁻¹ := by
  letI := invertibleOfNonzero ht
  simpa only [invOf_eq_inv] using Matrix.inv_smul A t (isUnit_iff_ne_zero.mpr hA)

theorem bs_delta_normalization {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.det≠0) (T : ℝ) (hT : 0<T) (w : Fin d → ℝ) (i : Fin d) :
    (∑ j,((Real.sqrt T) • A)⁻¹ j i*(w j/Real.sqrt T))=
      (∑ j,(A⁻¹) j i*w j)/T := by
  rw [bs_scaled_inverse A hA _ (Real.sqrt_pos.mpr hT).ne',Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.smul_apply,smul_eq_mul]
  have ht := Real.sq_sqrt hT.le
  have htn := (Real.sqrt_pos.mpr hT).ne'
  field_simp
  rw [ht]
  ring

theorem bs_gamma_normalization {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.det≠0) (T : ℝ) (hT : 0<T) (i j : Fin d) :
    (∑ k,((Real.sqrt T) • A)⁻¹ k i*((Real.sqrt T) • A)⁻¹ k j)=
      (∑ k,(A⁻¹) k i*(A⁻¹) k j)/T := by
  rw [bs_scaled_inverse A hA _ (Real.sqrt_pos.mpr hT).ne',Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.smul_apply,smul_eq_mul]
  have ht := Real.sq_sqrt hT.le
  have htn := (Real.sqrt_pos.mpr hT).ne'
  field_simp
  rw [ht]
  ring

theorem bs_vega_score_normalization {d : ℕ} (T s : ℝ) (hT : 0<T)
    (w k : Fin d → ℝ) :
    (((∑ i,(w i/Real.sqrt T)^2)-(d:ℝ))/s-
      (∑ i,(Real.sqrt T*k i)*(w i/Real.sqrt T)))=
      (((∑ i,(w i)^2)/T-(d:ℝ))/s-(∑ i,k i*w i)) := by
  have he (i : Fin d) : (w i/Real.sqrt T)^2=(w i)^2/T := by
    rw [div_pow,Real.sq_sqrt hT.le]
  have he' (i : Fin d) : (Real.sqrt T*k i)*(w i/Real.sqrt T)=k i*w i := by
    field_simp
  simp only [he,he',← Finset.sum_div]

end Asakura.Chapter12
