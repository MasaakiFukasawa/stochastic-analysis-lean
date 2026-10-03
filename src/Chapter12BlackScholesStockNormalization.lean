import Chapter12BlackScholesGreekNormalization

open Matrix Finset
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem bs_terminal_normalization {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (T : ℝ) (hT : 0<T) (w : Fin d → ℝ) (i : Fin d) :
    (∑ j,((Real.sqrt T) • A) i j*(w j/Real.sqrt T))=∑ j,A i j*w j := by
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.smul_apply,smul_eq_mul]
  field_simp

theorem bs_scaled_matrix_nonsingular {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.det≠0) (T : ℝ) (hT : 0<T) : ((Real.sqrt T) • A).det≠0 := by
  rw [Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (Real.sqrt_pos.mpr hT).ne') hA

theorem bs_vega_terminal_normalization {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.det≠0) (T s : ℝ) (hT : 0<T) (w d0 : Fin d → ℝ) (i : Fin d) :
    (∑ j,((Real.sqrt T) • A) i j*
      (s*(w j/Real.sqrt T)-s^2*(Real.sqrt T*(A⁻¹.mulVec d0) j)/2))=
      s*(∑ j,A i j*w j)-s^2*T*d0 i/2 := by
  have hsq := Real.sq_sqrt hT.le
  have hsn := (Real.sqrt_pos.mpr hT).ne'
  have hi (j : Fin d) : ((Real.sqrt T) • A) i j*
      (s*(w j/Real.sqrt T)-s^2*(Real.sqrt T*(A⁻¹.mulVec d0) j)/2)=
      s*(A i j*w j)-(s^2*T/2)*(A i j*(A⁻¹.mulVec d0) j) := by
    simp only [Matrix.smul_apply,smul_eq_mul]
    calc
      _=s*(A i j*w j)-(s^2*(Real.sqrt T)^2/2)*(A i j*(A⁻¹.mulVec d0) j) := by
        field_simp
        <;> ring
      _=_ := by rw [hsq]
  simp only [hi,Finset.sum_sub_distrib,← Finset.mul_sum]
  have hm := congrArg (fun z => z i) (Matrix.mulVec_mulVec d0 A A⁻¹)
  rw [Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA),Matrix.one_mulVec] at hm
  change (∑ j,A i j*(A⁻¹.mulVec d0) j)=d0 i at hm
  rw [hm]
  ring

end Asakura.Chapter12
