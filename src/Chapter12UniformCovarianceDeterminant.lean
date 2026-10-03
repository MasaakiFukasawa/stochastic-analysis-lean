import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open Matrix MeasureTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem covariance_determinant_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (c : ℝ) (hc : 0≤c)
    (hb : ∀ v : ι → ℝ,c*(∑ i,(v i)^2)≤∑ i,v i*(A.mulVec v) i) :
    c^(Fintype.card ι)≤A.det := by
  have hev (j : ι) : c≤hA.eigenvalues j := by
    let v := hA.eigenvectorBasis j
    have hn : (∑ i,(v i)^2)=1 := by
      have hh := orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal j j
      rw [PiLp.inner_apply] at hh
      simpa only [v,Real.inner_apply,pow_two,if_true] using hh
    have hh := hb (fun i => v i)
    have he := hA.mulVec_eigenvectorBasis j
    change A.mulVec (fun i => v i)=hA.eigenvalues j • (fun i => v i) at he
    rw [he] at hh
    have hs : (∑ i,v i*((hA.eigenvalues j • (fun i => v i)) i))=
        hA.eigenvalues j*(∑ i,(v i)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      change v i*(hA.eigenvalues j*v i)=hA.eigenvalues j*(v i)^2
      ring
    rw [hs,hn,mul_one,mul_one] at hh
    exact hh
  rw [hA.det_eq_prod_eigenvalues]
  calc
    c^(Fintype.card ι) = ∏ _ : ι,c := by simp
    _≤∏ i,hA.eigenvalues i := Finset.prod_le_prod₀ (fun _ _ => hc) (fun i _ => hev i)

theorem covariance_inverse_determinant_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (c : ℝ) (hc : 0<c)
    (hb : ∀ v : ι → ℝ,c*(∑ i,(v i)^2)≤∑ i,v i*(A.mulVec v) i) :
    0<A.det ∧ A.det⁻¹≤(c^(Fintype.card ι))⁻¹ := by
  have hh := covariance_determinant_lower_bound A hA c hc.le hb
  have hp := pow_pos hc (Fintype.card ι)
  exact ⟨hp.trans_le hh,inv_anti₀ hp hh⟩

end Asakura.Chapter12
