import Chapter8ScoreMatrixIdentity
import Chapter6LikelihoodQuadratic

open Matrix
open scoped BigOperators
namespace Asakura.Chapter8
open Asakura.Chapter6
set_option maxHeartbeats 1000000

/-- The displayed normalised estimation error follows from the actual
quadratic likelihood equation, with the time factors checked explicitly. -/
theorem rescaled_likelihood_error {p : ℕ} (I : Matrix (Fin p) (Fin p) ℝ)
    (hI : I.PosDef) (θ score noise : Fin p → ℝ) (hscore : score=I *ᵥ θ+noise)
    (T : ℝ) (hT : 0<T) :
    WithLp.toLp 2 (fun k => Real.sqrt T*((I⁻¹ *ᵥ score) k-θ k))=
      Matrix.toEuclideanCLM (𝕜 := ℝ) (T⁻¹ • I)⁻¹
        (WithLp.toLp 2 (fun k => noise k/Real.sqrt T)) := by
  have he : I⁻¹ *ᵥ score-θ=I⁻¹ *ᵥ noise := by
    rw [hscore]
    exact likelihood_estimator_error I hI θ noise
  letI : Invertible (T⁻¹) := invertibleOfNonzero (inv_ne_zero hT.ne')
  have hi : (T⁻¹ • I)⁻¹=T • I⁻¹ := by
    rw [Matrix.inv_smul I (T⁻¹) (isUnit_iff_ne_zero.mpr hI.det_pos.ne')]
    simp only [invOf_eq_inv,inv_inv]
  rw [hi]
  ext k
  have hk := congrFun he k
  change Real.sqrt T*((I⁻¹ *ᵥ score) k-θ k)=∑ j,(T*I⁻¹ k j)*(noise j/Real.sqrt T)
  change (I⁻¹ *ᵥ score) k-θ k=(I⁻¹ *ᵥ noise) k at hk
  rw [hk]
  change Real.sqrt T*(∑ j,I⁻¹ k j*noise j)=_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hs := Real.sq_sqrt hT.le
  have hn := (Real.sqrt_pos.mpr hT).ne'
  field_simp
  rw [hs]
  ring
end Asakura.Chapter8
