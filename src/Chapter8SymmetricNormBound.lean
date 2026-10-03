import Chapter8NewtonSpectral
import Mathlib.Analysis.Calculus.MeanValue

open scoped BigOperators RealInnerProductSpace NNReal
namespace Asakura.Chapter8

/-- The Hessian quadratic-form upper bound gives the operator norm bound
needed by the construction of the actual integral equation. -/
theorem symmetric_norm_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric) (u : ℝ) (hu : 0≤u)
    (hb : ∀ z,0≤⟪z,H z⟫ ∧ ⟪z,H z⟫≤u*‖z‖^2) : ‖H‖≤u := by
  let B := hH.eigenvectorBasis rfl
  let ev := hH.eigenvalues rfl
  have he i : H (B i)=ev i • B i := hH.apply_eigenvectorBasis rfl i
  have hn i : ‖B i‖=1 := B.orthonormal.norm_eq_one i
  have hi i : ⟪B i,H (B i)⟫=ev i := by
    rw [he,inner_smul_right,real_inner_self_eq_norm_sq,hn]; ring
  have hev i : 0≤ev i ∧ ev i≤u := by simpa [hi,hn] using hb (B i)
  apply ContinuousLinearMap.opNorm_le_bound _ hu
  intro z
  have hc i : ⟪B i,H z⟫=ev i*⟪B i,z⟫ := by
    calc
      _ = ⟪H (B i),z⟫ := (hH (B i) z).symm
      _ = _ := by rw [he,real_inner_smul_left]
  have hs : ‖H z‖^2≤u^2*‖z‖^2 := by
    rw [←B.sum_sq_inner_right (H z),←B.sum_sq_inner_right z,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [hc,mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hev i).1 (hev i).2 2) (sq_nonneg _)
  nlinarith [norm_nonneg (H z),norm_nonneg z,mul_nonneg hu (norm_nonneg z)]

theorem hessian_bounds_lipschitz {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (g : E → E) (H : E → E →L[ℝ] E) (u : ℝ≥0)
    (hd : ∀ x,HasFDerivAt g (H x) x)
    (hs : ∀ x,(H x).toLinearMap.IsSymmetric)
    (hb : ∀ x z,0≤⟪z,H x z⟫ ∧ ⟪z,H x z⟫≤(u:ℝ)*‖z‖^2) :
    LipschitzWith u g := by
  apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (hd x).differentiableAt)
  intro x
  rw [(hd x).fderiv]
  exact_mod_cast symmetric_norm_bound (H x) (hs x) u u.coe_nonneg (hb x)

end Asakura.Chapter8
