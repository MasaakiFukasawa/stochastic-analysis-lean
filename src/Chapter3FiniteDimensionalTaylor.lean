import Chapter3CompactTaylor
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set Filter
open scoped Topology BigOperators
namespace Asakura.Chapter3Complete
set_option maxHeartbeats 1400000

/-- Coordinate expansion of the first differential. -/
theorem differential_coordinate_sum {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] ℝ) (v : Fin d → ℝ) :
    L v = ∑ i, v i * L (Pi.single i 1) := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp only [map_sum,map_smul,smul_eq_mul]

/-- Coordinate expansion of the second differential. -/
theorem hessian_coordinate_sum {d : ℕ}
    (B : (Fin d → ℝ) →L[ℝ] ((Fin d → ℝ) →L[ℝ] ℝ)) (v : Fin d → ℝ) :
    B v v = ∑ i, ∑ j, v i*v j*B (Pi.single i 1) (Pi.single j 1) := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp only [map_sum,map_smul,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- With the finite-product norm, its square is at most the sum of
coordinate squares. Thus the manuscript's quadratic sums control the
Taylor remainder without changing the underlying stochastic integrals. -/
theorem pi_norm_sq_le_sum_sq {d : ℕ} (v : Fin d → ℝ) :
    ‖v‖^2 ≤ ∑ i, (v i)^2 := by
  have hs : 0 ≤ ∑ i, (v i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn : ‖v‖ ≤ Real.sqrt (∑ i, (v i)^2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    have hi : (v i)^2 ≤ ∑ j, (v j)^2 :=
      Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    rw [Real.norm_eq_abs]
    nlinarith [Real.sq_sqrt hs,sq_abs (v i),abs_nonneg (v i),Real.sqrt_nonneg (∑ j, (v j)^2)]
  nlinarith [norm_nonneg v,Real.sqrt_nonneg (∑ j, (v j)^2),Real.sq_sqrt hs]

/-- A compact-ball uniform Taylor estimate written in the exact coordinate
sums of the multidimensional Ito formula. -/
theorem finite_dimensional_uniform_taylor {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) (R : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ Metric.closedBall 0 R, ∀ y ∈ Metric.closedBall 0 R,
      ‖y-x‖ ≤ δ →
      |f y-f x-(∑ i, (y i-x i)*fderiv ℝ f x (Pi.single i 1))-
        (∑ i, ∑ j, (y i-x i)*(y j-x j)*
          fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1))/2|
      ≤ (ε/2)*∑ i, (y i-x i)^2 := by
  obtain ⟨δ,hδ,hh⟩ := compact_uniform_taylor hf (isCompact_closedBall (0 : Fin d → ℝ) R)
    (convex_closedBall (0 : Fin d → ℝ) R) ε hε
  refine ⟨δ,hδ,?_⟩
  intro x hx y hy hxy
  have h := hh x hx (y-x) (by simpa using hy) hxy
  rw [differential_coordinate_sum,hessian_coordinate_sum] at h
  simp only [add_sub_cancel,Pi.sub_apply] at h
  have hn := pi_norm_sq_le_sum_sq (y-x)
  have he : ε*‖y-x‖^2/2 ≤ (ε/2)*∑ i, (y i-x i)^2 := by
    dsimp only [Pi.sub_apply] at hn
    nlinarith
  exact h.trans he

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.differential_coordinate_sum
#print axioms Asakura.Chapter3Complete.hessian_coordinate_sum
#print axioms Asakura.Chapter3Complete.pi_norm_sq_le_sum_sq
#print axioms Asakura.Chapter3Complete.finite_dimensional_uniform_taylor
