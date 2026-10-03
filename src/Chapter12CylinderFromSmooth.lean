import Chapter12DerivativeGrowthAlgebra

open MeasureTheory
open scoped ContDiff
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- Build a cylinder directly from the manuscript's smoothness and
all-order polynomial growth assumptions. -/
noncomputable def smoothCylinderOfFunction {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : ℕ} (u : Fin n → H) (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f)
    (hg : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x,
      ‖iteratedFDeriv ℝ k f x‖ ≤ C*(1+‖x‖)^a) : SmoothCylinder H where
  dim := n
  direction := u
  f := f
  df := fderiv ℝ f
  smooth := hf
  derivative := fun x => (hf.differentiable (by simp)).differentiableAt.hasFDerivAt
  growth := by
    obtain ⟨C,hC,a,hb⟩ := hg 0
    refine ⟨C,hC,a,fun x => ?_⟩
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hb x
  derivative_measurable := fun j => by
    have hc : Continuous (fderiv ℝ f) := (hf.fderiv_right (m := ∞) (by simp)).continuous
    exact (hc.clm_apply continuous_const).measurable
  derivative_growth := fun j => by
    obtain ⟨C,hC,a,hb⟩ := hg 1
    refine ⟨C,hC,a,fun x => ?_⟩
    have hn : ‖(Pi.single j 1 : Fin n → ℝ)‖ ≤ 1 := by
      apply pi_norm_le_iff_of_nonneg zero_le_one |>.mpr
      intro i
      by_cases hi : i=j <;> simp [Pi.single,hi]
    calc
      |fderiv ℝ f x (Pi.single j 1)| ≤ ‖fderiv ℝ f x‖*‖(Pi.single j 1 : Fin n → ℝ)‖ :=
        (fderiv ℝ f x).le_opNorm _
      _ ≤ ‖fderiv ℝ f x‖ := mul_le_of_le_one_right (norm_nonneg _) hn
      _ ≤ C*(1+‖x‖)^a := by simpa only [norm_iteratedFDeriv_one] using hb x
  all_derivatives_growth := hg

end Asakura.Chapter12
