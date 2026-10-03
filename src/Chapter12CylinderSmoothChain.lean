import Chapter12CylinderFromSmooth
import Chapter12DerivativeGrowthComposition

open MeasureTheory
open scoped ContDiff
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

noncomputable def composeSmoothCylinder {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (c : SmoothCylinder H) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hgB : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x,
      ‖iteratedFDeriv ℝ k g x‖ ≤ C*(1+‖x‖)^a) : SmoothCylinder H :=
  smoothCylinderOfFunction c.direction (g ∘ c.f) (hg.comp c.smooth)
    (iterated_polynomial_growth_comp c.f g c.smooth hg c.all_derivatives_growth hgB)

theorem composeSmoothCylinder_value {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (c : SmoothCylinder H)
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hgB : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x,
      ‖iteratedFDeriv ℝ k g x‖ ≤ C*(1+‖x‖)^a) :
    (composeSmoothCylinder c g hg hgB).value P W = fun w => g (c.value P W w) := rfl

theorem composeSmoothCylinder_gradient {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (c : SmoothCylinder H)
    (g dg : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hd : ∀ x, HasDerivAt g (dg x) x)
    (hgB : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x,
      ‖iteratedFDeriv ℝ k g x‖ ≤ C*(1+‖x‖)^a) :
    (composeSmoothCylinder c g hg hgB).gradient P W = fun w => dg (c.value P W w) • c.gradient P W w := by
  have he (z : Fin c.dim → ℝ) : fderiv ℝ (g ∘ c.f) z = dg (c.f z) • c.df z :=
    ((hd (c.f z)).comp_hasFDerivAt z (c.derivative z)).fderiv
  funext w
  dsimp only [SmoothCylinder.gradient,SmoothCylinder.value,composeSmoothCylinder,smoothCylinderOfFunction]
  simp only [he,ContinuousLinearMap.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul]

end Asakura.Chapter12
