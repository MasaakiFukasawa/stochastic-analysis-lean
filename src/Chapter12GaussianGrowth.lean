import Chapter12DivergenceCommutation

open MeasureTheory ProbabilityTheory
namespace Asakura.Chapter12
open Asakura.FullAudit

 theorem polynomial_growth_sub {E : Type*} [SeminormedAddCommGroup E]
    {f g : E → ℝ} (hf : PolyGrowth f) (hg : PolyGrowth g) :
    PolyGrowth (fun z => f z-g z) := by
  simpa only [neg_one_mul,sub_eq_add_neg] using hf.add ((PolyGrowth.const (-1)).mul hg)

theorem gaussian_divergence_measurable {n : ℕ}
    (u : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (du : Fin (n+1) → Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (hu : ∀ j, Measurable (u j)) (hdu : ∀ i j, Measurable (du i j)) :
    Measurable (gaussianDivergence u du) := by
  exact Finset.measurable_sum _ fun j _ =>
    ((measurable_pi_apply j).mul (hu j)).sub (hdu j j)

theorem gaussian_divergence_growth {n : ℕ}
    (u : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (du : Fin (n+1) → Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (hu : ∀ j, PolyGrowth (u j)) (hdu : ∀ i j, PolyGrowth (du i j)) :
    PolyGrowth (gaussianDivergence u du) := by
  exact PolyGrowth.finset_sum _ _ fun j _ =>
    polynomial_growth_sub ((polynomial_growth_coordinate j).mul (hu j)) (hdu j j)

end Asakura.Chapter12
