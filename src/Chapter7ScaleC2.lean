import Chapter7ScaleInverse

open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Asakura.Chapter7
set_option maxHeartbeats 2200000

lemma c2_of_two_continuous_derivatives
    (f df ddf : ℝ → ℝ) (h1 : ∀ x,HasDerivAt f (df x) x)
    (h2 : ∀ x,HasDerivAt df (ddf x) x) (hc : Continuous ddf) :
    ContDiff ℝ 2 f := by
  have hd1 : deriv f = df := funext fun x => (h1 x).deriv
  have hd2 : deriv df = ddf := funext fun x => (h2 x).deriv
  have hdf : ContDiff ℝ 1 df := contDiff_one_iff_deriv.mpr
    ⟨fun x => (h2 x).differentiableAt,by rw [hd2]; exact hc⟩
  rw [show (2:ℕ∞ω) = 1+1 by norm_num,contDiff_succ_iff_deriv]
  exact ⟨fun x => (h1 x).differentiableAt,by norm_num,by rw [hd1]; exact hdf⟩

theorem scale_c2_and_inverse
    (μ σ : ℝ → ℝ) (hμ : Continuous μ) (hσ : Continuous σ)
    (hσp : ∀ x,0 < σ x) (x0 : ℝ)
    (hsur : Function.Surjective (scaleFunction μ σ x0)) :
    ContDiff ℝ 2 (scaleFunction μ σ x0) ∧
    ∃ g : ℝ → ℝ,ContDiff ℝ 2 g ∧
      (∀ y,scaleFunction μ σ x0 (g y) = y) ∧
      (∀ x,g (scaleFunction μ σ x0 x) = x) ∧
      (∀ y,deriv g y = (scaleDensity μ σ x0 (g y))⁻¹) ∧
      (∀ y,deriv (deriv g) y = 2*μ (g y)/((σ (g y))^2*(scaleDensity μ σ x0 (g y))^2)) ∧
      Continuous (fun y => scaleDensity μ σ x0 (g y)*σ (g y)) ∧
      (∀ y,0 < scaleDensity μ σ x0 (g y)*σ (g y)) := by
  obtain ⟨hp,hs,hd,_,_⟩ := scale_derivatives μ σ hμ hσ hσp x0
  have hdc : Continuous (scaleDensity μ σ x0) := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  constructor
  · apply c2_of_two_continuous_derivatives _ _ _ hs hd
    exact (((continuous_const.mul hμ).div (hσ.pow 2) (fun x => pow_ne_zero _ (ne_of_gt (hσp x)))).mul hdc)
  · obtain ⟨g,hgc,hsg,hgs,hg,hgd⟩ := scale_inverse_derivatives μ σ hμ hσ hσp x0 hsur
    have hgddc : Continuous (fun y => 2*μ (g y)/((σ (g y))^2*(scaleDensity μ σ x0 (g y))^2)) :=
      (continuous_const.mul (hμ.comp hgc)).div
        (((hσ.comp hgc).pow 2).mul ((hdc.comp hgc).pow 2))
        (fun y => mul_ne_zero (pow_ne_zero _ (ne_of_gt (hσp _))) (pow_ne_zero _ (ne_of_gt (hp _))))
    have hge : deriv g = fun y => (scaleDensity μ σ x0 (g y))⁻¹ := funext fun y => (hg y).deriv
    refine ⟨g,c2_of_two_continuous_derivatives _ _ _ hg hgd hgddc,hsg,hgs,
      fun y => (hg y).deriv,?_,(hdc.comp hgc).mul (hσ.comp hgc),fun y => mul_pos (hp _) (hσp _)⟩
    intro y
    rw [hge]
    exact (hgd y).deriv

end Asakura.Chapter7
