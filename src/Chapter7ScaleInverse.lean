import Mathlib.Analysis.Calculus.Deriv.Inv
import Chapter7ScaleDerivatives
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.MonotoneContinuity

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter7
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

theorem scale_inverse_derivatives
    (μ σ : ℝ → ℝ) (hμ : Continuous μ) (hσ : Continuous σ)
    (hσp : ∀ x,0 < σ x) (x0 : ℝ)
    (hsur : Function.Surjective (scaleFunction μ σ x0)) :
    ∃ g : ℝ → ℝ,Continuous g ∧
      (∀ y,scaleFunction μ σ x0 (g y) = y) ∧
      (∀ x,g (scaleFunction μ σ x0 x) = x) ∧
      (∀ y,HasDerivAt g (scaleDensity μ σ x0 (g y))⁻¹ y) ∧
      (∀ y,HasDerivAt (fun y => (scaleDensity μ σ x0 (g y))⁻¹)
        (2*μ (g y)/((σ (g y))^2*(scaleDensity μ σ x0 (g y))^2)) y) := by
  obtain ⟨hp,hs,hd,hmono,_⟩ := scale_derivatives μ σ hμ hσ hσp x0
  let e := hmono.orderIsoOfSurjective (scaleFunction μ σ x0) hsur
  let g : ℝ → ℝ := e.symm
  have hgc : Continuous g := e.symm.continuous
  have hsg y : scaleFunction μ σ x0 (g y) = y := e.apply_symm_apply y
  have hgs x : g (scaleFunction μ σ x0 x) = x := e.symm_apply_apply x
  have hg y : HasDerivAt g (scaleDensity μ σ x0 (g y))⁻¹ y :=
    HasDerivAt.of_local_left_inverse hgc.continuousAt (hs (g y)) (ne_of_gt (hp (g y)))
      (Eventually.of_forall hsg)
  refine ⟨g,hgc,hsg,hgs,hg,?_⟩
  intro y
  have h := ((hd (g y)).comp y (hg y)).inv (ne_of_gt (hp (g y)))
  convert h using 1
  · rfl
  · have hn := ne_of_gt (hp (g y))
    have hsn := ne_of_gt (hσp (g y))
    dsimp only [Function.comp_def]
    field_simp
    <;> ring

/-- The two chain-rule coefficients in the inverse scale transform are
exactly the original diffusion and drift. -/
theorem inverse_scale_coefficients
    (p s b : ℝ) (hp : p ≠ 0) (hs : s ≠ 0) :
    p⁻¹*(p*s) = s ∧ (2*b/(s^2*p^2))*(p*s)^2/2 = b := by
  constructor <;> field_simp <;> ring

end Asakura.Chapter7
