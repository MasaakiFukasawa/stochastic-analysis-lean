import Chapter12ChainLimit
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory
open scoped ENNReal NNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

lemma lipschitz_sub_value {C : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith C f) :
    LipschitzWith C (fun x => f x-f 0) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_sub_right] using hf.dist_le_mul x y

noncomputable def lipschitzCompositionLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (p : ℝ≥0∞) {C : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith C f) (u : Lp ℝ p P) : Lp ℝ p P :=
  (lipschitz_sub_value hf).compLp (sub_self _) u+
    (memLp_const (μ := P) (p := p) (f 0)).toLp (fun _ => f 0)

theorem lipschitzCompositionLp_coe {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (p : ℝ≥0∞) {C : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith C f) (u : Lp ℝ p P) :
    (lipschitzCompositionLp P p hf u : Ω → ℝ) =ᵐ[P] fun w => f (u w) := by
  filter_upwards [Lp.coeFn_add ((lipschitz_sub_value hf).compLp (sub_self _) u)
    ((memLp_const (μ := P) (p := p) (f 0)).toLp (fun _ => f 0)),
    (lipschitz_sub_value hf).coeFn_compLp (sub_self _) u,
    (memLp_const (μ := P) (p := p) (f 0)).coeFn_toLp] with w h1 h2 h3
  dsimp only [lipschitzCompositionLp]
  rw [h1,Pi.add_apply,h2,h3]
  exact sub_add_cancel _ _

theorem lipschitzCompositionLp_continuous {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {C : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith C f) :
    Continuous (lipschitzCompositionLp P p hf) :=
  ((lipschitz_sub_value hf).continuous_compLp (sub_self _)).add continuous_const

theorem bounded_derivative_lipschitz (f df : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt f (df x) x) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |df x| ≤ C) :
    LipschitzWith ⟨C,hC⟩ f := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hd x).differentiableAt)
  intro x
  change ‖deriv f x‖ ≤ C
  rw [(hd x).deriv,Real.norm_eq_abs]
  exact hb x

end Asakura.Chapter12
