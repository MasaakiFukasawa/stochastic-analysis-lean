import Chapter4DeterministicItoEnergy
import Mathlib.Probability.Independence.Integration

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma independent_product_memLp_two {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G Z : Ω → ℝ) (hG : MemLp G 2 P) (hZ : MemLp Z 2 P) (hind : IndepFun G Z P) :
    MemLp (fun w => G w*Z w) 2 P ∧
    (∫ w,(G w*Z w)^2 ∂P)=(∫ w,G w^2 ∂P)*(∫ w,Z w^2 ∂P) := by
  have hiG := (memLp_two_iff_integrable_sq hG.aestronglyMeasurable).1 hG
  have hiZ := (memLp_two_iff_integrable_sq hZ.aestronglyMeasurable).1 hZ
  have hind2 := hind.comp (show Measurable (fun x : ℝ => x^2) by fun_prop)
    (show Measurable (fun x : ℝ => x^2) by fun_prop)
  have hip := hind2.integrable_mul hiG hiZ
  change Integrable (fun w => G w^2*Z w^2) P at hip
  have hp := hind2.integral_mul_eq_mul_integral hiG.aestronglyMeasurable hiZ.aestronglyMeasurable
  constructor
  · apply (memLp_two_iff_integrable_sq (hG.aestronglyMeasurable.mul hZ.aestronglyMeasurable)).2
    simpa only [mul_pow,Pi.mul_apply,Function.comp_def] using hip
  · simpa only [mul_pow,Pi.mul_apply,Function.comp_def] using hp

lemma gaussian_weighted_increment_energy {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G Z : Ω → ℝ) (hG : MemLp G 2 P) (v : ℝ≥0)
    (hZ : HasLaw Z (gaussianReal 0 v) P) (hind : IndepFun G Z P) :
    MemLp (fun w => G w*Z w) 2 P ∧
    (∫ w,(G w*Z w)^2 ∂P)=v*(∫ w,G w^2 ∂P) := by
  obtain ⟨hi,he⟩ := independent_product_memLp_two P G Z hG (hZ.memLp (memLp_id_gaussianReal 2)) hind
  refine ⟨hi,?_⟩
  rw [he,gaussian_law_square_integral P Z 0 v hZ]
  ring

end Asakura.Chapter4
