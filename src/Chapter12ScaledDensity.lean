import Chapter12RealMixtureDensity
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem scaled_density {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [ν.IsAddHaarMeasure]
    (g : E → ℝ≥0∞) (hg : Measurable g) (r : ℝ) (hr : r≠0) :
    (ν.withDensity g).map (fun x => r • x)=
      ν.withDensity (fun x => ENNReal.ofReal |(r^Module.finrank ℝ E)⁻¹| *g (r⁻¹ • x)) := by
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_map hφ (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul ν hg (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul ν (by fun_prop) hφ]
  let f : E → ℝ≥0∞ := fun x => g (r⁻¹ • x)*φ x
  have hf : Measurable f := by dsimp [f]; fun_prop
  have he := lintegral_map hf (show Measurable (fun x : E => r • x) by fun_prop) (μ := ν)
  rw [Measure.map_addHaar_smul ν hr,lintegral_smul_measure] at he
  have ht : (fun x => f (r • x))=(fun x => g x*φ (r • x)) := by
    funext x
    simp [f,smul_smul,hr]
  rw [ht] at he
  simp only [Pi.mul_apply]
  rw [← he]
  change ENNReal.ofReal |(r^Module.finrank ℝ E)⁻¹| * (∫⁻ x,f x ∂ν)=_
  rw [← lintegral_const_mul _ hf]
  apply lintegral_congr
  intro x
  dsimp [f]
  exact (mul_assoc _ _ _).symm

end Asakura.Chapter12
