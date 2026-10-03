import Chapter12GaussianTranslationDerivative

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem finite_gaussian_translation_integrable {d : ℕ} (q : Fin d → ℝ) (t : ℝ)
    (f : (Fin d → ℝ) → ℝ) (hm : Measurable f)
    (hf : MemLp f 2 (Measure.pi (fun _ : Fin d => gaussianReal 0 1))) :
    Integrable (fun z => f (t • q+z)) (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  let μ := Measure.pi (fun _ : Fin d => gaussianReal 0 1)
  let v : ℝ≥0 := ⟨∑ i,(q i)^2,Finset.sum_nonneg (fun i _ => sq_nonneg _)⟩
  have he : MemLp (fun z => Real.exp (t*(∑ i,q i*z i)-t^2*v/2)) 2 μ := by
    have hh := (gaussian_exponential_memLp μ (fun z => ∑ i,q i*z i) 0 v
      (finite_gaussian_linear_score_law q) t 2 (by norm_num)).const_mul (Real.exp (-t^2*v/2))
    convert hh using 1
    funext z
    rw [← Real.exp_add]
    congr 1
    ring
  apply (integrable_map_measure hm.aestronglyMeasurable (by fun_prop)).mp
  rw [standard_gaussian_translation_density]
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  convert he.integrable_mul hf using 1
  funext z
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _),smul_eq_mul,Pi.mul_apply]
  rfl

end Asakura.Chapter12
