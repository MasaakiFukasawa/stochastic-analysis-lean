import Chapter12BrownianSquareInverseMoment
import Chapter12SquaredGaussianNoContinuousDensity

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- All distributional claims of the square-Brownian counterexample on
the original probability space, including impossibility of a continuous density. -/
theorem brownian_square_counterexample {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (T : ℝ≥0) (hT : 0<T) :
    HasLaw (fun w => (B T w)^2)
      (volume.withDensity (fun x => ENNReal.ofReal (squaredGaussianDensity T x))) P ∧
    (∀ᵐ w ∂P,0<4*(T:ℝ)*(B T w)^2) ∧
    (¬Integrable (fun w => (4*(T:ℝ)*(B T w)^2)⁻¹) P) ∧
    (∀ p : ℝ → ℝ,Continuous p → (∀ x,0≤p x) →
      P.map (fun w => (B T w)^2)≠volume.withDensity (fun x => ENNReal.ofReal (p x))) := by
  have hs : HasLaw (fun x : ℝ => x^2)
      (volume.withDensity (fun x => ENNReal.ofReal (squaredGaussianDensity T x))) (gaussianReal 0 T) := by
    have hh := hasLaw_map (P := gaussianReal 0 T) (show AEMeasurable (fun x : ℝ => x^2) _ by fun_prop)
    rw [squared_gaussian_law T hT.ne'] at hh
    exact hh
  have hl := hs.comp (hB.hasLaw_eval T)
  obtain ⟨hp,hi⟩ := brownian_square_covariance_inverse_failure P B hB T hT
  refine ⟨hl,hp,hi,?_⟩
  intro p hpc hp0 he
  have hh : (gaussianReal 0 T).map (fun x : ℝ => x^2)=
      volume.withDensity (fun x => ENNReal.ofReal (p x)) := by
    rw [squared_gaussian_law T hT.ne',←hl.map_eq]
    exact he
  exact squared_gaussian_no_continuous_density T hT p hpc hp0 hh

end Asakura.Chapter12
