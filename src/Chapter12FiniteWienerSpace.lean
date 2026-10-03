import Chapter12VectorWienerExists
import Chapter12LpZeroExtension

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false

/-- Restrict the actual vector Wiener integral to the finite horizon by
extension by zero. The law has exactly the finite-horizon L2 variance. -/
theorem finite_horizon_wiener_exists {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1)) (T : ℝ) :
    ∃ W : PiLp 2 (fun _ : Fin (d+1) =>
        Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) →ₗᵢ[ℝ] Lp ℝ 2 P,
      ∀ f, HasLaw (W f : Ω → ℝ) (gaussianReal 0 ⟨‖f‖^2,sq_nonneg _⟩) P := by
  obtain ⟨I,hI,_⟩ := vector_actual_wiener_isometry_exists P B
  let J := finitePiIsometry (ι := Fin (d+1))
    (L2ZeroExtension (E := ℝ) (volume.restrict (Ioi (0:ℝ))) (Iic T) measurableSet_Iic)
  refine ⟨I.comp J,fun f => ?_⟩
  change HasLaw (I (J f) : Ω → ℝ) _ P
  have h := hI (J f)
  simpa only [J.norm_map] using h

end Asakura.Chapter12
