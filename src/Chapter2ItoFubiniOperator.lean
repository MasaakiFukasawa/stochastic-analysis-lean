import Chapter2ItoParameterIntegrability
import Chapter2ProgressiveEnergyComplete
import Chapter2L2FubiniMinkowski
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Stochastic Fubini on the concrete progressive-energy and M2 spaces.
The right-hand integrand is identified with the ordinary pointwise parameter
integral, and the equality is an equality in the actual M2 space. -/
theorem ito_fubini_for_actual_operator
    {Ω E : Type*} {m : MeasurableSpace Ω} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (c : ℕ → ℝ) (μ : Measure E) [SigmaFinite μ]
    (ν : Measure (Ω × ℝ)) [SigmaFinite ν]
    (L : progressiveEnergyRange F c ν →ₗᵢ[ℝ] continuousM2Terminal P F)
    (H : E × (Ω × ℝ) → ℝ) (hH : Measurable H)
    (hp : ∀ x n, @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H (x,(z.1,z.2.val))))
    (hN : (∫⁻ x, eLpNorm (fun z => H (x,z)) 2 ν ∂μ) < ∞) :
    ∃ U : E → progressiveEnergyRange F c ν,
      (∀ x, (U x : Lp ℝ 2 ν) = l2Section ν H x) ∧
      Integrable U μ ∧ Integrable (fun x => L (U x)) μ ∧
      ∃ g : progressiveEnergyRange F c ν,
        ((g : Lp ℝ 2 ν) : Ω × ℝ → ℝ) =ᵐ[ν] (fun z => ∫ x, H (x,z) ∂μ) ∧
        (∫ x, L (U x) ∂μ) = L g := by
  letI : CompleteSpace (progressiveEnergyRange F c ν) := progressive_energy_complete F c ν
  letI : CompleteSpace (continuousM2Terminal P F) := continuous_m2_hilbert_complete P F hF hle hnull
  obtain ⟨U,hU,hm,hi,hLI,hn⟩ := ito_parameter_family_integrable P F c μ ν L H hH hp hN
  have hpoint := (mixed_l1_l2_fubini_minkowski μ ν H hH hN).2.1
  let g : progressiveEnergyRange F c ν := ∫ x, U x ∂μ
  have hsub := (progressiveEnergyRange F c ν).subtypeL.integral_comp_comm hi
  change (∫ x, (U x : Lp ℝ 2 ν) ∂μ) = (g : Lp ℝ 2 ν) at hsub
  have he : (g : Lp ℝ 2 ν) = ∫ x, l2Section ν H x ∂μ := by
    rw [← hsub]
    exact integral_congr_ae (ae_of_all _ hU)
  refine ⟨U,hU,hi,hLI,g,?_,L.integral_comp_comm U⟩
  rw [he]
  exact hpoint

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ito_fubini_for_actual_operator
