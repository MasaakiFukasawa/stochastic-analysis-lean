import Chapter2ItoConstructionAllTimeEnergy
import Chapter2ItoApproximationCharacterization
import Chapter2LocalCovarianceAE

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- Energy for any constructed Ito integral, without assuming a terminal
integrability condition or the energy identity itself. -/
theorem ito_covariance_formula_all_time_energy
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hAm : ∀ n ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (hAc : ∀ n ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (H : Ω × ℝ → ℝ)
    (hH : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val)))
    (hi : ∀ n, ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)^2)
      (intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) ω) (hAm n ω)
        (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure)
    (Y : ClosedTime T → Ω → ℝ) (hY : LocalMProcessWitness P F Y)
    (hYI : ItoCovarianceFormula P F X H Y) :
    ∃ B : ClosedTime T → Ω → ℝ, LocalCovarianceWitness P F Y Y B ∧
      ∀ j d (hd : 0 ≤ d), d ≤ c j →
        ∃ hAdm : ∀ ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 d),
        ∃ hAdc : ∀ ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 d),
        B (realTimeClamp d) =ᵐ[P] fun ω => ∫ r, H (ω,r)^2
          ∂(intervalStieltjes 0 d hd (fun r => A (realTimeClamp r) ω) (hAdm ω)
            (fun r hr => (hAdc ω r hr).mono inter_subset_left)).measure := by
  obtain ⟨N,u,V,Z,W,hu,hub,hVm,hZ,hW,hlim,B,hB,henergy,hprob⟩ :=
    ito_integral_constructed_with_all_time_energy P hT F hF hle hnull X A hX hA c hc hcm hcT
      hct hcut hcc hAm hAc H hH hi
  have hWI := ito_approximation_covariance_characterization P hT F hF hle hnull
    X A hX hA c hc hcm hcT hct hcut hcc hAm hAc H hH hi N u V Z W
      hu hub hVm hZ hW hlim hprob
  have he := hWI.unique P hT F hF hle hnull X _ Y H hX hW hY hYI
  exact ⟨B,hB.congr_ae_processes P F hF hle hW hW hY hY he he,henergy⟩

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.ito_covariance_formula_all_time_energy
