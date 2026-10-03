import Chapter2ItoConstructionAllTests
import Chapter2ItoCovarianceCharacterization

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Connect the uniqueness and linearity characterization to the actual
Hilbert-density and local-martingale-completion construction. -/
theorem ito_integral_exists_with_covariance_characterization
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
        (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure) :
    ∃ Y : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Y ∧ ItoCovarianceFormula P F X H Y := by
  obtain ⟨N,u,V,Z,Y,hu,hub,hVm,hZ,hY,hlim,hprob,hcov⟩ :=
    ito_integral_constructed_all_test_covariances P hT F hF hle hnull X A hX hA
      c hc hcm hcT hct hcut hcc hAm hAc H hH hi
  refine ⟨fun t ω => extendOpenPath (Y ω) t,hY,?_⟩
  intro Y0 C0 hY0 hC0
  obtain ⟨D,hD,hd⟩ := hcov Y0 C0 hY0 hC0
  refine ⟨D,hD,?_⟩
  intro d hd0 hdT
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d:EReal) < T
    rw [real_time_clamp_eq d hd0 hdT.le]
    exact hdT
  obtain ⟨j,hj⟩ := hcc _ hdt
  have hdj : d ≤ c j := by
    change (realTimeClamp d:EReal) < (realTimeClamp (c j):EReal) at hj
    rw [real_time_clamp_eq d hd0 hdT.le,real_time_clamp_eq (c j) (hc j).le (hcT j).le] at hj
    exact (EReal.coe_lt_coe_iff.mp hj).le
  exact hd j d hd0 hdj

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ito_integral_exists_with_covariance_characterization
