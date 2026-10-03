import Chapter2ItoGlobalEnergyConstruction
import Chapter2ItoOperatorAssembly

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false

/-- Concrete Ito linear isometry from the actual progressive Stieltjes L2
classes into the manuscript's complete terminal M2 realization. All existence
and linearity inputs are supplied by the preceding construction. -/
theorem actual_ito_l2_isometry_constructed
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
    (hAmr : ∀ r, Measurable (fun ω => A (realTimeClamp r) ω))
    (ν : Measure (Ω × ℝ))
    (hν : ∀ f : Ω × ℝ → ℝ≥0∞, Measurable f →
      (∫⁻ z, f z ∂ν) = ∫⁻ ω, ⨆ n, ∫⁻ r, f (ω,r)
        ∂(intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) ω) (hAm n ω)
          (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure ∂P)
    : ∃ L : progressiveEnergyRange F c ν →ₗᵢ[ℝ] continuousM2Terminal P F,
      ∀ H : progressiveEnergyIntegrands F c ν,
        ∃ Y : ClosedTime T → Ω → ℝ, ∃ hY : ContinuousM2Witness P F Y,
          ItoCovarianceFormula P F X H.val Y ∧
          L ⟨progressiveEnergyToLp F c ν H,LinearMap.mem_range_self _ H⟩ = m2TerminalOfProcess P F Y hY := by
  apply ito_operator_from_characterized_existence P hT F hF hle hnull X hX c ν
  intro H
  obtain ⟨Y,hY,hYL,hchar,hiso⟩ := ito_integral_from_global_l2_energy P hT F hF hle hnull X A hX hA
    c hc hcm hcT hct hcut hcc hAm hAc H.val H.property.2.1 H.property.1 hAmr ν hν H.property.2.2
  refine ⟨Y,hY,hchar,?_⟩
  exact hiso.trans (real_l2_norm_sq_integral ν H.val H.property.2.2).symm

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.actual_ito_l2_isometry_constructed
