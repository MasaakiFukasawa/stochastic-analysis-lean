import Chapter2ActualItoOperator
import Chapter2ItoFubiniOperator
import Chapter2GlobalEnergyIdentity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
universe u
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- End-to-end stochastic Fubini: the Stieltjes measure and the Ito operator
are constructed, and the right side is identified with the pointwise
parameter integral. This proof uses the constructed Ito isometry directly;
the separate covariance-exchange module checks that part of the printed proof. -/
theorem constructed_stochastic_fubini
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
    : ∃ ν : Measure (Ω × ℝ), SigmaFinite ν ∧
      ∃ L : progressiveEnergyRange F c ν →ₗᵢ[ℝ] continuousM2Terminal P F,
      (∀ f : Ω × ℝ → ℝ≥0∞, Measurable f →
        (∫⁻ z, f z ∂ν) = ∫⁻ ω, ⨆ n, ∫⁻ r, f (ω,r)
          ∂(intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) ω) (hAm n ω)
            (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure ∂P) ∧
      (∀ H : progressiveEnergyIntegrands F c ν,
        ∃ Y : ClosedTime T → Ω → ℝ, ∃ hY : ContinuousM2Witness P F Y,
          ItoCovarianceFormula P F X H.val Y ∧
          L ⟨progressiveEnergyToLp F c ν H,LinearMap.mem_range_self _ H⟩ = m2TerminalOfProcess P F Y hY) ∧
      ∀ (E : Type u) [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
        (H : E × (Ω × ℝ) → ℝ), Measurable H →
        (∀ x n, @Measurable _ _
          (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
          (fun z : Ω × Icc (0:ℝ) (c n) => H (x,(z.1,z.2.val)))) →
        (∫⁻ x, eLpNorm (fun z => H (x,z)) 2 ν ∂μ) < ∞ →
        ∃ U : E → progressiveEnergyRange F c ν,
          (∀ x, (U x : Lp ℝ 2 ν) = l2Section ν H x) ∧
          Integrable U μ ∧ Integrable (fun x => L (U x)) μ ∧
          ∃ g : progressiveEnergyRange F c ν,
            ((g : Lp ℝ 2 ν) : Ω × ℝ → ℝ) =ᵐ[ν] (fun z => ∫ x, H (x,z) ∂μ) ∧
            (∫ x, L (U x) ∂μ) = L g := by
  obtain ⟨ν,hν,henergy⟩ := global_stieltjes_energy_identity P c (fun n => (hc n).le) hcm.monotone
    (fun ω r => A (realTimeClamp r) ω) hAm hAc hAmr
  letI : SigmaFinite ν := hν
  obtain ⟨L,hIto⟩ := actual_ito_l2_isometry_constructed P hT F hF hle hnull X A hX hA
    c hc hcm hcT hct hcut hcc hAm hAc hAmr ν henergy
  refine ⟨ν,hν,L,henergy,hIto,?_⟩
  intro E mE μ hμ H hH hp hN
  exact ito_fubini_for_actual_operator P F hF hle hnull c μ ν L H hH hp hN

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.constructed_stochastic_fubini
