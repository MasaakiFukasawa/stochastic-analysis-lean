import Chapter2ItoTerminalCharacterization
import Chapter2GlobalL2TerminalEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The actual global Stieltjes L2 hypothesis supplies all pathwise local
integrability and terminal-energy hypotheses. The output is the constructed
M2 integral with its covariance characterization and exact global energy. -/
theorem ito_integral_from_global_l2_energy
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
    (hHjoint : Measurable H)
    (hAmr : ∀ r, Measurable (fun ω => A (realTimeClamp r) ω))
    (ν : Measure (Ω × ℝ))
    (hν : ∀ f : Ω × ℝ → ℝ≥0∞, Measurable f →
      (∫⁻ z, f z ∂ν) = ∫⁻ ω, ⨆ n, ∫⁻ r, f (ω,r)
        ∂(intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) ω) (hAm n ω)
          (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure ∂P)
    (hL : MemLp H 2 ν) :
    ∃ Y : ClosedTime T → Ω → ℝ, ∃ hY : ContinuousM2Witness P F Y,
      LocalMProcessWitness P F Y ∧ ItoCovarianceFormula P F X H Y ∧
      ‖(hY.moment ⊤).toLp (Y ⊤)‖^2 = ∫ z, H z^2 ∂ν := by
  obtain ⟨CT,hCT,hCTnon,hi,hlim,henergy⟩ := global_l2_terminal_energy P c (fun n => (hc n).le)
    hcm.monotone (fun ω r => A (realTimeClamp r) ω) hAm hAc hAmr ν hν H hHjoint hL
  obtain ⟨Y,hY,hYL,hchar,hiso,_⟩ := ito_terminal_isometry_and_covariance_constructed
    P hT F hF hle hnull X A hX hA c hc hcm hcT hct hcut hcc hAm hAc H hH hi CT hCT hlim
  exact ⟨Y,hY,hYL,hchar,hiso.trans henergy⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ito_integral_from_global_l2_energy
