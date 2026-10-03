import Chapter2M2ProcessRepresentatives
import Chapter2L2BochnerPointwise

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Evaluation of an M2 martingale at any fixed time is a bounded linear
map into L2, explicitly realized by conditional expectation of its terminal value. -/
theorem m2_evaluation_operator {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {T:EReal} [Fact (0≤T)]
    (F:ClosedTime T → MeasurableSpace Ω) (hle:∀t,F t≤m) (t:ClosedTime T) :
    ∃L:continuousM2Terminal P F →L[ℝ] Lp ℝ 2 P,
      ∀Y:ClosedTime T → Ω → ℝ,∀hY:ContinuousM2Witness P F Y,
        ((L (m2TerminalOfProcess P F Y hY):Lp ℝ 2 P):Ω → ℝ)=ᵐ[P] Y t := by
  let L:continuousM2Terminal P F →L[ℝ] Lp ℝ 2 P :=
    (lpMeas ℝ ℝ (F t) 2 P).subtypeL.comp
      ((condExpL2 ℝ ℝ (hle t)).comp (continuousM2Terminal P F).subtypeL)
  refine ⟨L,?_⟩
  intro Y hY
  change ((condExpL2 ℝ ℝ (hle t) ((hY.moment ⊤).toLp (Y ⊤)) : Lp ℝ 2 P):Ω → ℝ)=ᵐ[P] Y t
  exact ((hY.moment ⊤).condExpL2_ae_eq_condExp (hle t)).trans (hY.martingale t ⊤ le_top)

/-- The M2-valued integral used in stochastic Fubini yields the usual
pointwise parameter integral at every fixed time. -/
theorem m2_integral_fixed_time {Ω E:Type*} {m:MeasurableSpace Ω} [MeasurableSpace E]
    (P:Measure Ω) [IsProbabilityMeasure P] {T:EReal} [Fact (0≤T)]
    (F:ClosedTime T → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    (hnull:∀t A,MeasurableSet[m] A → P A=0 → MeasurableSet[F t] A)
    (μ:Measure E) [SigmaFinite μ] (N:E → ClosedTime T → Ω → ℝ)
    (hN:∀x,ContinuousM2Witness P F (N x))
    (hi:Integrable (fun x => m2TerminalOfProcess P F (N x) (hN x)) μ)
    (Y:ClosedTime T → Ω → ℝ) (hY:ContinuousM2Witness P F Y)
    (he:(∫x,m2TerminalOfProcess P F (N x) (hN x)∂μ)=m2TerminalOfProcess P F Y hY)
    (t:ClosedTime T) (hm:Measurable (fun z:E × Ω => N z.1 t z.2)) :
    Y t=ᵐ[P] (fun w => ∫x,N x t w∂μ) := by
  letI:CompleteSpace (continuousM2Terminal P F):=continuous_m2_hilbert_complete P F hF hle hnull
  obtain ⟨L,hL⟩:=m2_evaluation_operator P F hle t
  have hlp x:L (m2TerminalOfProcess P F (N x) (hN x))=(hN x |>.moment t).toLp (N x t) := by
    apply Lp.ext
    exact (hL (N x) (hN x)).trans ((hN x).moment t).coeFn_toLp.symm
  have hI:Integrable (fun x => ((hN x).moment t).toLp (N x t)) μ := by
    simpa only [Function.comp_def,hlp] using L.integrable_comp hi
  have hp:=l2_bochner_integral_pointwise μ P (fun z:E × Ω => N z.1 t z.2) hm
    (fun x => (hN x).moment t) hI
  have hcomm:=L.integral_comp_comm hi
  simp only [hlp,he] at hcomm
  change ((∫x,((hN x).moment t).toLp (N x t)∂μ : Lp ℝ 2 P):Ω → ℝ)=ᵐ[P] (fun w => ∫x,N x t w∂μ) at hp
  rw [hcomm] at hp
  exact (hL Y hY).symm.trans hp
end Asakura.Chapter13
#print axioms Asakura.Chapter13.m2_evaluation_operator
#print axioms Asakura.Chapter13.m2_integral_fixed_time
