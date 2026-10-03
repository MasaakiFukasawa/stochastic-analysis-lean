import Chapter13M2Evaluation
import Chapter13L2PointwiseAE

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Fixed-time evaluation of the stochastic-Fubini M2 identity, allowing
exactly the a.e.-parameter realization furnished by stochastic Fubini. -/
theorem m2_integral_fixed_time_ae {Ω E:Type*} {m:MeasurableSpace Ω} [MeasurableSpace E]
    (P:Measure Ω) [IsProbabilityMeasure P] {T:EReal} [Fact (0≤T)]
    (F:ClosedTime T → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    (hnull:∀t A,MeasurableSet[m] A → P A=0 → MeasurableSet[F t] A)
    (μ:Measure E) [SigmaFinite μ] (Z:E → continuousM2Terminal P F) (hi:Integrable Z μ)
    (N:E → ClosedTime T → Ω → ℝ)
    (hN:∀ᵐx∂μ,∃h:ContinuousM2Witness P F (N x),Z x=m2TerminalOfProcess P F (N x) h)
    (Y:ClosedTime T → Ω → ℝ) (hY:ContinuousM2Witness P F Y)
    (he:(∫x,Z x∂μ)=m2TerminalOfProcess P F Y hY)
    (t:ClosedTime T) (hm:Measurable (fun z:E × Ω => N z.1 t z.2)) :
    Y t=ᵐ[P] (fun w => ∫x,N x t w∂μ) := by
  letI:CompleteSpace (continuousM2Terminal P F):=continuous_m2_hilbert_complete P F hF hle hnull
  obtain ⟨L,hL⟩:=m2_evaluation_operator P F hle t
  have hl:∀ᵐx∂μ,(L (Z x):Ω → ℝ)=ᵐ[P] N x t := by
    filter_upwards [hN] with x hx
    obtain ⟨h,hz⟩:=hx
    rw [hz]
    exact hL (N x) h
  have hp:=l2_bochner_pointwise_ae μ P (fun z:E × Ω => N z.1 t z.2) hm
    (fun x => L (Z x)) (L.integrable_comp hi) hl
  have hc:=L.integral_comp_comm hi
  rw [he] at hc
  rw [hc] at hp
  exact (hL Y hY).symm.trans hp
/-- The displayed parameter field may be any jointly measurable realization
of the fixed-time values; M2 membership on exceptional parameters is irrelevant. -/
theorem m2_fixed_time_from_realizations {Ω E:Type*} {m:MeasurableSpace Ω} [MeasurableSpace E]
    (P:Measure Ω) [IsProbabilityMeasure P] {T:EReal} [Fact (0≤T)]
    (F:ClosedTime T → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    (hnull:∀t A,MeasurableSet[m] A → P A=0 → MeasurableSet[F t] A)
    (μ:Measure E) [SigmaFinite μ] (Z:E → continuousM2Terminal P F) (hi:Integrable Z μ)
    (H:E × Ω → ℝ) (hm:Measurable H) (t:ClosedTime T)
    (hrep:∀ᵐx∂μ,∃Y:ClosedTime T → Ω → ℝ,∃h:ContinuousM2Witness P F Y,
      Z x=m2TerminalOfProcess P F Y h ∧ Y t=ᵐ[P] (fun w => H (x,w)))
    (Y:ClosedTime T → Ω → ℝ) (hY:ContinuousM2Witness P F Y)
    (he:(∫x,Z x∂μ)=m2TerminalOfProcess P F Y hY) :
    Y t=ᵐ[P] (fun w => ∫x,H (x,w)∂μ) := by
  letI:CompleteSpace (continuousM2Terminal P F):=continuous_m2_hilbert_complete P F hF hle hnull
  obtain ⟨L,hL⟩:=m2_evaluation_operator P F hle t
  have hl:∀ᵐx∂μ,(L (Z x):Ω → ℝ)=ᵐ[P] (fun w => H (x,w)) := by
    filter_upwards [hrep] with x hx
    obtain ⟨V,hV,hz,hv⟩:=hx
    rw [hz]
    exact (hL V hV).trans hv
  have hp:=l2_bochner_pointwise_ae μ P H hm (fun x => L (Z x)) (L.integrable_comp hi) hl
  have hc:=L.integral_comp_comm hi
  rw [he] at hc
  rw [hc] at hp
  exact (hL Y hY).symm.trans hp

theorem m2_realizations_product_integrable {Ω E:Type*} {m:MeasurableSpace Ω} [MeasurableSpace E]
    (P:Measure Ω) [IsProbabilityMeasure P] {T:EReal} [Fact (0≤T)]
    (F:ClosedTime T → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    (hnull:∀t A,MeasurableSet[m] A → P A=0 → MeasurableSet[F t] A)
    (μ:Measure E) [SigmaFinite μ] (Z:E → continuousM2Terminal P F) (hi:Integrable Z μ)
    (H:E × Ω → ℝ) (hm:Measurable H) (t:ClosedTime T)
    (hrep:∀ᵐx∂μ,∃Y:ClosedTime T → Ω → ℝ,∃h:ContinuousM2Witness P F Y,
      Z x=m2TerminalOfProcess P F Y h ∧ Y t=ᵐ[P] (fun w => H (x,w)))
    : Integrable H (μ.prod P) := by
  letI:CompleteSpace (continuousM2Terminal P F):=continuous_m2_hilbert_complete P F hF hle hnull
  obtain ⟨L,hL⟩:=m2_evaluation_operator P F hle t
  have hl:∀ᵐx∂μ,(L (Z x):Ω → ℝ)=ᵐ[P] (fun w => H (x,w)) := by
    filter_upwards [hrep] with x hx
    obtain ⟨V,hV,hz,hv⟩:=hx
    rw [hz]
    exact (hL V hV).trans hv
  exact l2_realizations_product_integrable μ P H hm (fun x => L (Z x)) (L.integrable_comp hi) hl

end Asakura.Chapter13
#print axioms Asakura.Chapter13.m2_integral_fixed_time_ae

#print axioms Asakura.Chapter13.m2_fixed_time_from_realizations

#print axioms Asakura.Chapter13.m2_realizations_product_integrable
