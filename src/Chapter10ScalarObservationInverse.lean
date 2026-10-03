import Chapter10DeterministicIntegralIdentity
import Chapter2VariationStoppedInterval
import Chapter2ItoIntegrandEncoding

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Actual stochastic integration by reciprocal deterministic coefficients
recovers a scalar observation, including its initial-value correction. -/
theorem scalar_observation_inverse {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X A M : HalfClosedTime → Ω → ℝ) (hX : SemimartingaleDecomposition P F X A M)
    (D J : ℝ → ℝ) (hD : Continuous D) (hJ : Continuous J)
    (hinv : ∀ r,0≤r → D r*J r=1) :
    ∃ (c : ℕ → ℝ) (hc : ∀ n,0≤c n),
      (∀ t : HalfClosedTime,t<⊤ → ∃ n,t<realTimeClamp (c n)) ∧
      ∃ A1 M1 Z,
        SemimartingaleDecomposition P F (fun t w => A1 t w+M1 t w) A1 M1 ∧
        VariationIntegralFormula P c hc A (fun z => J z.2) A1 ∧
        ItoCovarianceFormula P F M (fun z => J z.2) M1 ∧
        SemimartingaleIntegralFormula P F c hc A1 M1 (fun z => D z.2) Z ∧
        ∀ᵐ w ∂P,∀ t,t<⊤ → Z t w=X t w-X ⊥ w := by
  obtain ⟨c,hc,hcc,A1,M1,Z,U,h1,hA1,hM1,hZ,hU,he⟩ :=
    semimartingale_associativity_constructed P (by simp : (0:EReal)<⊤) F hF hle hnull
      X A M hX (fun z => D z.2) (fun z => J z.2)
      (fun r _ _ => show Measurable[F (realTimeClamp r)] (fun _ : Ω => D r) from measurable_const)
      (fun r _ _ => show Measurable[F (realTimeClamp r)] (fun _ : Ω => J r) from measurable_const)
      (fun _ _ _ _ => hD.continuousOn) (fun _ _ _ _ => hJ.continuousOn)
  have hU1 : SemimartingaleIntegralFormula P F c hc A M (fun _ => 1) U := by
    obtain ⟨I,N,hUN,hI,hN⟩ := hU
    exact ⟨I,N,hUN,
      hI.congr_on_time_domain P c hc (fun n => EReal.coe_lt_top _) A I _ _ (fun w r hr _ => hinv r hr),
      hN.congr_on_time_domain P F M N _ _ (fun w r hr _ => hinv r hr)⟩
  have hid := deterministic_integral_identity P F hF hle hnull X A M U hX c hc
    (fun n => EReal.coe_lt_top _) hcc hU1
  refine ⟨c,hc,hcc,A1,M1,Z,h1,hA1,hM1,hZ,?_⟩
  filter_upwards [he,hid] with w hw hi
  exact fun t ht => (hw t ht).trans (hi t ht)

end Asakura.Chapter10
