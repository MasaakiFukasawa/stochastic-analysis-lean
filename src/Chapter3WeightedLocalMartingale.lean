import Chapter3WeightedStoppedM2
import Chapter2M2Localization
import Chapter2LocalCovarianceRules

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- A bounded F_sigma measurable coefficient may multiply a local
martingale that is zero before sigma. The M2 result is applied to the
actual localizers, then their M2 localization is refined to M_loc. -/
theorem bounded_stopped_weight_local
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (Y : ClosedTime T → Ω → ℝ) (hY : LocalMProcessWitness P F Y)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hz : ∀ ω t, t ≤ σ ω → Y t ω = 0)
    (A : Ω → ℝ) (hA : Measurable[writtenStoppedSpace m F σ hσ] A)
    (hAb : MemLp A ∞ P) :
    LocalMProcessWitness P F (fun t ω => A ω*Y t ω) := by
  obtain ⟨τ,ht,hm,htt,hc,hYτ⟩ := hY.localizers
  apply m2_localization_implies_local P F hF hle _ τ ht hm htt hc
  intro n
  exact bounded_stopped_weight_m2 P F hF hle _ (hYτ n).1 σ hσ
    (fun ω t hts => hz ω _ ((min_le_right _ _).trans hts)) A hA hAb

/-- Pathwise finite variation is preserved by a random scalar constant in
time. Its stochastic measurability is supplied separately when needed. -/
theorem random_scalar_local_variation
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (C : ClosedTime T → Ω → ℝ)
    (hC : LocalVariationWitness F C) (A : Ω → ℝ) :
    LocalVariationWitness F (fun t ω => A ω*C t ω) := by
  obtain ⟨τ,ht,hm,htt,hc,hv⟩ := hC.localizers
  exact ⟨τ,ht,hm,htt,hc,fun n ω => monotone_difference_smul _ (hv n ω) (A ω)⟩

/-- Covariance of a bounded stopping-time weighted increment. This proves
the weighted product compensator needed to identify a step Ito integral. -/
theorem bounded_stopped_weight_covariance
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X Y C : ClosedTime T → Ω → ℝ) (hC : LocalCovarianceWitness P F X Y C)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hXz : ∀ ω t, t ≤ σ ω → X t ω = 0)
    (hCz : ∀ ω t, t ≤ σ ω → C t ω = 0)
    (A : Ω → ℝ) (hA : Measurable[writtenStoppedSpace m F σ hσ] A)
    (hAb : MemLp A ∞ P) :
    LocalCovarianceWitness P F (fun t ω => A ω*X t ω) Y (fun t ω => A ω*C t ω) := by
  refine ⟨?_,random_scalar_local_variation F C hC.variation A⟩
  have h := bounded_stopped_weight_local P F hF hle _ hC.defect σ hσ
    (fun ω t ht => by simp only [hXz ω t ht,hCz ω t ht,zero_mul,sub_self]) A hA hAb
  convert h using 1
  funext t ω
  ring

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.bounded_stopped_weight_local
#print axioms Asakura.Chapter3Complete.random_scalar_local_variation
#print axioms Asakura.Chapter3Complete.bounded_stopped_weight_covariance
