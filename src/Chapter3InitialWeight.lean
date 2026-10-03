import Chapter3WeightedLocalMartingale
import Chapter2ItoCovarianceCharacterization

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- A bounded initial-information coefficient pulls through the actual
conditional expectations, including the a.e. initial-zero condition. -/
theorem bounded_initial_weight_m2
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (Y : ClosedTime T → Ω → ℝ) (hY : ContinuousM2Witness P F Y)
    (A : Ω → ℝ) (hA : Measurable[F ⊥] A) (hAb : MemLp A ∞ P) :
    ContinuousM2Witness P F (fun t ω => A ω*Y t ω) := by
  have h2 t : MemLp (fun ω => A ω*Y t ω) 2 P := hAb.mul (hY.moment t)
  refine ⟨fun t => (hA.mono (hF bot_le) le_rfl).mul (hY.adapted t),h2,
    fun ω => continuous_const.mul (hY.path ω),?_,?_⟩
  · intro s t hst
    have hp := unbounded_pullout_by_restriction P (hle s) A (Y t)
      (hA.mono (hF bot_le) le_rfl).stronglyMeasurable
      ((h2 t).integrable (by norm_num)) ((hY.moment t).integrable (by norm_num))
    filter_upwards [hp,hY.martingale s t hst] with ω hpω hYω
    simpa only [Pi.mul_apply,Pi.mul_def,hYω] using hpω
  · filter_upwards [hY.initial] with ω hω
    simp only [Pi.zero_apply] at hω ⊢
    rw [hω,mul_zero]

theorem bounded_initial_weight_local
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (Y : ClosedTime T → Ω → ℝ) (hY : LocalMProcessWitness P F Y)
    (A : Ω → ℝ) (hA : Measurable[F ⊥] A) (hAb : MemLp A ∞ P) :
    LocalMProcessWitness P F (fun t ω => A ω*Y t ω) := by
  obtain ⟨σ,hs,hm,ht,hc,hYσ⟩ := hY.localizers
  exact m2_localization_implies_local P F hF hle _ σ hs hm ht hc
    (fun k => bounded_initial_weight_m2 P F hF hle _ (hYσ k).1 A hA hAb)

theorem bounded_initial_weight_covariance
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X Y C : ClosedTime T → Ω → ℝ) (hC : LocalCovarianceWitness P F X Y C)
    (A : Ω → ℝ) (hA : Measurable[F ⊥] A) (hAb : MemLp A ∞ P) :
    LocalCovarianceWitness P F (fun t ω => A ω*X t ω) Y (fun t ω => A ω*C t ω) := by
  refine ⟨?_,random_scalar_local_variation F C hC.variation A⟩
  have h := bounded_initial_weight_local P F hF hle _ hC.defect A hA hAb
  convert h using 1
  funext t ω
  ring

/-- The initial-information coefficient also pulls through the signed
covariance integral, proving its Ito-integral identity. -/
theorem bounded_initial_weight_ito_formula
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X Y : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hI : ItoCovarianceFormula P F X H Y)
    (A : Ω → ℝ) (hA : Measurable[F ⊥] A) (hAb : MemLp A ∞ P) :
    ItoCovarianceFormula P F X (fun z => A z.1*H z) (fun t ω => A ω*Y t ω) := by
  intro N C hN hC
  obtain ⟨D,hD,hd⟩ := hI N C hN hC
  refine ⟨fun t ω => A ω*D t ω,bounded_initial_weight_covariance P F hF hle Y N D hD A hA hAb,?_⟩
  intro d hd0 hdT
  obtain ⟨ν,hν,hν0,hi,he⟩ := hd d hd0 hdT
  refine ⟨ν,hν,hν0,hi.mono (fun ω hω => hω.const_mul (A ω)),?_⟩
  filter_upwards [hi,he] with ω hiω heω
  change A ω*D (realTimeClamp d) ω = _
  rw [heω]
  unfold signedIntegralRaw
  rw [integral_const_mul,integral_const_mul]
  ring

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.bounded_initial_weight_m2
#print axioms Asakura.Chapter3Complete.bounded_initial_weight_local
#print axioms Asakura.Chapter3Complete.bounded_initial_weight_covariance
#print axioms Asakura.Chapter3Complete.bounded_initial_weight_ito_formula
