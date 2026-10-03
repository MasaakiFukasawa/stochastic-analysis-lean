import FullAuditBoundedKW
import Chapter2SignedMeasureIdentification
import Chapter2SignedCumulativeContinuity
import Chapter2CommonTimeEquality
import Chapter2BoundedTestSeparation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The actual finite signed measure and integrability are part of the formula,
not an uninterpreted bilinear pairing. -/
def ItoCovarianceFormula
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (X : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ) (Y : ClosedTime T → Ω → ℝ) : Prop :=
  ∀ Y0 C0, LocalMProcessWitness P F Y0 → LocalCovarianceWitness P F X Y0 C0 →
    ∃ D, LocalCovarianceWitness P F Y Y0 D ∧
      ∀ d : ℝ, 0 ≤ d → (d:EReal) < T → ∃ ν : Ω → SignedMeasure ℝ,
        (∀ ω a b, 0 ≤ a → a ≤ b → ν ω (Ioc a b) =
          C0 (min (realTimeClamp b) (realTimeClamp d)) ω -
          C0 (min (realTimeClamp a) (realTimeClamp d)) ω) ∧
        (∀ᵐ ω ∂P, (ν ω).totalVariation (Iic 0) = 0) ∧
        (∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)) (ν ω).totalVariation) ∧
        D (realTimeClamp d) =ᵐ[P] fun ω => signedIntegralRaw (ν ω) (fun r => H (ω,r))

theorem finite_closed_time_real
    {T : EReal} [Fact (0 ≤ T)] (t : ClosedTime T) (ht : t < ⊤) :
    ∃ d : ℝ, 0 ≤ d ∧ (d:EReal) < T ∧ realTimeClamp d = t := by
  have htt : (t:EReal) < T := ht
  have he := EReal.coe_toReal (ne_of_lt (htt.trans_le le_top))
    (ne_of_gt ((EReal.bot_lt_coe 0).trans_le t.property.1))
  refine ⟨(t:EReal).toReal,EReal.toReal_nonneg t.property.1,he ▸ htt,?_⟩
  apply Subtype.ext
  rw [real_time_clamp_eq _ (EReal.toReal_nonneg t.property.1) (by rw [he]; exact t.property.2)]
  exact he

/-- The covariance formula determines the constructed local martingale uniquely.
The proof uses the chapter's separation proposition and continuity, not a
pre-existing stochastic integral. -/
theorem ItoCovarianceFormula.unique
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y Z : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hZ : LocalMProcessWitness P F Z)
    (hy : ItoCovarianceFormula P F X H Y) (hz : ItoCovarianceFormula P F X H Z) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → Y t ω = Z t ω := by
  apply local_covariance_separates P F hF hle Y Z hY hZ
  intro N hN
  obtain ⟨C,hC⟩ := local_covariance_witness_exists P F hF hle hnull X N hX hN
  obtain ⟨D,hD,hdy⟩ := hy N C hN hC
  obtain ⟨E,hE,hez⟩ := hz N C hN hC
  refine ⟨D,E,hD,hE,?_⟩
  apply local_covariance_common_time_equality P hT F Y N D E hY hN hD
    (hE.continuous_open_paths P F Z N E hZ hN)
  intro t ht
  obtain ⟨d,hd,hdT,rfl⟩ := finite_closed_time_real t ht
  obtain ⟨ν,hν,hν0,_,hνD⟩ := hdy d hd hdT
  obtain ⟨κ,hκ,hκ0,_,hκE⟩ := hez d hd hdT
  filter_upwards [hν0,hκ0,hνD,hκE] with ω hν0ω hκ0ω hDω hEω
  have heq : ν ω = κ ω := signed_measure_ext_positive_Ioc _ _ hν0ω hκ0ω
    (fun a b ha hab => (hν ω a b ha hab).trans (hκ ω a b ha hab).symm)
  rw [hDω,hEω,heq]

/-- Linearity of the covariance characterization, with the same actual
covariance measure for both summands after identifying interval increments. -/
theorem ItoCovarianceFormula.add_smul
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X Y Z : ClosedTime T → Ω → ℝ) (H G : Ω × ℝ → ℝ)
    (hy : ItoCovarianceFormula P F X H Y) (hz : ItoCovarianceFormula P F X G Z) (a : ℝ) :
    ItoCovarianceFormula P F X (fun z => a*H z+G z) (fun t ω => a*Y t ω+Z t ω) := by
  intro N C hN hC
  obtain ⟨D,hD,hd⟩ := hy N C hN hC
  obtain ⟨E,hE,he⟩ := hz N C hN hC
  refine ⟨(fun t ω => a*D t ω+E t ω),hD.bilinear P F hF hle hE a,?_⟩
  intro d hd0 hdT
  obtain ⟨ν,hν,hν0,hνI,hνD⟩ := hd d hd0 hdT
  obtain ⟨κ,hκ,hκ0,hκI,hκE⟩ := he d hd0 hdT
  have hme : ∀ᵐ ω ∂P, ν ω = κ ω := by
    filter_upwards [hν0,hκ0] with ω hν0ω hκ0ω
    exact signed_measure_ext_positive_Ioc _ _ hν0ω hκ0ω
      (fun b c hb hbc => (hν ω b c hb hbc).trans (hκ ω b c hb hbc).symm)
  refine ⟨ν,hν,hν0,?_,?_⟩
  · filter_upwards [hνI,hκI,hme] with ω hI hJ heq
    rw [← heq] at hJ
    exact (hI.const_mul a).add hJ
  · filter_upwards [hνI,hκI,hme,hνD,hκE] with ω hI hJ heq hDω hEω
    rw [← heq] at hJ hEω
    change a*D (realTimeClamp d) ω+E (realTimeClamp d) ω = _
    rw [hDω,hEω,signed_integral_add_smul _ _ _ hI hJ a]

/-- Once each integral has been constructed, linearity follows as an equality
of local martingale processes, outside a common null set for all finite times. -/
theorem ito_integral_linearity_of_characterization
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y Z W : ClosedTime T → Ω → ℝ) (H G : Ω × ℝ → ℝ) (a : ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hZ : LocalMProcessWitness P F Z) (hW : LocalMProcessWitness P F W)
    (hy : ItoCovarianceFormula P F X H Y) (hz : ItoCovarianceFormula P F X G Z)
    (hw : ItoCovarianceFormula P F X (fun z => a*H z+G z) W) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → W t ω = a*Y t ω+Z t ω := by
  exact hw.unique P hT F hF hle hnull X W (fun t ω => a*Y t ω+Z t ω)
    (fun z => a*H z+G z) hX hW ((hY.smul P F a).add P F hF hle hZ)
    (hy.add_smul P F hF hle X Y Z H G hz a)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ItoCovarianceFormula.unique
#print axioms Asakura.Chapter2Complete.ItoCovarianceFormula.add_smul
