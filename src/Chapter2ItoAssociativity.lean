import Chapter2ItoCovarianceProcessFormula
import Chapter2SignedDensityIdentification

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Associativity of actual Ito integrals, proved by the manuscript's
covariance-separation hint. Each integral is characterized by the actual
signed covariance measure, and the deterministic iterated integral identity
has been proved from simple approximation and dominated convergence. -/
theorem ito_integral_associativity
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y Z W : ClosedTime T → Ω → ℝ) (G H : Ω × ℝ → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hZ : LocalMProcessWitness P F Z) (hW : LocalMProcessWitness P F W)
    (hG : ∀ ω, Measurable (fun r => G (ω,r))) (hH : ∀ ω, Measurable (fun r => H (ω,r)))
    (hy : ItoCovarianceFormula P F X G Y)
    (hz : ItoCovarianceFormula P F Y H Z)
    (hw : ItoCovarianceFormula P F X (fun z => H z*G z) W) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → Z t ω = W t ω := by
  apply local_covariance_separates P F hF hle Z W hZ hW
  intro N hN
  obtain ⟨C,hC⟩ := local_covariance_witness_exists P F hF hle hnull X N hX hN
  obtain ⟨D,hD,hDp⟩ := hy.finite_process_formula P F X Y G hY hG N C hN hC
  obtain ⟨E,hE,hEp⟩ := hz N D hN hD
  obtain ⟨K,hK,hKp⟩ := hw N C hN hC
  refine ⟨E,K,hE,hK,?_⟩
  apply local_covariance_common_time_equality P hT F Z N E K hZ hN hE
    (hK.continuous_open_paths P F W N K hW hN)
  intro t ht
  obtain ⟨d,hd0,hdT,rfl⟩ := finite_closed_time_real t ht
  obtain ⟨ν,hν,hν0,hνi,hνD⟩ := hDp d hd0 hdT
  obtain ⟨κ,hκ,hκ0,hκi,hκE⟩ := hEp d hd0 hdT
  obtain ⟨ξ,hξ,hξ0,hξi,hξK⟩ := hKp d hd0 hdT
  filter_upwards [hν0,hνi,hνD,hκ0,hκi,hκE,hξ0,hξi,hξK]
    with ω hn0 hni hnD hk0 hki hkE hl0 hli hlK
  have heq : ξ ω = ν ω := signed_measure_ext_positive_Ioc _ _ hl0 hn0
    (fun a b ha hab => (hξ ω a b ha hab).trans (hν ω a b ha hab).symm)
  rw [heq] at hli hlK
  have hνr : ν ω = (ν ω).restrict (Iic d) := by
    apply signed_stopped_interval_consistency (fun r => C (realTimeClamp r) ω)
      d d hd0 le_rfl (ν ω) (ν ω) hn0 hn0
    all_goals
      intro a b ha hab
      simpa only [real_time_clamp_mono.map_min] using hν ω a b ha hab
  rw [hkE,hlK]
  apply signed_iterated_integral_of_cumulative (ν ω) (κ ω)
    (fun r => G (ω,r)) (fun r => H (ω,r)) (hG ω) (hH ω) hni hki hli d hn0 hk0 hνr
  intro a b ha hab
  have ha' := hnD (min a d) ⟨le_min ha hd0,min_le_right _ _⟩
  have hb' := hnD (min b d) ⟨le_min (ha.trans hab) hd0,min_le_right _ _⟩
  simp only [real_time_clamp_mono.map_min] at ha' hb'
  rw [hκ ω a b ha hab,ha',hb']

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ito_integral_associativity
