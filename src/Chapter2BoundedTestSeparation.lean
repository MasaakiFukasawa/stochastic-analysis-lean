import Chapter2OneSidedStoppedCovariance
import Chapter2LocalSeparation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The localization of the test process in the printed stochastic-Fubini
proof is legitimate: bounded continuous M2 test processes already separate
all continuous local martingales. The stop and passage to a common null set
are explicitly proved. -/
theorem local_covariance_separates_bounded_tests
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X X' : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hX' : LocalMProcessWitness P F X')
    (htest : ∀ Y, Y ∈ boundedMProcess P F →
      ∃ C D, LocalCovarianceWitness P F X Y C ∧ LocalCovarianceWitness P F X' Y D ∧
        ∀ᵐ ω ∂P, ∀ t, t < ⊤ → C t ω = D t ω) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → X t ω = X' t ω := by
  apply local_covariance_separates P F hF hle X X' hX hX'
  intro Y hY
  obtain ⟨C,hC⟩ := local_covariance_witness_exists P F hF hle hnull X Y hX hY
  obtain ⟨D,hD⟩ := local_covariance_witness_exists P F hF hle hnull X' Y hX' hY
  obtain ⟨τ,hτ,hm,htt,hc,hb⟩ := hY.localizers
  have he n : ∀ᵐ ω ∂P, ∀ t, t < ⊤ →
      C (min (τ n ω) t) ω = D (min (τ n ω) t) ω := by
    obtain ⟨Cn,Dn,hCn,hDn,he⟩ := htest _ (hb n)
    have hCs := local_covariance_one_sided_stopping P F hF hle hnull Y X C Cn hY hX
      (hC.symm P F) (τ n) (hτ n) (hCn.symm P F)
    have hDs := local_covariance_one_sided_stopping P F hF hle hnull Y X' D Dn hY hX'
      (hD.symm P F) (τ n) (hτ n) (hDn.symm P F)
    filter_upwards [he,hCs,hDs] with ω hω hcw hdw
    intro t ht
    exact (hcw t ht).symm.trans ((hω t ht).trans (hdw t ht))
  refine ⟨C,D,hC,hD,?_⟩
  filter_upwards [ae_all_iff.mpr he] with ω hω
  intro t ht
  obtain ⟨n,hn⟩ := hc ω t ht
  simpa only [min_eq_right hn.le] using hω n t ht

/-- In particular it suffices to test against M2, as done in Section 2.8. -/
theorem local_covariance_separates_m2_tests
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X X' : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hX' : LocalMProcessWitness P F X')
    (htest : ∀ Y, ContinuousM2Witness P F Y →
      ∃ C D, LocalCovarianceWitness P F X Y C ∧ LocalCovarianceWitness P F X' Y D ∧
        ∀ᵐ ω ∂P, ∀ t, t < ⊤ → C t ω = D t ω) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → X t ω = X' t ω :=
  local_covariance_separates_bounded_tests P F hF hle hnull X X' hX hX'
    (fun Y hY => htest Y hY.1)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_covariance_separates_m2_tests
