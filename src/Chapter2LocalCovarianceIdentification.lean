import Chapter2LocalQuadraticVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Any local covariance agrees along any common bounded localizers with
the constructed bounded covariance, simultaneously at every time. -/
theorem local_covariance_matches_bounded_localizers
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y C : ClosedTime T → Ω → ℝ) (hC : LocalCovarianceWitness P F X Y C)
    (τ : ℕ → Ω → ClosedTime T)
    (ht : ∀ n t, MeasurableSet[F t] {ω | τ n ω ≤ t})
    (hm : ∀ ω, Monotone (fun n => τ n ω)) (htt : ∀ n ω, τ n ω < ⊤)
    (hc : ∀ ω t, t < ⊤ → ∃ n, t < τ n ω)
    (hx : ∀ n, (fun t ω => X (min (τ n ω) t) ω) ∈ boundedMProcess P F)
    (hy : ∀ n, (fun t ω => Y (min (τ n ω) t) ω) ∈ boundedMProcess P F) :
    ∀ᵐ ω ∂P, ∀ n t, C (min (τ n ω) t) ω =
      boundedCov P F hF hle hnull ⟨_,hx n⟩ ⟨_,hy n⟩ t ω := by
  obtain ⟨Q,hQm,hQc,hQbv,hQM,hstop⟩ := local_covariation_exists_along_localizers
    P F hF hle hnull X Y τ ht hm htt hc hx hy
  have hQ : LocalCovarianceWitness P F X Y Q :=
    ⟨m2_localization_implies_local P F hF hle _ τ ht hm htt hc hQM,
      ⟨τ,ht,hm,htt,hc,hQbv⟩⟩
  filter_upwards [hC.unique P F hF hle hQ,hstop] with ω he hs
  intro n t
  exact (he _ ((min_le_left _ _).trans_lt (htt n ω))).trans (hs n t)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_covariance_matches_bounded_localizers
