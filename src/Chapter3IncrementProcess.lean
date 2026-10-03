import Chapter3IncrementLemma
import Chapter2StoppedRegularity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Transfer M2 to an indistinguishable adapted continuous process. This
keeps the explicit square-defect formula, including its exact zero interval. -/
theorem m2_of_common_ae_equality
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (Z R : ClosedTime T → Ω → ℝ) (hZ : ContinuousM2Witness P F Z)
    (hm : ∀ t, Measurable[F t] (R t)) (hc : ∀ ω, Continuous (fun t => R t ω))
    (he : ∀ᵐ ω ∂P, ∀ t, Z t ω = R t ω) : ContinuousM2Witness P F R := by
  have he' (t) : Z t =ᵐ[P] R t := he.mono fun ω h => h t
  refine ⟨hm,fun t => (hZ.moment t).ae_eq (he' t),hc,?_,(he' ⊥).symm.trans hZ.initial⟩
  intro s t hst
  exact (condExp_congr_ae (he' t).symm).trans ((hZ.martingale s t hst).trans (he' s))

/-- The literal formula M^{n,j} of prop:qcv is a continuous M2 process,
not just an unspecified equivalent process. Its adaptedness and continuity
follow from the original processes stopped strictly before T. -/
theorem actual_increment_defect_m2
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Q : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hQ : LocalCovarianceWitness P F X X Q)
    (σ τ : Ω → ClosedTime T)
    (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (hστ : ∀ ω, σ ω ≤ τ ω) (hτtop : ∀ ω, τ ω < ⊤)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖X (min (τ ω) t) ω-X (min (σ ω) t) ω‖ ≤ δ) :
    ContinuousM2Witness P F (fun t ω =>
      (X (min (τ ω) t) ω-X (min (σ ω) t) ω)^2-
        (Q (min (τ ω) t) ω-Q (min (σ ω) t) ω)) := by
  obtain ⟨_,⟨Z,hZ,he⟩,_⟩ := stopped_increment_lemma P F hF hle hnull X Q hX hQ
    σ τ hσ hτ hστ hτtop δ hδ hb
  have hσtop (ω) : σ ω < ⊤ := (hστ ω).trans_lt (hτtop ω)
  obtain ⟨hxm,hxc⟩ := hX.stopped_regular P F hF hle τ hτ hτtop
  obtain ⟨hym,hyc⟩ := hX.stopped_regular P F hF hle σ hσ hσtop
  obtain ⟨hqm,hqc⟩ := hQ.stopped_regular P F hF hle hX hX τ hτ hτtop
  obtain ⟨hrm,hrc⟩ := hQ.stopped_regular P F hF hle hX hX σ hσ hσtop
  exact m2_of_common_ae_equality P F Z _ hZ
    (fun t => (((hxm t).sub (hym t)).pow_const 2).sub ((hqm t).sub (hrm t)))
    (fun ω => (((hxc ω).sub (hyc ω)).pow 2).sub ((hqc ω).sub (hrc ω))) he

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.m2_of_common_ae_equality
#print axioms Asakura.Chapter3Complete.actual_increment_defect_m2
