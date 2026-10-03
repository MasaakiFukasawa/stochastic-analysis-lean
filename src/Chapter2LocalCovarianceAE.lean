import Chapter2StoppedRegularity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem LocalMProcessWitness.congr_ae_of_stopped_regular
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    {X Y : ClosedTime T → Ω → ℝ} (hX : LocalMProcessWitness P F X)
    (he : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → X t ω = Y t ω)
    (hreg : ∀ σ : Ω → ClosedTime T,
      (∀ t, MeasurableSet[F t] {ω | σ ω ≤ t}) → (∀ ω, σ ω < ⊤) →
      (∀ t, Measurable[F t] (fun ω => Y (min (σ ω) t) ω)) ∧
      (∀ ω, Continuous (fun t => Y (min (σ ω) t) ω))) :
    LocalMProcessWitness P F Y := by
  obtain ⟨τ,hτ,hm,ht,hc,hb⟩ := hX.localizers
  refine ⟨τ,hτ,hm,ht,hc,?_⟩
  intro n
  obtain ⟨hym,hyc⟩ := hreg (τ n) (hτ n) (ht n)
  have he' t : (fun ω => X (min (τ n ω) t) ω) =ᵐ[P] (fun ω => Y (min (τ n ω) t) ω) :=
    he.mono (fun ω hω => hω _ ((min_le_left _ _).trans_lt (ht n ω)))
  refine ⟨⟨hym,fun t => ((hb n).1.moment t).ae_eq (he' t),hyc,?_,
    (he' ⊥).symm.trans (hb n).1.initial⟩,fun t => ((hb n).2 t).ae_eq (he' t)⟩
  intro s t hst
  exact (condExp_congr_ae (he' t).symm).trans (((hb n).1.martingale s t hst).trans (he' s))

/-- The same covariation process represents indistinguishable local
martingales. This justifies using regular quadratic-variation representatives
without changing the underlying stochastic integral problem. -/
theorem LocalCovarianceWitness.congr_ae_processes
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    {X Y X' Y' C : ClosedTime T → Ω → ℝ}
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hX' : LocalMProcessWitness P F X') (hY' : LocalMProcessWitness P F Y')
    (hC : LocalCovarianceWitness P F X Y C)
    (heX : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → X t ω = X' t ω)
    (heY : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → Y t ω = Y' t ω) :
    LocalCovarianceWitness P F X' Y' C := by
  refine ⟨hC.defect.congr_ae_of_stopped_regular P F ?_ ?_,hC.variation⟩
  · filter_upwards [heX,heY] with ω hx hy
    intro t ht
    rw [hx t ht,hy t ht]
  · intro σ hσ hσt
    obtain ⟨hxm,hxc⟩ := hX'.stopped_regular P F hF hle σ hσ hσt
    obtain ⟨hym,hyc⟩ := hY'.stopped_regular P F hF hle σ hσ hσt
    obtain ⟨hcm,hcc⟩ := hC.stopped_regular P F hF hle hX hY σ hσ hσt
    exact ⟨fun t => ((hxm t).mul (hym t)).sub (hcm t),fun ω => ((hxc ω).mul (hyc ω)).sub (hcc ω)⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.LocalCovarianceWitness.congr_ae_processes
