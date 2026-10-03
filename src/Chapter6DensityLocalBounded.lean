import Chapter6DensityMartingale
import Chapter2CanonicalLocalizers

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- A true continuous martingale has explicit bounded localizers, obtained
by level stopping. This supplies the localization needed after Bayes' formula. -/
theorem continuous_martingale_is_local
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (X : ClosedTime T → Ω → ℝ)
    (ha : ∀ t,Measurable[F t] (X t)) (hc : ∀ w,Continuous (fun t => X t w))
    (hi : ∀ t,Integrable (X t) P)
    (hM : ∀ s t,s ≤ t → P[X t|F s] =ᵐ[P] X s) (hz : X ⊥ =ᵐ[P] 0)
    (u : ℕ → ClosedTime T) (hu : Monotone u) (hut : ∀ n,u n < ⊤)
    (huc : ∀ t,t < ⊤ → ∃ n,t < u n) : LocalMProcessWitness P F X := by
  obtain ⟨hs,hm,ht,hco,hb⟩ := canonical_continuous_localizers P F hF X ha
    (fun w _ _ => (hc w).continuousAt) hz u hu hut huc
  refine ⟨_,hs,hm,ht,hco,?_⟩
  intro n
  exact bounded_stop_of_integrable_martingale P F hF hle X ha hi hc hM hz _ (hs n) n
    (fun t => (hb n).mono fun _ h => h t)

/-- A Q martingale times its continuous conditional density is a P local
martingale. The weighted integrability and bounded localization are proved. -/
theorem density_times_martingale_local
    {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (d : Ω → ℝ≥0) (hd : Measurable d)
    (hdi : Integrable (fun w => (d w : ℝ)) P)
    (hp : ∀ᵐ w ∂P,0 < (d w : ℝ))
    (hQ : Q = P.withDensity (fun w => (d w : ℝ≥0∞)))
    (M X : ClosedTime T → Ω → ℝ)
    (hMa : ∀ t,Measurable[F t] (M t)) (hMc : ∀ w,Continuous (fun t => M t w))
    (hME : ∀ t,M t =ᵐ[P] P[(fun w => (d w : ℝ))|F t])
    (hXa : ∀ t,Measurable[F t] (X t)) (hXc : ∀ w,Continuous (fun t => X t w))
    (hXi : ∀ t,Integrable (X t) Q)
    (hXM : ∀ s t,s ≤ t → Q[X t|F s] =ᵐ[Q] X s) (hX0 : X ⊥ =ᵐ[Q] 0)
    (u : ℕ → ClosedTime T) (hu : Monotone u) (hut : ∀ n,u n < ⊤)
    (huc : ∀ t,t < ⊤ → ∃ n,t < u n) :
    LocalMProcessWitness P F (fun t w => M t w*X t w) := by
  have he t : (fun w => M t w*X t w) =ᵐ[P]
      (fun w => P[(fun w => (d w : ℝ))|F t] w*X t w) :=
    (hME t).mono fun _ h => congrArg (fun z => z*_) h
  have hi t : Integrable (fun w => M t w*X t w) P :=
    (conditional_density_product P Q (hle t) d hd hdi hQ (X t) (hXa t).stronglyMeasurable (hXi t)).1.congr (he t).symm
  have hm := (density_martingale_identity_iff P Q F hF hle d hd hdi hp hQ X
    (fun t => (hXa t).stronglyMeasurable) hXi).mp hXM
  have hz : X ⊥ =ᵐ[P] 0 := by
    rw [hQ] at hX0
    exact (positive_density_ae_iff P d hd hp _).mp hX0
  apply continuous_martingale_is_local P F hF hle _
    (fun t => (hMa t).mul (hXa t)) (fun w => (hMc w).mul (hXc w)) hi _ _ u hu hut huc
  · intro s t hst
    exact (condExp_congr_ae (he t)).trans ((hm s t hst).trans (he s).symm)
  · filter_upwards [hz] with w hw
    simp only [Pi.mul_apply,hw,Pi.zero_apply,mul_zero]

end Asakura.Chapter6
