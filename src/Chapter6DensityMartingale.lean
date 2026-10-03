import Chapter6DensityConditional

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace Asakura.Chapter6
open Asakura.FullAudit
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

lemma positive_density_ae_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (d : Ω → ℝ≥0) (hd : Measurable d)
    (hp : ∀ᵐ w ∂P, 0 < (d w : ℝ)) (p : Ω → Prop) :
    (∀ᵐ w ∂P.withDensity (fun w => (d w : ℝ≥0∞)), p w) ↔ ∀ᵐ w ∂P, p w := by
  rw [ae_withDensity_iff hd.coe_nnreal_ennreal]
  constructor
  · intro h
    filter_upwards [h,hp] with w hw hpw
    apply hw
    intro hz
    have hdw : d w = 0 := ENNReal.coe_eq_zero.mp hz
    simp [hdw] at hpw
  · intro h
    exact h.mono fun _ hw _ => hw

/-- The product criterion for true martingales at deterministic times, with
integrability and equivalence of null sets supplied by the actual density. -/
theorem density_martingale_identity_iff
    {Ω ι : Type*} {m : MeasurableSpace Ω} [Preorder ι]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (d : Ω → ℝ≥0) (hd : Measurable d)
    (hdi : Integrable (fun w => (d w : ℝ)) P)
    (hp : ∀ᵐ w ∂P, 0 < (d w : ℝ))
    (hQ : Q = P.withDensity (fun w => (d w : ℝ≥0∞)))
    (X : ι → Ω → ℝ) (hX : ∀ t,StronglyMeasurable[F t] (X t))
    (hi : ∀ t,Integrable (X t) Q) :
    (∀ s t,s ≤ t → Q[X t|F s] =ᵐ[Q] X s) ↔
    (∀ s t,s ≤ t →
      P[(fun w => P[(fun w => (d w : ℝ))|F t] w * X t w)|F s] =ᵐ[P]
        (fun w => P[(fun w => (d w : ℝ))|F s] w * X s w)) := by
  have hae (p : Ω → Prop) : (∀ᵐ w ∂Q,p w) ↔ ∀ᵐ w ∂P,p w := by
    rw [hQ]
    exact positive_density_ae_iff P d hd hp p
  have ht (s t : ι) (hst : s ≤ t) := density_conditional_transport P Q (hF hst) (hle t)
    d hd hdi hp hQ (X t) (hX t) (hi t)
  constructor
  · intro h s t hst
    exact (ht s t hst).trans ((hae _).mp (h s t hst) |>.mono fun w hw => by dsimp only; rw [hw])
  · intro h s t hst
    apply (hae _).mpr
    have hz := exercise_ce_strictly_positive P (hle s) hdi hp
    filter_upwards [ht s t hst,h s t hst,hz] with w ht hw hz
    exact mul_left_cancel₀ (ne_of_gt hz) (ht.symm.trans hw)

end Asakura.Chapter6
