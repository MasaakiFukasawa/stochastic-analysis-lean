import FullAuditQVModification

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

/-- The complete bounded-martingale quadratic-variation construction in
 Theorem 2.4: the actual dyadic square sums, their uniform bound, Hilbert
 convex tails, Doob, the positive-part limit, a common null-set modification,
 uniqueness from A intersect M2, and the final norm bound. -/
theorem quadratic_variation_exists_unique_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (hTop : ∀ t, MemLp (X t) ∞ P) (hc : ∀ ω, Continuous (fun t => X t ω))
    (hmart : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s) (hz : X ⊥ =ᵐ[P] 0) :
    ∃ A : ClosedTime T → Ω → ℝ, (∀ t, Measurable[F t] (A t)) ∧
      (∀ ω, Continuous (fun t => A t ω)) ∧ (∀ ω, Monotone (fun t => A t ω)) ∧
      ContinuousM2Witness P F (fun t ω => X t ω^2-A t ω) ∧
      eLpNorm (fun ω => X ⊤ ω^2-A ⊤ ω) 2 P ≤
        ENNReal.ofReal (2*(eLpNorm (X ⊤) ∞ P).toReal*Real.sqrt (∫ ω, X ⊤ ω^2 ∂P)) ∧
      (∀ B : ClosedTime T → Ω → ℝ, (∀ ω, Monotone (fun t => B t ω)) →
        ContinuousM2Witness P F (fun t ω => X t ω^2-B t ω) →
        ∀ᵐ ω ∂P, ∀ t, A t ω = B t ω) := by
  obtain ⟨Y,hY,hmono,hbound⟩ := qv_exists_ae_monotone P F hF hle hnull X hm hTop hc hmart hz
  obtain ⟨A,hAm,hAc,hAo,hYA,he⟩ := qv_monotone_modification P F hle hnull X Y hm hc hY hmono
  refine ⟨A,hAm,hAc,hAo,hYA,?_,?_⟩
  · rw [eLpNorm_congr_ae (he.mono fun ω h => h ⊤)]
    exact hbound
  · intro B hBo hYB
    exact qv_uniqueness_written P F hF hle X A B hAo hBo hYA hYB

end Asakura.FullAudit
