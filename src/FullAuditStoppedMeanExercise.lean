import FullAuditContinuousOptional
import FullAuditStoppingExercises

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written

/-- The converse in the exercise uses precisely the suggested two-valued
 stopping times; integrability of these values follows from the given marginals. -/
theorem martingale_of_zero_stopped_means {Ω ι : Type*} {m : MeasurableSpace Ω}
    [LinearOrder ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ι → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t)) (hi : ∀ t, Integrable (X t) P)
    (hz : ∀ (τ : Ω → ι), (∀ t, MeasurableSet[F t] {ω | τ ω ≤ t}) →
      ∫ ω, X (τ ω) ω ∂P = 0) :
    ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s := by
  classical
  intro s t hst
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (hle s) (hi t)
    (fun _ _ _ => (hi s).integrableOn) _ (hm s).stronglyMeasurable.aestronglyMeasurable
  intro A hA _
  have hAm := hle s _ hA
  have hτ := two_time_stopping F hF A s t hst hA
  have hmean := hz (fun ω => if ω ∈ A then s else t) hτ
  have hconst := hz (fun _ => t) (fun r => by
    by_cases h : t ≤ r <;> simp [h])
  have he : (fun ω => X (if ω ∈ A then s else t) ω) = A.indicator (X s) + Aᶜ.indicator (X t) := by
    funext ω; by_cases h : ω ∈ A <;> simp [Set.indicator,h]
  rw [he] at hmean
  change (∫ ω, A.indicator (X s) ω + Aᶜ.indicator (X t) ω ∂P) = 0 at hmean
  rw [integral_add ((hi s).indicator hAm) ((hi t).indicator hAm.compl),
    integral_indicator hAm,integral_indicator hAm.compl] at hmean
  have ht := integral_add_compl hAm (hi t)
  linarith

/-- Full solution of the zero-stopped-mean exercise for the actual continuous
 time interval, using the previously checked optional-sampling proof. -/
theorem zero_stopped_mean_exercise {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} (hT : 0 ≤ T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (hi : ∀ t, Integrable (X t) P)
    (hr : ∀ ω t, ContinuousWithinAt (fun s => X s ω) (Ici t) t)
    (hzero : X ⟨0,le_rfl,hT⟩ =ᵐ[P] 0) :
    (∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s) ↔
    ∀ (τ : Ω → ClosedTime T) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t}),
      Integrable (fun ω => X (τ ω) ω) P ∧ ∫ ω, X (τ ω) ω ∂P = 0 := by
  constructor
  · intro hmart τ hτ
    let topTime : ClosedTime T := ⟨T,hT,le_rfl⟩
    let zeroTime : ClosedTime T := ⟨0,le_rfl,hT⟩
    have hc (t : ClosedTime T) : X t =ᵐ[P] P[X topTime | F t] :=
      (hmart t topTime t.property.2).symm
    have h := continuous_closed_optional_written P hT F hF hle τ hτ X hm hr
      ((hm topTime).mono (hle topTime) le_rfl) (hi topTime) hc
    refine ⟨integrable_condExp.congr h.symm,?_⟩
    rw [integral_congr_ae h,integral_condExp (show writtenStoppedSpace m F τ hτ ≤ m from fun A hA => hA.1)]
    have h0 := (hmart zeroTime topTime hT).trans hzero
    have h0i := integral_congr_ae h0
    rw [integral_condExp (hle zeroTime)] at h0i
    simpa using h0i
  · intro hz
    exact martingale_of_zero_stopped_means P F hF hle X hm hi (fun τ hτ => (hz τ hτ).2)

end Asakura.FullAudit
