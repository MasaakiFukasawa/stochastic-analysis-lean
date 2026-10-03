import FullAuditMartingalePathNorm
import FullAuditStrongMarkovWritten

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2200000

lemma nnreal_stopped_min_measurable
    {Ω : Type*} (F : ℝ≥0 → MeasurableSpace Ω) (hF : Monotone F)
    (τ : Ω → ℝ≥0) (hτ : ∀ t,MeasurableSet[F t] {w | τ w ≤ t}) (t : ℝ≥0) :
    Measurable[F t] (fun w => min (τ w) t) := by
  letI : MeasurableSpace Ω := F t
  apply measurable_of_Iic
  intro r
  by_cases htr : t ≤ r
  · have he : (fun w => min (τ w) t) ⁻¹' Iic r = univ := by
      ext w
      simp only [mem_preimage,mem_Iic,mem_univ,iff_true]
      exact (min_le_right _ _).trans htr
    rw [he]
    exact MeasurableSet.univ
  · have he : (fun w => min (τ w) t) ⁻¹' Iic r = {w | τ w ≤ r} := by ext w; simp [min_le_iff,htr]
    rw [he]
    exact hF (le_of_not_ge htr) _ (hτ r)

/-- Sampling a continuous adapted process at a finite stopping time is
measurable for its stopped sigma algebra. The proof uses measurable
continuous paths and clipped times, with no right-continuity assumption
on the filtration. -/
theorem finite_stopped_sampling
    {Ω : Type*} (m : MeasurableSpace Ω)
    (F : ℝ≥0 → MeasurableSpace Ω) (hF : Monotone F) (hl : ∀ t,F t ≤ m)
    (X : ℝ≥0 → Ω → ℝ) (hm : ∀ t,Measurable[F t] (X t))
    (hc : ∀ w,Continuous (fun t => X t w))
    (τ : Ω → ℝ≥0) (hτ : ∀ t,MeasurableSet[F t] {w | τ w ≤ t}) :
    Measurable[writtenStoppedSpace m F τ hτ] (fun w => X (τ w) w) := by
  let path : Ω → C(ℝ≥0,ℝ) := fun w => ⟨fun t => X t w,hc w⟩
  have hp : Measurable[m] path := ContinuousMap.measurable_iff_eval.mpr (fun t => (hm t).mono (hl t) le_rfl)
  have htm : Measurable[m] τ := measurable_of_Iic fun t => hl t _ (hτ t)
  have ham : Measurable[m] (fun w => X (τ w) w) := continuous_eval.measurable.comp (hp.prodMk htm)
  have hclip t : Measurable[F t] (fun w => X (min (τ w) t) w) := by
    letI : MeasurableSpace Ω := F t
    let pc : Ω → C(ℝ≥0,ℝ) := fun w => ⟨fun s => X (min s t) w,(hc w).comp (continuous_id.min continuous_const)⟩
    have hpc : Measurable[F t] pc := ContinuousMap.measurable_iff_eval.mpr (fun s => (hm (min s t)).mono (hF (min_le_right _ _)) le_rfl)
    have h := continuous_eval.measurable.comp (hpc.prodMk (nnreal_stopped_min_measurable F hF τ hτ t))
    simpa only [pc,ContinuousMap.coe_mk,Function.comp_def,min_assoc,min_self] using h
  intro A hA
  refine ⟨ham hA,fun t => ?_⟩
  have he : (fun w => X (τ w) w) ⁻¹' A ∩ {w | τ w ≤ t} =
      (fun w => X (min (τ w) t) w) ⁻¹' A ∩ {w | τ w ≤ t} := by
    ext w
    simp only [mem_inter_iff,mem_preimage,mem_setOf_eq]
    constructor <;> rintro ⟨ha,ht⟩ <;> simpa only [min_eq_left ht] using And.intro ha ht
  rw [he]
  exact ((hclip t) hA).inter (hτ t)

end Asakura.Chapter7
