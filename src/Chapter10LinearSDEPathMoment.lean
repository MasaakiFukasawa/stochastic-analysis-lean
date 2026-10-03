import Chapter10LinearSDEConstruction
import Chapter10VectorNoisePath
import Chapter10LinearPathMoment

open MeasureTheory Set
open scoped BigOperators NNReal ENNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The constructed linear SDE with a square-integrable random initial value
has a square-integrable path supremum on a finite interval. -/
theorem linear_sde_path_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (K : ℝ≥0) (hAK : ∀ t,‖A t‖≤K)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (ξ : Ω → Fin d → ℝ) (hξm : Measurable ξ) (hξ : MemLp ξ 2 P)
    (T : ℝ) (hT : 0≤T) :
    ∃ (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
      (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ)),
      (∀ i j,LocalMProcessWitness P B.F (N i j)) ∧
      (∀ i j,ItoCovarianceFormula P B.F (B.W j) (fun z => G i j z.2) (N i j)) ∧
      Measurable X ∧ MemLp X 2 P ∧
      ∀ w t,X w t=ξ w+(∫ s in 0..t.val,A s (X w (projIcc 0 T hT s)))+
        (fun i => ∑ j,N i j (realTimeClamp t.val) w) := by
  obtain ⟨N,U,hN,hNI,hm,hc,he⟩ := time_dependent_linear_sde_family P B A hA G hG T hT
  obtain ⟨W,hWm,hWi,hWe⟩ := deterministic_vector_noise_path P B G hG N hN hNI T hT
  let X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ) := fun w =>
    ⟨fun t => U (ξ w) t.val w,(hc (ξ w) w).comp continuous_subtype_val⟩
  have hXm : Measurable X := ContinuousMap.measurable_iff_eval.mpr
    (fun t => (hm t.val).comp (hξm.prodMk measurable_id))
  have heq w (t : Icc (0:ℝ) T) : X w t=ξ w+
      (∫ s in 0..t.val,A s (X w (projIcc 0 T hT s)))+W w t := by
    have hWe' : W w t=(fun i => ∑ j,N i j (realTimeClamp t.val) w) := funext (hWe w t)
    change U (ξ w) t.val w=_
    rw [he (ξ w) w t.val t.property, hWe']
    congr 2
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s∈Icc 0 T := by
      rw [uIcc_of_le t.property.1] at hs
      exact ⟨hs.1,hs.2.trans t.property.2⟩
    have hp : (projIcc 0 T hT s).val=s := by simp [projIcc,hs'.1,hs'.2]
    simp only [X,ContinuousMap.coe_mk,hp]
  have hXi := linear_forced_path_memLp P T hT K A hA hAK ξ hξ W X hWi hXm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun w => heq w))
  refine ⟨N,X,hN,hNI,hXm,hXi,?_⟩
  intro w t
  rw [heq]
  congr 1
  exact funext (hWe w t)

end Asakura.Chapter10
