import Chapter10StateMeanContinuity
import Chapter10MeanODEZero

open MeasureTheory Set Filter
open scoped BigOperators NNReal ENNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Centering is derived from the actual state SDE, rather than assumed as a
property of its covariance equation. -/
theorem LinearStateWitness.centered {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (K : ℝ≥0) (hAK : ∀ s,‖A s‖≤K)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (ξ : Ω → Fin d → ℝ) (hξ2 : MemLp ξ 2 P) (hξ0 : ∫ w,ξ w ∂P=0)
    (T : ℝ) (hT : 0≤T)
    (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (h : LinearStateWitness P B A G ξ T hT N X) :
    ∀ r : Icc (0:ℝ) T,(∫ w,X w r ∂P)=0 := by
  let m := fun s => ∫ w,X w (projIcc 0 T hT s) ∂P
  have hm : Continuous m := state_mean_continuous P T hT X h.measurable h.moment
  have hXi s := state_value_integrable P T hT X h.measurable h.moment s
  let hproj (i : Fin d) : (Fin d → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have he : ∀ s∈Icc 0 T,∀ i,m s i=∫ t in 0..s,(A t (m t)) i := by
    intro s hs i
    have hp : projIcc 0 T hT s=⟨s,hs⟩ := Subtype.ext (by simp [projIcc,hs.1,hs.2])
    have hex := h.mean_equation P B A hA K hAK G hG ξ hξ2 T hT N X i ⟨s,hs⟩
    have hxi0 : (∫ w,ξ w i ∂P)=0 := by
      change (∫ w,hproj i (ξ w) ∂P)=0
      rw [(hproj i).integral_comp_comm (hξ2.integrable (by norm_num)),hξ0,map_zero]
    have hmi : m s i=∫ w,X w ⟨s,hs⟩ i ∂P := by
      have hh := (hproj i).integral_comp_comm (hXi s)
      simpa only [hproj,ContinuousLinearMap.proj_apply,hp,m] using hh.symm
    rw [hmi,hex,hxi0,zero_add]
    apply intervalIntegral.integral_congr
    intro t _
    have hh := ((hproj i).comp (A t)).integral_comp_comm (hXi t)
    exact hh
  have hz := homogeneous_mean_equation_zero m hm A hA T K hT (fun s _ => hAK s) he
  intro r
  have hp : projIcc 0 T hT r.val=r := Subtype.ext (by simp [projIcc,r.property.1,r.property.2])
  simpa only [m,hp] using hz r.val r.property

end Asakura.Chapter10
