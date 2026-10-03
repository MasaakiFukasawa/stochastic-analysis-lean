import Chapter10LinearSDEPathMoment
import Chapter10FlowAdapted

open MeasureTheory Set
open scoped BigOperators NNReal ENNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- Construct an adapted L2 linear state path from the original Brownian driver
and an initial random variable, retaining the actual Ito-integral witnesses. -/
theorem adapted_linear_state {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (K : ℝ≥0) (hAK : ∀ t,‖A t‖≤K)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξ2 : MemLp ξ 2 P)
    (T : ℝ) (hT : 0≤T) :
    ∃ (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
      (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ)),
      (∀ i j,LocalMProcessWitness P B.F (N i j)) ∧
      (∀ i j,ItoCovarianceFormula P B.F (B.W j) (fun z => G i j z.2) (N i j)) ∧
      Measurable X ∧ MemLp X 2 P ∧
      (∀ t,Measurable[B.F (realTimeClamp t.val)] (fun w => X w t)) ∧
      ∀ w t,X w t=ξ w+(∫ s in 0..t.val,A s (X w (projIcc 0 T hT s)))+
        (fun i => ∑ j,N i j (realTimeClamp t.val) w) := by
  letI : MeasurableSpace Ω := m
  obtain ⟨N,X,hN,hNI,hm,hi,he⟩ := linear_sde_path_moment P B A hA K hAK G hG ξ
    (hξ.mono (B.le _) le_rfl) hξ2 T hT
  let U := fun s w => X w (projIcc 0 T hT s)
  let W := fun s w i => ∑ j,N i j (realTimeClamp s) w
  have hWc w : Continuous (fun s => W s w) := by
    apply continuous_pi
    intro i
    apply continuous_finsetSum
    intro j _
    apply continuous_iff_continuousAt.mpr
    intro s
    exact ((hN i j).path P B.F w _ (half_real_time_finite s)).comp real_time_clamp_continuous.continuousAt
  have hWm s : Measurable[B.F (realTimeClamp s)] (W s) := by
    letI : MeasurableSpace Ω := B.F (realTimeClamp s)
    exact Measurable.of_eval (fun i => Finset.measurable_sum _
      (fun j _ => (hN i j).adapted P B.F _ (half_real_time_finite s)))
  have hzero : realTimeClamp (T := ⊤) 0=⊥ := by
    apply Subtype.ext
    exact real_time_clamp_eq 0 le_rfl le_top
  have hξ0 : Measurable[B.F (realTimeClamp (T := ⊤) 0)] ξ := by
    rw [hzero]
    exact hξ
  have hlip s : LipschitzWith K (A s) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,dist_eq_norm,←map_sub]
    exact ((A s).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hAK s) (norm_nonneg _))
  have hUa := time_dependent_flow_adapted (m := m) (fun s => B.F (realTimeClamp s))
    (B.mono.comp real_time_clamp_mono) (fun s x => A s x) K
    (hA.comp continuous_fst |>.clm_apply continuous_snd) hlip ξ hξ0 U W
    (fun w => (X w).continuous.comp continuous_projIcc) hWc T (fun s _ => hWm s) (by
      intro w s hs
      have hp : projIcc 0 T hT s=⟨s,hs⟩ := Subtype.ext (by simp [projIcc,hs.1,hs.2])
      simpa only [U,W,hp] using he w ⟨s,hs⟩)
  refine ⟨N,X,hN,hNI,hm,hi,?_,he⟩
  intro t
  have hp : projIcc 0 T hT t.val=t := Subtype.ext (by simp [projIcc,t.property.1,t.property.2])
  simpa only [U,hp] using hUa t.val t.property

end Asakura.Chapter10
