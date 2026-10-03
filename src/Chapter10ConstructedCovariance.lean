import Chapter10LinearDriftFubini

open MeasureTheory Set Filter
open scoped BigOperators NNReal ENNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- Covariance integral equation from the actual Brownian-driven construction.
The SDE, product formula, martingale and Fubini steps are all discharged. -/
theorem constructed_covariance_equation {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (K : ℝ≥0) (hAK : ∀ t,‖A t‖≤K)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξ2 : MemLp ξ 2 P)
    (T : ℝ) (hT : 0≤T) :
    ∃ (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
      (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ)),LinearStateWitness P B A G ξ T hT N X ∧
      ((fun w => X w ⟨0,le_rfl,hT⟩) =ᵐ[P] ξ) ∧
      ∀ i j (r : Icc (0:ℝ) T),
        (∫ w,X w r i*X w r j ∂P)=(∫ w,ξ w i*ξ w j ∂P)+
          (∫ s in 0..r.val,∫ w,X w (projIcc 0 T hT s) j*(A s (X w (projIcc 0 T hT s))) i ∂P)+
          (∫ s in 0..r.val,∫ w,X w (projIcc 0 T hT s) i*(A s (X w (projIcc 0 T hT s))) j ∂P)+
          (∫ s in 0..r.val,∑ k,G i k s*G j k s) := by
  letI : MeasurableSpace Ω := m
  obtain ⟨N,X,Z,hState,hinit,hZ,he⟩ := linear_state_products P B A hA K hAK G hG ξ hξ hξ2 T hT
  have hm := hState.measurable
  have hX := hState.moment
  have hmom (r : Icc (0:ℝ) T) i : MemLp (fun w => X w r i) 2 P := by
    apply hX.norm.of_le ((measurable_pi_apply i).comp ((continuous_eval_const r).measurable.comp hm)).aestronglyMeasurable
    exact ae_of_all _ fun w => by
      simpa only [norm_norm,Function.comp_apply] using (norm_le_pi_norm (X w r) i).trans ((X w).norm_coe_le_norm r)
  refine ⟨N,X,hState,hinit,?_⟩
  intro i j r
  have hq : Continuous (fun s => ∑ k,G i k s*G j k s) :=
    continuous_finsetSum _ (fun k _ => (hG i k).mul (hG j k))
  have hz := linear_product_mean_zero P B.F B.mono B.le T hT X hX A hA K hAK i j _ hq
    (Z i j) (hZ i j) (he i j) r.val r.property
  obtain ⟨hi,hfi⟩ := linear_drift_fubini P T hT X hm hX A hA K hAK i j r.val r.property.1
  obtain ⟨hj,hfj⟩ := linear_drift_fubini P T hT X hm hX A hA K hAK j i r.val r.property.1
  let f := fun w => X w ⟨0,le_rfl,hT⟩ i*X w ⟨0,le_rfl,hT⟩ j
  let g := fun w => ∫ s in 0..r.val,X w (projIcc 0 T hT s) j*(A s (X w (projIcc 0 T hT s))) i
  let h := fun w => ∫ s in 0..r.val,X w (projIcc 0 T hT s) i*(A s (X w (projIcc 0 T hT s))) j
  let c := ∫ s in 0..r.val,∑ k,G i k s*G j k s
  have hf : Integrable f P := (hmom ⟨0,le_rfl,hT⟩ i).integrable_mul (hmom ⟨0,le_rfl,hT⟩ j)
  have hc : Integrable (fun _ : Ω => c) P := integrable_const _
  have hxi : (∫ w,f w ∂P)=∫ w,ξ w i*ξ w j ∂P :=
    integral_congr_ae (hinit.mono (fun w hw => by
      change X w ⟨0,le_rfl,hT⟩=ξ w at hw
      change X w ⟨0,le_rfl,hT⟩ i*X w ⟨0,le_rfl,hT⟩ j=ξ w i*ξ w j
      rw [hw]))
  have hh : (∫ w,X w r i*X w r j ∂P)=(∫ w,f w ∂P)+(∫ w,g w ∂P)+(∫ w,h w ∂P)+c := by
    rw [integral_congr_ae (he i j r)]
    change (∫ w,f w+g w+h w+c+Z i j (realTimeClamp r.val) w ∂P)=_
    rw [integral_add (show Integrable (fun w => f w+g w+h w+c) P from ((hf.add hi).add hj).add hc) hz.1,
      integral_add (show Integrable (fun w => f w+g w+h w) P from (hf.add hi).add hj) hc,
      integral_add (show Integrable (fun w => f w+g w) P from hf.add hi) hj,
      integral_add hf hi,hz.2,add_zero]
    simp [g,h]
  rw [hh,hxi,hfi,hfj]

end Asakura.Chapter10
