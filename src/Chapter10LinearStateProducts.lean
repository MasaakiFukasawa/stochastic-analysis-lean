import Chapter10LinearStateWitness
import Chapter10NoiseCovariance
import Chapter10FiniteSDEProduct

open MeasureTheory Set Filter
open scoped BigOperators NNReal ENNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- Construct the state and all coordinate-product local martingales from
the original Brownian system; neither the covariance nor Ito identity is assumed. -/
theorem linear_state_products {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (K : ℝ≥0) (hAK : ∀ t,‖A t‖≤K)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξ2 : MemLp ξ 2 P)
    (T : ℝ) (hT : 0≤T) :
    ∃ (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
      (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
      (Z : Fin d → Fin d → HalfClosedTime → Ω → ℝ),
      LinearStateWitness P B A G ξ T hT N X ∧
      ((fun w => X w ⟨0,le_rfl,hT⟩) =ᵐ[P] ξ) ∧
      (∀ i j,LocalMProcessWitness P B.F (Z i j)) ∧
      ∀ i j (r : Icc (0:ℝ) T),∀ᵐ w ∂P,
        X w r i*X w r j=X w ⟨0,le_rfl,hT⟩ i*X w ⟨0,le_rfl,hT⟩ j+
          (∫ s in 0..r.val,X w (projIcc 0 T hT s) j*(A s (X w (projIcc 0 T hT s))) i)+
          (∫ s in 0..r.val,X w (projIcc 0 T hT s) i*(A s (X w (projIcc 0 T hT s))) j)+
          (∫ s in 0..r.val,∑ k,G i k s*G j k s)+Z i j (realTimeClamp r.val) w := by
  letI : MeasurableSpace Ω := m
  obtain ⟨N,X,hN,hNI,hm,hi,hS⟩ := linear_state_semimartingale P B A hA K hAK G hG ξ hξ hξ2 T hT
  obtain ⟨C,hC,hCe⟩ := deterministic_noise_covariance P B G hG N hN hNI
  let U := fun s w => X w (projIcc 0 T hT s)
  have hp s (hs : s∈Icc (0:ℝ) T) : projIcc 0 T hT s=⟨s,hs⟩ :=
    Subtype.ext (by simp [projIcc,hs.1,hs.2])
  have hc w : Continuous (fun s => U s w) := (X w).continuous.comp continuous_projIcc
  have hs : ∀ t,MeasurableSet[B.F t] {w : Ω | realTimeClamp (T := ⊤) T≤t} := by
    intro t
    by_cases h : realTimeClamp (T := ⊤) T≤t <;> simp [h]
  have hsc i j := (hC i j).stopped P B.F B.mono B.le (fun _ => realTimeClamp T) hs
  have hde i : SemimartingaleDecomposition P B.F
      (fun t w => U (finitePrefixTime T hT t).val w i)
      (fun t w => ξ w i+∫ s in 0..(finitePrefixTime T hT t).val,(A s (U s w)) i)
      (fun t w => ∑ k,N i k (min (realTimeClamp T) t) w) := by
    convert hS i using 1
    funext t w
    simp only [U,hp _ (finitePrefixTime T hT t).property]
  have hprod i j := finite_sde_product P B.F B.mono B.le B.null
    (fun s w => U s w i) (fun s w => U s w j)
    (fun s w => (A s (U s w)) i) (fun s w => (A s (U s w)) j)
    (fun w => ξ w i) (fun w => ξ w j) T hT _ _ _ (hde i) (hde j) (hsc i j)
    (fun w => (continuous_apply i).comp (hA.clm_apply (hc w)))
    (fun w => (continuous_apply j).comp (hA.clm_apply (hc w)))
    (fun s => ∑ k,G i k s*G j k s) (by
      intro r hr
      filter_upwards [hCe i j T hT] with w hw
      change C i j (min (realTimeClamp T) (realTimeClamp r)) w=_
      rw [min_eq_right (real_time_clamp_mono hr.2)]
      exact hw r hr)
  choose Z hZ hZe using hprod
  have hinit : (fun w => X w ⟨0,le_rfl,hT⟩) =ᵐ[P] ξ := by
    filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => (hN i j).initial P B.F))] with w hw
    funext i
    have hh := (hS i).decomposition ⊥ (by change (0:EReal)<⊤; simp) w
    have hp0 : finitePrefixTime (T := (⊤:EReal)) T hT ⊥=⟨0,le_rfl,hT⟩ :=
      Subtype.ext (Asakura.Chapter9.finite_prefix_bot T hT)
    simpa only [hp0,intervalIntegral.integral_same,add_zero,min_bot_right,hw,Pi.zero_apply,Finset.sum_const_zero] using hh
  refine ⟨N,X,Z,⟨hN,hNI,hm,hi,hS⟩,hinit,hZ,?_⟩
  intro i j r
  have hh := hZe i j r.val r.property
  simpa only [U,hp r.val r.property,hp 0 ⟨le_rfl,hT⟩] using hh

end Asakura.Chapter10
