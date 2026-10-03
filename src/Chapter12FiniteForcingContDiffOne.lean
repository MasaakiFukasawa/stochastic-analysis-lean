import Chapter12FiniteForcingFlowC1
import Chapter12ForcingVariationContinuity
import Mathlib.Analysis.Calculus.ContDiff.Defs

open Set
open scoped NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

/-- The first forcing derivative varies continuously in its parameter.
Consequently each fixed-time solution is genuinely C1. -/
theorem forcing_flow_contDiff_one {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : E → E →L[ℝ] E) (hcD : Continuous D) (L : ℝ) (hL : 0<L) (hDb : ∀ z,‖D z‖≤L)
    (X : F → ℝ → E) (hcX : ∀ z,Continuous (X z))
    (R : ℝ → F →L[ℝ] E) (hcR : Continuous R)
    (J : F → ℝ → F →L[ℝ] E) (hcJ : ∀ z,Continuous (J z))
    (T C : ℝ) (hT : 0≤T) (hC : 0≤C)
    (hLip : ∀ z y t,t∈Icc 0 T → ‖X z t-X y t‖≤C*‖z-y‖)
    (hJ : ∀ z t,t∈Icc 0 T → ∀ h,J z t h=R t h+∫ s in 0..t,D (X z s) (J z s h))
    (hdJ : ∀ z t,t∈Icc 0 T → HasFDerivAt (fun y => X y t) (J z t) z) :
    ∀ t,t∈Icc 0 T → ContDiff ℝ 1 (fun z => X z t) := by
  let S : F → C(Icc (0:ℝ) T,E) := fun z =>
    ⟨fun t => X z t.val,(hcX z).comp continuous_subtype_val⟩
  let JP : F → C(Icc (0:ℝ) T,F →L[ℝ] E) := fun z =>
    ⟨fun t => J z t.val,(hcJ z).comp continuous_subtype_val⟩
  let RP : C(Icc (0:ℝ) T,F →L[ℝ] E) :=
    ⟨fun t => R t.val,hcR.comp continuous_subtype_val⟩
  have hp (s : ℝ) (hs : s∈Icc 0 T) : (projIcc 0 T hT s).val=s := by
    simp [projIcc,hs.1,hs.2]
  have hSc : Continuous S := by
    have hh : LipschitzWith ⟨C,hC⟩ S := by
      apply LipschitzWith.of_dist_le_mul
      intro z y
      change dist (S z) (S y)≤C*dist z y
      rw [dist_eq_norm,dist_eq_norm]
      apply (ContinuousMap.norm_le _ (mul_nonneg hC (norm_nonneg _))).mpr
      intro t
      exact hLip z y t.val t.property
    exact hh.continuous
  have hJPc : Continuous JP := by
    apply forcing_variation_parameter_continuous T hT L hL D hcD hDb S JP RP hSc
    intro z t
    apply ContinuousLinearMap.ext
    intro v
    change J z t.val v=R t.val v+(∫ s in 0..t.val,
      (D (S z (projIcc 0 T hT s))).comp (JP z (projIcc 0 T hT s))) v
    rw [hJ z t.val t.property v,ContinuousLinearMap.intervalIntegral_apply
      (φ := fun s => (D (S z (projIcc 0 T hT s))).comp (JP z (projIcc 0 T hT s)))
      (((hcD.comp ((S z).continuous.comp continuous_projIcc)).clm_comp
        ((JP z).continuous.comp continuous_projIcc)).intervalIntegrable 0 t.val)]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s∈Icc 0 t.val := by simpa only [uIcc_of_le t.property.1] using hs
    simp only [S,JP,ContinuousMap.coe_mk,hp s ⟨hs'.1,hs'.2.trans t.property.2⟩,
      ContinuousLinearMap.comp_apply]
  intro t ht
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun z => J z t,?_,fun z => hdJ z t ht⟩
  exact (continuous_eval_const (⟨t,ht⟩ : Icc (0:ℝ) T)).comp hJPc

end Asakura.Chapter12
