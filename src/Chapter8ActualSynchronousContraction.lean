import Chapter8SDERandomAdditiveEquation
import Chapter8BrownianForcingPath
import FullAuditLangevinContraction

open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The synchronous contraction for two actual SDE solutions, allowing
random initial values, holds simultaneously at all nonnegative times. -/
theorem actual_synchronous_contraction {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (e : (Fin d → ℝ) ≃L[ℝ] E) (g : (Fin d → ℝ) → (Fin d → ℝ)) (hg : Continuous g)
    (σ : Fin d → Fin n → ℝ) (κ : ℝ)
    (hmono : ∀ x y,κ*‖e x-e y‖^2≤⟪e x-e y,e (g x)-e (g y)⟫)
    (ξ ζ : Ω → Fin d → ℝ)
    (X Y : HalfClosedTime → Ω → Fin d → ℝ)
    (hX : VectorSDESolution P B.F B.W (fun i x => -(g x i)) (fun i j _ => σ i j) ξ X)
    (hY : VectorSDESolution P B.F B.W (fun i x => -(g x i)) (fun i j _ => σ i j) ζ Y) :
    ∀ᵐ w ∂P,∀ t : ℝ,0≤t →
      ‖e (X (realTimeClamp t) w)-e (Y (realTimeClamp t) w)‖≤
        Real.exp (-κ*t)*‖e (ξ w)-e (ζ w)‖ := by
  have hXc w : Continuous (fun r => X (realTimeClamp r) w) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (hX.path w _ (half_real_time_finite r)).comp real_time_clamp_continuous.continuousAt
  have hYc w : Continuous (fun r => Y (realTimeClamp r) w) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (hY.path w _ (half_real_time_finite r)).comp real_time_clamp_continuous.continuousAt
  have hzero : realTimeClamp (T := ⊤) 0=⊥ := by
    apply Subtype.ext
    rw [real_time_clamp_eq 0 le_rfl (by simp)]
    rfl
  have hX0 := hX.initial_value P (EReal.coe_lt_top 0) B.F B.W _ _ ξ X
  have hY0 := hY.initial_value P (EReal.coe_lt_top 0) B.F B.W _ _ ζ Y
  filter_upwards [sde_random_additive_equation P B (fun i x => -(g x i)) σ ξ X hX,
    sde_random_additive_equation P B (fun i x => -(g x i)) σ ζ Y hY,hX0,hY0] with w hx hy hx0 hy0
  let W := fun r i => ∑ j,σ i j*B.W j (realTimeClamp r) w
  have assemble (Z : ℝ → Fin d → ℝ) (z : Fin d → ℝ) (hc : Continuous Z)
      (hz : ∀ r : ℝ,0≤r → ∀ i,Z r i=z i+(∫ s in 0..r,-(g (Z s) i))+W r i) :
      ∀ r : ℝ,0≤r → Z r=z-(∫ s in 0..r,g (Z s))+W r := by
    intro r hr
    ext i
    have hi := (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).intervalIntegral_comp_comm
      ((hg.comp hc).intervalIntegrable 0 r (μ := volume))
    change (∫ s in 0..r,g (Z s) i)=(∫ s in 0..r,g (Z s)) i at hi
    change Z r i=z i-(∫ s in 0..r,g (Z s)) i+W r i
    rw [hz r hr i,intervalIntegral.integral_neg,hi]
    rfl
  have hxI := assemble (fun r => X (realTimeClamp r) w) (ξ w) (hXc w) hx
  have hyI := assemble (fun r => Y (realTimeClamp r) w) (ζ w) (hYc w) hy
  let G := fun y : E => e (g (e.symm y))
  have hG a b : κ*‖a-b‖^2≤⟪a-b,G a-G b⟫ := by
    simpa only [G,e.apply_symm_apply] using hmono (e.symm a) (e.symm b)
  intro t ht
  have hd := langevin_common_noise_difference (fun r => X (realTimeClamp r) w)
    (fun r => Y (realTimeClamp r) w) W g (ξ w) (ζ w) t (hXc w) (hYc w) hg
    (fun r hr => hxI r hr.1) (fun r hr => hyI r hr.1)
  have hdE r (hr : r∈Ioo 0 t) : HasDerivAt
      (fun s => e (X (realTimeClamp s) w)-e (Y (realTimeClamp s) w))
      (-(G (e (X (realTimeClamp r) w))-G (e (Y (realTimeClamp r) w)))) r := by
    simpa only [G,e.symm_apply_apply,Function.comp_def,map_sub,map_neg,ContinuousLinearEquiv.coe_coe] using
      e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt r (hd r hr)
  have hh := langevin_path_contraction (fun r => e (X (realTimeClamp r) w))
    (fun r => e (Y (realTimeClamp r) w)) G κ t ht
    (e.continuous.comp (hXc w)).continuousOn (e.continuous.comp (hYc w)).continuousOn hG hdE t ⟨ht,le_rfl⟩
  simpa only [hzero,hx0,hy0] using hh

end Asakura.Chapter8
