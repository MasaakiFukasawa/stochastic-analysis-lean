import Chapter6DensityLowerBound
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter6
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The uniform conditional bound passes to the L1 limit, using integral
inequalities directly and without selecting an almost-sure subsequence. -/
theorem conditional_bound_L1_limit {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω)
    (S : ℕ → Ω → ℝ) (Z K : Ω → ℝ)
    (hS : ∀ n,Integrable (S n) P) (hZ : Integrable Z P) (hK : Integrable K P)
    (hb : ∀ n,∀ᵐ w ∂P,|P[S n|G] w|≤K w)
    (hl : Tendsto (fun n => ∫ w,‖Z w-S n w‖ ∂P) atTop (𝓝 0)) :
    ∀ᵐ w ∂P,|P[Z|G] w|≤K w := by
  let F := fun w => max (|P[Z|G] w|-K w) 0
  have hposint : Integrable (fun w => ((|P[Z|G] w|-K w)+|(|P[Z|G] w|-K w)|)/2) P :=
    (((integrable_condExp (μ := P) (m := G) (f := Z)).abs.sub hK).add
      ((integrable_condExp (μ := P) (m := G) (f := Z)).abs.sub hK).abs).div_const 2
  have hFi : Integrable F P := by
    convert hposint using 1
    funext w
    dsimp [F]
    by_cases hh : 0≤|P[Z|G] w|-K w
    · rw [abs_of_nonneg hh,max_eq_left hh]; ring
    · rw [abs_of_neg (lt_of_not_ge hh),max_eq_right (le_of_not_ge hh)]; ring
  have hFn w : 0≤F w := le_max_right _ _
  have hbound n : (∫ w,F w ∂P)≤∫ w,‖Z w-S n w‖ ∂P := by
    have hd := condExp_sub hZ (hS n) G
    have hle : ∀ᵐ w ∂P,F w≤‖P[(fun w => Z w-S n w)|G] w‖ := by
      filter_upwards [hd,hb n] with w hd hb
      change P[(fun w => Z w-S n w)|G] w=P[Z|G] w-P[S n|G] w at hd
      rw [hd,Real.norm_eq_abs]
      apply max_le _ (abs_nonneg _)
      have hh := abs_add_le (P[Z|G] w-P[S n|G] w) (P[S n|G] w)
      rw [sub_add_cancel] at hh
      linarith
    exact (integral_mono_ae hFi (integrable_condExp.norm) hle).trans (integral_norm_condExp_le _)
  have hzero : (∫ w,F w ∂P)=0 := le_antisymm (ge_of_tendsto hl (Eventually.of_forall hbound)) (integral_nonneg hFn)
  have hae := (integral_eq_zero_iff_of_nonneg hFn hFi).mp hzero
  filter_upwards [hae] with w hw
  have hh : |P[Z|G] w|-K w≤0 := (le_max_left _ _).trans_eq hw
  linarith

end Asakura.Chapter6
