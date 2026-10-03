import Chapter8ForcedIntegralExistence
import FullAuditChapter4Gronwall

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter9
open Asakura.FullAudit
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false

/-- An initial-state estimate for a genuinely time-dependent drift.
The forcing cancels, so its differentiability is never used. -/
theorem time_dependent_initial_stability {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (b : ℝ → E → E) (K : ℝ≥0) (hbc : Continuous b.uncurry) (hb : ∀ t,LipschitzWith K (b t))
    (X Y W : ℝ → E) (hcX : Continuous X) (hcY : Continuous Y)
    (x y : E) (T : ℝ) (hT : 0 ≤ T)
    (hX : ∀ t,t∈Icc 0 T → X t=x+(∫ s in 0..t,b s (X s))+W t)
    (hY : ∀ t,t∈Icc 0 T → Y t=y+(∫ s in 0..t,b s (Y s))+W t) :
    ∀ t,t∈Icc 0 T → ‖X t-Y t‖ ≤ Real.exp (((K:ℝ)+1)*T)*‖x-y‖ := by
  have hc : Continuous (fun t => ‖X t-Y t‖) := (hcX.sub hcY).norm
  have hineq t (ht : t∈Icc 0 T) :
      ‖X t-Y t‖ ≤ ‖x-y‖+((K:ℝ)+1)*(∫ s in 0..t,‖X s-Y s‖) := by
    have he : X t-Y t=(x-y)+∫ s in 0..t,b s (X s)-b s (Y s) := by
      rw [hX t ht,hY t ht,intervalIntegral.integral_sub (f := fun s => b s (X s)) (g := fun s => b s (Y s))
        ((hbc.comp (continuous_id.prodMk hcX)).intervalIntegrable 0 t) ((hbc.comp (continuous_id.prodMk hcY)).intervalIntegrable 0 t)]
      abel
    rw [he]
    have hh := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := (0:ℝ)) (b := t)
      (f := fun s => b s (X s)-b s (Y s)) (g := fun s => (K:ℝ)*‖X s-Y s‖) ht.1
      (ae_of_all _ (fun s _ => (hb s).norm_sub_le (X s) (Y s))) ((hc.const_mul K).intervalIntegrable 0 t)
    rw [intervalIntegral.integral_const_mul] at hh
    have hn : 0 ≤ ∫ s in 0..t,‖X s-Y s‖ := intervalIntegral.integral_nonneg ht.1 (fun s _ => norm_nonneg _)
    exact (norm_add_le _ _).trans (add_le_add le_rfl (hh.trans (by nlinarith)))
  have hh := ch4_gronwall_written (fun t => ‖X t-Y t‖) ‖x-y‖ ((K:ℝ)+1) T hT
    hc.continuousOn (by positivity) hineq
  intro t ht
  have he : Real.exp (((K:ℝ)+1)*t) ≤ Real.exp (((K:ℝ)+1)*T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (by positivity))
  exact (hh t ht).trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left he (norm_nonneg (x-y)))

end Asakura.Chapter9
