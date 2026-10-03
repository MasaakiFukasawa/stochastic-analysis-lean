import Mathlib.Analysis.ODE.Gronwall

open Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Applying Gronwall after reversing a finite interval gives the estimate
needed for the inverse variational flow; no positive lower bound on K is needed. -/
theorem backward_variational_norm_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f df : ℝ → E) (T K : ℝ) (hT : 0≤T) (hc : Continuous f)
    (hd : ∀ t∈Ioc (0:ℝ) T,HasDerivAt f (df t) t)
    (hb : ∀ t∈Ioc (0:ℝ) T,‖df t‖≤K*‖f t‖) :
    ‖f 0‖≤‖f T‖*Real.exp (K*T) := by
  let g := fun s => f (T-s)
  let dg := fun s => -(df (T-s))
  have hg : Continuous g := hc.comp (continuous_const.sub continuous_id)
  have hgd : ∀ s∈Ico (0:ℝ) T,HasDerivWithinAt g (dg s) (Ici s) s := by
    intro s hs
    have ht : T-s∈Ioc (0:ℝ) T := ⟨by linarith [hs.2],by linarith [hs.1]⟩
    have hh := (hd (T-s) ht).scomp s ((hasDerivAt_id s).const_sub T)
    simpa only [g,dg,Function.comp_def,neg_smul,one_smul] using hh.hasDerivWithinAt
  have hgb : ∀ s∈Ico (0:ℝ) T,‖dg s‖≤K*‖g s‖+(0:ℝ) := by
    intro s hs
    have ht : T-s∈Ioc (0:ℝ) T := ⟨by linarith [hs.2],by linarith [hs.1]⟩
    simpa only [g,dg,norm_neg,add_zero] using hb (T-s) ht
  have hh := norm_le_gronwallBound_of_norm_deriv_right_le hg.continuousOn hgd
    (le_rfl : ‖g 0‖≤‖g 0‖) hgb T ⟨hT,le_rfl⟩
  simpa only [g,sub_zero,sub_self,gronwallBound_ε0] using hh

end Asakura.Chapter12
