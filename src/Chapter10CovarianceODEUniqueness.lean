import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic.NoncommRing

open Set
namespace Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false

/-- Uniqueness for the two-sided linear equation satisfied by S and the actual
error covariance V. The coefficient bound is only needed on the finite interval. -/
theorem covariance_ode_unique {E : Type*} [NormedRing E] [NormedAlgebra ℝ E]
    (V S a b q : ℝ → E) (T C : ℝ)
    (hV : ContinuousOn V (Icc 0 T)) (hS : ContinuousOn S (Icc 0 T))
    (hdV : ∀ t∈Ico 0 T,HasDerivWithinAt V (a t*V t+V t*b t+q t) (Ici t) t)
    (hdS : ∀ t∈Ico 0 T,HasDerivWithinAt S (a t*S t+S t*b t+q t) (Ici t) t)
    (ha : ∀ t∈Ico 0 T,‖a t‖≤C) (hb : ∀ t∈Ico 0 T,‖b t‖≤C)
    (hzero : V 0=S 0) : ∀ t∈Icc 0 T,V t=S t := by
  have he := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := fun t => V t-S t)
    (f' := fun t => a t*V t+V t*b t+q t-(a t*S t+S t*b t+q t))
    (K := 2*C) (a := 0) (b := T) (hV.sub hS)
    (fun t ht => (hdV t ht).sub (hdS t ht))
    (sub_eq_zero.mpr hzero) (by
      intro t ht
      have hid : a t*V t+V t*b t+q t-(a t*S t+S t*b t+q t)=
          a t*(V t-S t)+(V t-S t)*b t := by noncomm_ring
      rw [hid]
      calc
        _ ≤ ‖a t*(V t-S t)‖+‖(V t-S t)*b t‖ := norm_add_le _ _
        _ ≤ ‖a t‖*‖V t-S t‖+‖V t-S t‖*‖b t‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ C*‖V t-S t‖+‖V t-S t‖*C := add_le_add
          (mul_le_mul_of_nonneg_right (ha t ht) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (hb t ht) (norm_nonneg _))
        _ = 2*C*‖V t-S t‖ := by ring)
  exact fun t ht => sub_eq_zero.mp (he t ht)

end Asakura.Chapter10
