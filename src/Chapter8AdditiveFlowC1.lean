import Chapter8ForcedInitialStability
import Chapter8VariationalConstruction
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Construct the additive-noise solution family and its first initial-
state derivative from the drift assumptions and a continuous forcing path.
No differentiability or variational process is supplied as input. -/
theorem additive_flow_first_derivative_exists {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : E → E) (D : E → E →L[ℝ] E) (hD : ∀ z,HasFDerivAt b (D z) z)
    (K L : ℝ≥0) (hK : LipschitzWith K D) (hL : 0<L) (hDb : ∀ z,‖D z‖ ≤ (L:ℝ))
    (W : ℝ → E) (hW : Continuous W) (T : ℝ) (hT : 0 ≤ T) :
    ∃ X : E → ℝ → E,
      (∀ x,Continuous (X x)) ∧
      (∀ x t,t∈Icc 0 T → X x t=x+(∫ s in 0..t,b (X x s))+W t) ∧
      (∀ x y t,t∈Icc 0 T → ‖X x t-X y t‖ ≤ Real.exp (((L:ℝ)+1)*T)*‖x-y‖) ∧
      ∀ x,∃ J : ℝ → E →L[ℝ] E,Continuous J ∧
        (∀ t,t∈Icc 0 T → ∀ h,J t h=h+∫ s in 0..t,D (X x s) (J s h)) ∧
        ∀ t,t∈Icc 0 T → HasFDerivAt (fun z => X z t) (J t) x := by
  have hLb : LipschitzWith L b := by
    apply lipschitzWith_of_nnnorm_fderiv_le (fun z => (hD z).differentiableAt)
    intro z
    rw [(hD z).fderiv]
    exact_mod_cast hDb z
  have hex x := forced_integral_equation_exists T hT L (fun _ z => b z)
    (hLb.continuous.comp continuous_snd) (fun _ => hLb) (fun t => x+W t) (continuous_const.add hW)
  choose X hcX hXe using hex
  have hX x t (ht : t∈Icc 0 T) : X x t=x+(∫ s in 0..t,b (X x s))+W t := by
    rw [hXe x t ht]
    abel
  have hLip x y := forced_initial_stability b L hLb (X x) (X y) W (hcX x) (hcX y) x y T hT (hX x) (hX y)
  refine ⟨X,hcX,hX,hLip,?_⟩
  intro x
  apply flow_first_derivative_constructed b D hD K L hK hL hDb X W hcX x T
    (Real.exp (((L:ℝ)+1)*T)) hT (Real.exp_pos _).le hX
  intro h t ht
  simpa only [add_sub_cancel_left] using hLip (x+h) x t ht

end Asakura.Chapter8
