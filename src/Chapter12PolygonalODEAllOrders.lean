import Chapter12FiniteForcingAllOrders
import Chapter12PathEvaluationDerivatives
import Chapter12PolygonalGridOperator

open MeasureTheory Set
open scoped Topology ContDiff NNReal
namespace Asakura.Chapter12
universe u
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem polygonal_ode_all_orders {E G : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (A : G →L[ℝ] E) (x₀ : E) (T h : ℝ) (hT : 0≤T) (n : ℕ) :
    ∃X : (Fin (n+1) → G) → C(Icc (0:ℝ) T,E),ContDiff ℝ ∞ X ∧
      (∀z t,X z t=x₀+A (polygonalGridOperator h n t.val z)+
        ∫s in 0..t.val,b (X z (projIcc 0 T hT s))) ∧
      (∀f : ℝ → G,∀t,X (fun i => f ((i:ℝ)*h)) t=x₀+A (polygonalPath f h n t.val)+
        ∫s in 0..t.val,b (X (fun i => f ((i:ℝ)*h)) (projIcc 0 T hT s))) ∧
      (∃C M : ℝ,0≤C ∧ 0≤M ∧ ∀z t,‖X z t‖≤M+C*‖z‖) ∧
      ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀z t,‖iteratedFDeriv ℝ k (fun y => X y t) z‖≤C := by
  let R : C(Icc (0:ℝ) T,(Fin (n+1) → G) →L[ℝ] E) :=
    ⟨fun t => A.comp (polygonalGridOperator h n t.val),
      continuous_const.clm_comp ((polygonalGridOperator_continuous h n).comp continuous_subtype_val)⟩
  obtain ⟨X,hX,heq,hbX⟩ := finite_forcing_all_orders b hb hbound T hT (ContinuousMap.const _ x₀) R
  refine ⟨X,hX,heq,?_,?_,?_⟩
  · intro f t
    simpa only [R,ContinuousMap.const_apply,ContinuousMap.coe_mk,ContinuousLinearMap.comp_apply,polygonalGridOperator_samples] using heq (fun i => f ((i:ℝ)*h)) t
  · obtain ⟨C,hC,hCX⟩ := hbX 1 le_rfl
    have hLip : LipschitzWith ⟨C,hC⟩ X := by
      apply lipschitzWith_of_nnnorm_fderiv_le (hX.differentiable (by simp))
      intro z
      have hh : ‖fderiv ℝ X z‖≤C := by simpa only [norm_iteratedFDeriv_one] using hCX z
      exact_mod_cast hh
    refine ⟨C,‖X 0‖,hC,norm_nonneg _,?_⟩
    intro z t
    have hh := hLip.norm_sub_le z 0
    change ‖X z-X 0‖≤C*‖z-0‖ at hh
    rw [sub_zero] at hh
    have hn := norm_add_le (X z-X 0) (X 0)
    rw [sub_add_cancel] at hn
    exact ((X z).norm_coe_le_norm t).trans (hn.trans (by linarith))
  · intro k hk
    obtain ⟨C,hC,hbC⟩ := hbX k hk
    exact ⟨C,hC,fun z t => path_evaluation_derivative_bound X hX k C hC hbC z t⟩
end Asakura.Chapter12
#print axioms Asakura.Chapter12.polygonal_ode_all_orders
