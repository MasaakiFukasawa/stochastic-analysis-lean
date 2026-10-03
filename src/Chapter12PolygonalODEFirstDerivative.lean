import Chapter12PolygonalGridOperator
import Chapter12FiniteForcingFlowC1

open Set
open scoped NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- For the actual finite-grid ODE, the solution is a differentiable
function of the grid values, grows at most linearly in those values, and
has a uniformly bounded first derivative. Higher derivatives are not
asserted by this theorem. -/
theorem polygonal_ode_first_derivative {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (b : E → E) (D : E → E →L[ℝ] E) (hD : ∀ z,HasFDerivAt b (D z) z)
    (K L : ℝ≥0) (hK : LipschitzWith K D) (hL : 0<L) (hDb : ∀ z,‖D z‖≤(L:ℝ))
    (A : G →L[ℝ] E) (x₀ : E) (T h : ℝ) (hT : 0≤T) (n : ℕ) :
    ∃ (X : (Fin (n+1) → G) → ℝ → E) (C M : ℝ),0≤C ∧ 0≤M ∧
      (∀ z,Continuous (X z)) ∧
      (∀ z t,t∈Icc 0 T → X z t=x₀+(∫ s in 0..t,b (X z s))+A (polygonalGridOperator h n t z)) ∧
      (∀ f : ℝ → G,∀ t,t∈Icc 0 T →
        X (fun i => f ((i:ℝ)*h)) t=x₀+
          (∫ s in 0..t,b (X (fun i => f ((i:ℝ)*h)) s))+A (polygonalPath f h n t)) ∧
      (∀ z t,t∈Icc 0 T → ‖X z t‖≤M+C*‖z‖) ∧
      ∀ z t,t∈Icc 0 T → ∃ J : (Fin (n+1) → G) →L[ℝ] E,
        HasFDerivAt (fun y => X y t) J z ∧ ‖J‖≤C := by
  let R := fun t => A.comp (polygonalGridOperator (E := G) h n t)
  have hcR : Continuous R := continuous_const.clm_comp (polygonalGridOperator_continuous h n)
  obtain ⟨X,C,hC,hcX,hX,hLip,hJ⟩ := finite_forcing_flow_first_derivative b D hD K L hK hL hDb
    0 continuous_const R hcR x₀ T hT
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) T)).exists_bound_of_continuousOn (hcX 0).continuousOn
  have hM0 : 0≤M := (norm_nonneg _).trans (hM 0 ⟨le_rfl,hT⟩)
  have hx z t (ht : t∈Icc 0 T) :
      X z t=x₀+(∫ s in 0..t,b (X z s))+A (polygonalGridOperator h n t z) := by
    simpa only [Pi.zero_apply,add_zero,R,ContinuousLinearMap.comp_apply] using hX z t ht
  refine ⟨X,C,M,hC,hM0,hcX,hx,?_,?_,?_⟩
  · intro f t ht
    rw [hx _ t ht,polygonalGridOperator_samples]
  · intro z t ht
    have he : X z t=(X z t-X 0 t)+X 0 t := sub_add_cancel _ _ |>.symm
    have hn := norm_add_le (X z t-X 0 t) (X 0 t)
    rw [← he] at hn
    have hl := hLip z 0 t ht
    simp only [sub_zero] at hl
    linarith [hM t ht]
  · intro z t ht
    obtain ⟨J,_,_,hd,hb⟩ := hJ z
    exact ⟨J t,hd t ht,hb t ht⟩

end Asakura.Chapter12
