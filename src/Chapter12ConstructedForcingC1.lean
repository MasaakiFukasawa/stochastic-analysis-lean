import Chapter12FiniteForcingContDiffOne

open Set
open scoped NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem constructed_forcing_C1 {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : E → E) (D : E → E →L[ℝ] E) (hD : ∀ z,HasFDerivAt b (D z) z)
    (K L : ℝ≥0) (hK : LipschitzWith K D) (hL : 0<L) (hDb : ∀ z,‖D z‖≤(L:ℝ))
    (W : ℝ → E) (hcW : Continuous W) (R : ℝ → F →L[ℝ] E) (hcR : Continuous R)
    (x₀ : E) (T : ℝ) (hT : 0≤T) :
    ∃ (X : F → ℝ → E) (C : ℝ),0≤C ∧
      (∀ z,Continuous (X z)) ∧
      (∀ z t,t∈Icc 0 T → X z t=x₀+(∫ s in 0..t,b (X z s))+W t+R t z) ∧
      (∀ t,t∈Icc 0 T → ContDiff ℝ 1 (fun z => X z t)) ∧
      ∀ z t,t∈Icc 0 T → ‖fderiv ℝ (fun y => X y t) z‖≤C := by
  obtain ⟨X,C,hC,hcX,hX,hLip,hJex⟩ := finite_forcing_flow_first_derivative
    b D hD K L hK hL hDb W hcW R hcR x₀ T hT
  choose J hcJ hJ hdJ hbJ using hJex
  refine ⟨X,C,hC,hcX,hX,?_,?_⟩
  · exact forcing_flow_contDiff_one D hK.continuous L (by exact_mod_cast hL) hDb
      X hcX R hcR J hcJ T C hT hC hLip hJ hdJ
  · intro z t ht
    rw [(hdJ z t ht).fderiv]
    exact hbJ z t ht

end Asakura.Chapter12
