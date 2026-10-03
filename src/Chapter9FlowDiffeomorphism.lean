import Chapter9FlowReversal

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Solving the forward and reversed equations constructs a global
homeomorphism whose two directions are differentiable. -/
theorem time_dependent_flow_diffeomorphism {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (b : ℝ → E → E) (D : ℝ → E → E →L[ℝ] E)
    (hb : Continuous b.uncurry) (hcD : Continuous D.uncurry)
    (hD : ∀ t z,HasFDerivAt (b t) (D t z) z)
    (K : ℝ≥0) (hK : ∀ t,LipschitzWith K (b t))
    (T : ℝ) (hT : 0≤T) :
    ∃ e : E ≃ₜ E, Differentiable ℝ e ∧ Differentiable ℝ e.symm ∧
      ∀ x,∃ X : ℝ → E,Continuous X ∧ X T=e x ∧
        (∀ s∈Icc 0 T,X s=x+∫ r in 0..s,b r (X r)) ∧
        ∃ J : ℝ → E →L[ℝ] E,Continuous J ∧
          (∀ t∈Icc 0 T,∀ h,J t h=h+∫ r in 0..t,D r (X r) (J r h)) ∧
          HasFDerivAt e (J T) x := by
  obtain ⟨X,hcX,hX,hJX⟩ := time_dependent_flow_c1_exists b D hb hcD hD K hK T hT
  let c := fun s y => -b (T-s) y
  let D' := fun s y => -D (T-s) y
  have hc : Continuous c.uncurry := (hb.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)).neg
  have hDc : Continuous D'.uncurry := (hcD.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)).neg
  have hDc' s y : HasFDerivAt (c s) (D' s y) y := (hD (T-s) y).neg
  obtain ⟨Y,hcY,hY,hJY⟩ := time_dependent_flow_c1_exists c D' hc hDc hDc'
    K (fun s => (hK (T-s)).neg) T hT
  have hdX : Differentiable ℝ (fun x => X x T) := by
    intro x
    obtain ⟨J,_,_,hJ⟩ := hJX x
    exact (hJ T ⟨hT,le_rfl⟩).differentiableAt
  have hdY : Differentiable ℝ (fun x => Y x T) := by
    intro x
    obtain ⟨J,_,_,hJ⟩ := hJY x
    exact (hJ T ⟨hT,le_rfl⟩).differentiableAt
  obtain ⟨hl,hr⟩ := integral_flow_inverse b hb K hK X Y hcX hcY T hT hX hY
  let e : E ≃ₜ E := {
    toEquiv := { toFun := fun x => X x T
                 invFun := fun y => Y y T
                 left_inv := hl
                 right_inv := hr }
    continuous_toFun := hdX.continuous
    continuous_invFun := hdY.continuous }
  refine ⟨e,hdX,hdY,?_⟩
  intro x
  obtain ⟨J,hcJ,hJ,hdJ⟩ := hJX x
  exact ⟨X x,hcX x,rfl,hX x,J,hcJ,hJ,hdJ T ⟨hT,le_rfl⟩⟩
end Asakura.Chapter9
