import Chapter12ForcingParameterDerivative
import Chapter8ForcedIntegralExistence

open Set
open scoped NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem forcing_variational_operator_exists {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ℝ) (hT : 0≤T) (D : ℝ → E →L[ℝ] E) (hcD : Continuous D)
    (L : ℝ≥0) (hb : ∀ t,‖D t‖≤(L:ℝ))
    (R : ℝ → F →L[ℝ] E) (hcR : Continuous R) :
    ∃ J : ℝ → F →L[ℝ] E,Continuous J ∧
      ∀ t,t∈Icc 0 T → ∀ h,J t h=R t h+∫ s in 0..t,D s (J s h) := by
  have hc : Continuous (fun p : ℝ × (F →L[ℝ] E) => (D p.1).comp p.2) :=
    (hcD.comp continuous_fst).clm_comp continuous_snd
  have hLip t : LipschitzWith L (fun J : F →L[ℝ] E => (D t).comp J) := by
    apply LipschitzWith.of_dist_le_mul
    intro J K
    rw [dist_eq_norm,dist_eq_norm,← ContinuousLinearMap.comp_sub]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hb t) (norm_nonneg _))
  obtain ⟨J,hJc,hJ⟩ := Asakura.Chapter8.forced_integral_equation_exists T hT L
    (fun t J => (D t).comp J) hc hLip R hcR
  refine ⟨J,hJc,?_⟩
  intro t ht h
  have he := congrArg (fun A : F →L[ℝ] E => A h) (hJ t ht)
  change J t h=R t h+(∫ s in 0..t,(D s).comp (J s)) h at he
  rw [ContinuousLinearMap.intervalIntegral_apply (φ := fun s => (D s).comp (J s))
    ((hcD.clm_comp hJc).intervalIntegrable 0 t)] at he
  exact he

/-- No derivative of the solution family is assumed: it is obtained from
the constructed variational operator and the quadratic remainder estimate. -/
theorem forcing_parameter_derivative_constructed {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : E → E) (D : E → E →L[ℝ] E) (hD : ∀ z,HasFDerivAt b (D z) z)
    (K L : ℝ≥0) (hK : LipschitzWith K D) (hL : 0<L) (hDb : ∀ z,‖D z‖≤(L:ℝ))
    (X : F → ℝ → E) (W : ℝ → E) (R : ℝ → F →L[ℝ] E) (hcR : Continuous R)
    (x₀ : E) (hcX : ∀ z,Continuous (X z)) (x : F) (T A : ℝ) (hT : 0≤T) (hA : 0≤A)
    (hX : ∀ z s,s∈Icc 0 T → X z s=x₀+(∫ r in 0..s,b (X z r))+W s+R s z)
    (hLip : ∀ h s,s∈Icc 0 T → ‖X (x+h) s-X x s‖≤A*‖h‖) :
    ∃ J : ℝ → F →L[ℝ] E,Continuous J ∧
      (∀ t,t∈Icc 0 T → ∀ h,J t h=R t h+∫ s in 0..t,D (X x s) (J s h)) ∧
      ∀ t,t∈Icc 0 T → HasFDerivAt (fun z => X z t) (J t) x := by
  obtain ⟨J,hcJ,hJ⟩ := forcing_variational_operator_exists T hT (fun t => D (X x t))
    (hK.continuous.comp (hcX x)) L (fun t => hDb _) R hcR
  refine ⟨J,hcJ,hJ,?_⟩
  intro t ht
  exact flow_forcing_parameter_derivative b D hD K hK L (by exact_mod_cast hL) hDb
    X W R x₀ hcX x t A ht.1 hA
    (fun z s hs => hX z s ⟨hs.1,hs.2.trans ht.2⟩)
    (fun h s hs => hLip h s ⟨hs.1,hs.2.trans ht.2⟩) J hcJ
    (fun s hs => hJ s ⟨hs.1,hs.2.trans ht.2⟩)

end Asakura.Chapter12
