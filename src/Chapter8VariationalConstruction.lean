import Chapter8ForcedIntegralExistence
import Chapter8ContinuousVariationalDerivative

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Construct the first variational equation as a continuous path of
bounded linear operators, including its integral equation on every vector. -/
theorem variational_operator_exists {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 ≤ T) (D : ℝ → E →L[ℝ] E) (hcD : Continuous D)
    (L : ℝ≥0) (hb : ∀ t,‖D t‖ ≤ (L:ℝ)) :
    ∃ J : ℝ → E →L[ℝ] E,Continuous J ∧
      ∀ t,t∈Icc 0 T → ∀ h,J t h=h+∫ s in 0..t,D s (J s h) := by
  have hc : Continuous (fun p : ℝ × (E →L[ℝ] E) => D p.1*p.2) :=
    (hcD.comp continuous_fst).mul continuous_snd
  have hLip t : LipschitzWith L (fun J : E →L[ℝ] E => D t*J) := by
    apply LipschitzWith.of_dist_le_mul
    intro J K
    rw [dist_eq_norm,dist_eq_norm,← mul_sub]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hb t) (norm_nonneg _))
  obtain ⟨J,hJc,hJ⟩ := forced_integral_equation_exists T hT L (fun t J => D t*J) hc hLip
    (fun _ => (1 : E →L[ℝ] E)) continuous_const
  refine ⟨J,hJc,?_⟩
  intro t ht h
  have he := congrArg (fun A : E →L[ℝ] E => A h) (hJ t ht)
  change J t h=h+(∫ s in 0..t,D s*J s) h at he
  rw [ContinuousLinearMap.intervalIntegral_apply (φ := fun s => D s*J s)
    ((hcD.mul hJc).intervalIntegrable 0 t)] at he
  exact he

/-- For the given solution family, the initial-state derivative is now
constructed, not supplied as an assumed variational process. -/
theorem flow_first_derivative_constructed {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : E → E) (D : E → E →L[ℝ] E) (hD : ∀ z,HasFDerivAt b (D z) z)
    (K L : ℝ≥0) (hK : LipschitzWith K D) (hL : 0<L) (hDb : ∀ z,‖D z‖ ≤ (L:ℝ))
    (X : E → ℝ → E) (W : ℝ → E) (hcX : ∀ z,Continuous (X z))
    (x : E) (T A : ℝ) (hT : 0 ≤ T) (hA : 0 ≤ A)
    (hX : ∀ z s,s∈Icc 0 T → X z s=z+(∫ r in 0..s,b (X z r))+W s)
    (hLip : ∀ h s,s∈Icc 0 T → ‖X (x+h) s-X x s‖ ≤ A*‖h‖) :
    ∃ J : ℝ → E →L[ℝ] E,Continuous J ∧
      (∀ t,t∈Icc 0 T → ∀ h,J t h=h+∫ s in 0..t,D (X x s) (J s h)) ∧
      ∀ t,t∈Icc 0 T → HasFDerivAt (fun z => X z t) (J t) x := by
  obtain ⟨J,hJc,hJ⟩ := variational_operator_exists T hT (fun t => D (X x t))
    (hK.continuous.comp (hcX x)) L (fun t => hDb _)
  refine ⟨J,hJc,hJ,?_⟩
  intro t ht
  exact continuous_variational_derivative b D hD hK.continuous (ContinuousLinearMap.id ℝ E) 0
    X W hcX x t A L ht.1 hA (by exact_mod_cast hL) (fun s _ => hDb _)
    (fun z s hs => by simpa only [ContinuousLinearMap.id_apply,add_zero] using hX z s ⟨hs.1,hs.2.trans ht.2⟩)
    (fun h s hs => hLip h s ⟨hs.1,hs.2.trans ht.2⟩) J hJc
    (fun s hs => hJ s ⟨hs.1,hs.2.trans ht.2⟩)

end Asakura.Chapter8
