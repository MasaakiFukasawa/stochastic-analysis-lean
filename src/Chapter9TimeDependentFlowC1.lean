import Chapter9TimeDependentVariation
import Chapter9TimeDependentStability
import Chapter8VariationalConstruction

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Construct the time-dependent solution family and its actual initial-point
Fréchet derivative. The variational equation is solved by the fixed-point
theorem and then identified with the derivative using the compact Taylor estimate. -/
theorem time_dependent_flow_c1_exists {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (b : ℝ → E → E) (D : ℝ → E → E →L[ℝ] E)
    (hb : Continuous b.uncurry) (hcD : Continuous D.uncurry)
    (hD : ∀ t z,HasFDerivAt (b t) (D t z) z)
    (K : ℝ≥0) (hK : ∀ t,LipschitzWith K (b t))
    (T : ℝ) (hT : 0≤T) :
    ∃ X : E → ℝ → E,
      (∀ x,Continuous (X x)) ∧
      (∀ x t,t∈Icc 0 T → X x t=x+∫ s in 0..t,b s (X x s)) ∧
      ∀ x,∃ J : ℝ → E →L[ℝ] E,Continuous J ∧
        (∀ t,t∈Icc 0 T → ∀ h,J t h=h+∫ s in 0..t,D s (X x s) (J s h)) ∧
        ∀ t,t∈Icc 0 T → HasFDerivAt (fun z => X z t) (J t) x := by
  have hex x := Asakura.Chapter8.forced_integral_equation_exists T hT K b hb hK
    (fun _ => x) continuous_const
  choose X hcX hX using hex
  have hLip x y := time_dependent_initial_stability b K hb hK (X x) (X y) (fun _ => 0)
    (hcX x) (hcX y) x y T hT
    (fun t ht => by simpa only [add_zero] using hX x t ht)
    (fun t ht => by simpa only [add_zero] using hX y t ht)
  have hnorm t z : ‖D t z‖≤(K:ℝ) := by
    rw [←(hD t z).fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ (hK t)
  refine ⟨X,hcX,hX,?_⟩
  intro x
  obtain ⟨J,hJc,hJ⟩ := Asakura.Chapter8.variational_operator_exists T hT
    (fun t => D t (X x t)) (hcD.comp (continuous_id.prodMk (hcX x)))
    (K+1) (fun t => (hnorm t _).trans (by simp))
  refine ⟨J,hJc,hJ,?_⟩
  intro t ht
  apply time_dependent_variational_derivative b D hD hb hcD
    (ContinuousLinearMap.id ℝ E) 0 X (fun _ => 0) hcX x t
    (Real.exp (((K:ℝ)+1)*T)) ((K:ℝ)+1) ht.1 (Real.exp_pos _).le (by positivity)
    (fun s _ => (hnorm s _).trans (by linarith))
    (fun z s hs => by simpa only [ContinuousLinearMap.id_apply,add_zero] using hX z s ⟨hs.1,hs.2.trans ht.2⟩)
    (fun h s hs => by simpa only [add_sub_cancel_left] using hLip (x+h) x s ⟨hs.1,hs.2.trans ht.2⟩)
    J hJc (fun s hs => hJ s ⟨hs.1,hs.2.trans ht.2⟩)
end Asakura.Chapter9
