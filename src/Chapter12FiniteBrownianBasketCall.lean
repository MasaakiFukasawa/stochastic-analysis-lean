import Chapter12EqualVarianceBasketAtomless
import Chapter12BasketCallGraph
import Chapter12BrownianMalliavinOperator

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The closed Malliavin derivative of a correlated basket on the actual
finite-time Brownian Hilbert space. Invertibility supplies the atomless strike. -/
theorem finite_brownian_basket_call_derivative {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) (T : ℝ≥0) (hT : 0<T) :
    letI := finite_horizon_L2_nontrivial (T:ℝ) (show (0:ℝ)<T from hT)
    ∀ (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P),
    ∀ hlaw : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P,
    ∀ (D : Lp ℝ 2 P →ₗ.[ℝ] Lp (FiniteWienerHilbert d T) 2 P),D.IsClosed →
    (D.graph : Set _) = closure (range (cylinderPair P W univ dense_univ (fun h _ => hlaw h) 2 (by simp))) →
    ∀ (A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ),A.det≠0 →
    ∀ (s wgt : Fin (d+1) → ℝ),0<s 0 → 0<wgt 0 → ∀ K discount : ℝ,
    let h := fun i => ∑ j,A i j • brownianTimeDirection (j,⟨(T:ℝ),T.property,le_rfl⟩)
    let V := fun w => ∑ i,wgt i*(s i*Real.exp (W (h i) w))
    let U := fun w => ∑ i,(wgt i*(s i*Real.exp (W (h i) w))) • h i
    ∃ hi : MemLp (fun w => discount*max (V w-K) 0) 2 P,
    ∃ hdi : MemLp (fun w => discount • ((if K<V w then (1:ℝ) else 0) • U w)) 2 P,
      (hi.toLp _,hdi.toLp _) ∈ D.graph := by
  letI := finite_horizon_L2_nontrivial (T:ℝ) (show (0:ℝ)<T from hT)
  intro W hlaw D hD hg A hA s wgt hs hwgt K discount
  have hno := correlated_equal_variance_basket_atomless P W hlaw d
    (fun j => brownianTimeDirection (j,⟨(T:ℝ),T.property,le_rfl⟩)) T hT.ne'
    (brownian_terminal_direction_inner d T T.property) A hA (fun i => wgt i*s i) (mul_pos hwgt hs) K
  apply basket_call_derivative_graph P W univ dense_univ (fun h _ => hlaw h) D hD hg
    s wgt _ K discount
  simpa only [mul_assoc] using hno

end Asakura.Chapter12
