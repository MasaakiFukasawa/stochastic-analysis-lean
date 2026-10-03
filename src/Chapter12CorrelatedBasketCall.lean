import Chapter12CorrelatedBasketAtomless
import Chapter12BasketCallGraph

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem correlated_basket_call_derivative {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hlaw : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD : D.IsClosed)
    (hg : (D.graph : Set _) = closure (range (cylinderPair P W univ dense_univ (fun h _ => hlaw h) 2 (by simp))))
    (d : ℕ) (e : Fin (d+1) → H) (he : Orthonormal ℝ e)
    (A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) (hA : A.det≠0)
    (s wgt : Fin (d+1) → ℝ) (hs : 0<s 0) (hwgt : 0<wgt 0) (K discount : ℝ) :
    let h := fun i => ∑ j,A i j • e j
    let V := fun w => ∑ i,wgt i*(s i*Real.exp (W (h i) w))
    let U := fun w => ∑ i,(wgt i*(s i*Real.exp (W (h i) w))) • h i
    ∃ hi : MemLp (fun w => discount*max (V w-K) 0) 2 P,
    ∃ hdi : MemLp (fun w => discount • ((if K<V w then (1:ℝ) else 0) • U w)) 2 P,
      (hi.toLp _,hdi.toLp _) ∈ D.graph := by
  have hno := correlated_wiener_basket_atomless P W hlaw d e he A hA
    (fun i => wgt i*s i) (mul_pos hwgt hs) K
  apply basket_call_derivative_graph P W univ dense_univ (fun h _ => hlaw h) D hD hg
    s wgt (fun i => ∑ j,A i j • e j) K discount
  simpa only [mul_assoc] using hno

end Asakura.Chapter12
