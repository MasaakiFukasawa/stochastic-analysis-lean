import Chapter12FiniteBrownianBasketCall
import Chapter12RawGraphTransfer

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

/-- The closed derivative of the basket written with the original terminal
Brownian coordinates, rather than chosen Lp representatives of Wiener integrals. -/
theorem basket_brownian_payoff_graph {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) (T : ℝ≥0) (hT : 0<T) :
    letI := finite_horizon_L2_nontrivial (T:ℝ) (show (0:ℝ)<T from hT)
    ∀ (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P),
    ∀ hlaw : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P,
    ∀ (D : Lp ℝ 2 P →ₗ.[ℝ] Lp (FiniteWienerHilbert d T) 2 P),D.IsClosed →
    (D.graph : Set _) = closure (range (cylinderPair P W univ dense_univ (fun h _ => hlaw h) 2 (by simp))) →
    ∀ (Z : Fin (d+1) → Ω → ℝ),
    (∀ j,Z j =ᵐ[P] (W (brownianTimeDirection (j,⟨(T:ℝ),T.property,le_rfl⟩)) : Ω → ℝ)) →
    ∀ (A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ),A.det≠0 →
    ∀ (s wgt : Fin (d+1) → ℝ),0<s 0 → 0<wgt 0 → ∀ K discount : ℝ,
    let h := fun i => ∑ j,A i j • brownianTimeDirection (j,⟨(T:ℝ),T.property,le_rfl⟩)
    let V := fun w => ∑ i,wgt i*(s i*Real.exp (∑ j,A i j*Z j w))
    let U := fun w => ∑ i,(wgt i*(s i*Real.exp (∑ j,A i j*Z j w))) • h i
    ∃ hi : MemLp (fun w => discount*max (V w-K) 0) 2 P,
    ∃ hdi : MemLp (fun w => discount • ((if K<V w then (1:ℝ) else 0) • U w)) 2 P,
      (hi.toLp _,hdi.toLp _) ∈ D.graph := by
  letI := finite_horizon_L2_nontrivial (T:ℝ) (show (0:ℝ)<T from hT)
  intro W hlaw D hD hg Z hZ A hA s wgt hs hwgt K discount
  let e := fun j : Fin (d+1) => brownianTimeDirection (j,⟨(T:ℝ),T.property,le_rfl⟩)
  let h := fun i => ∑ j,A i j • e j
  obtain ⟨hi,hdi,hgraph⟩ := finite_brownian_basket_call_derivative P d T hT W hlaw D hD hg A hA s wgt hs hwgt K discount
  have hlinear : ∀ᵐ w ∂P,∀ i,W (h i) w=∑ j,A i j*Z j w := by
    filter_upwards [ae_all_iff.mpr (fun i => wiener_finite_linearity P W.toLinearMap e (A i)),
      ae_all_iff.mpr hZ] with w hw hz
    intro i
    have hh : W (h i) w=∑ j,A i j*W (e j) w := hw i
    rw [hh]
    exact Finset.sum_congr rfl (fun j _ => congrArg (fun z => A i j*z) (hz j).symm)
  apply derivative_graph_raw_ae_transfer P 2 D _ _ _ _ hi hdi hgraph
  · filter_upwards [hlinear] with w hw
    change discount*max ((∑ i,wgt i*(s i*Real.exp (W (h i) w)))-K) 0 =
      discount*max ((∑ i,wgt i*(s i*Real.exp (∑ j,A i j*Z j w)))-K) 0
    simp only [hw]
  · filter_upwards [hlinear] with w hw
    change discount • ((if K<(∑ i,wgt i*(s i*Real.exp (W (h i) w))) then (1:ℝ) else 0) •
      (∑ i,(wgt i*(s i*Real.exp (W (h i) w))) • h i)) =
      discount • ((if K<(∑ i,wgt i*(s i*Real.exp (∑ j,A i j*Z j w))) then (1:ℝ) else 0) •
        (∑ i,(wgt i*(s i*Real.exp (∑ j,A i j*Z j w))) • h i))
    simp only [hw]

end Asakura.Chapter12
