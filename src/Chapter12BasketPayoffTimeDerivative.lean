import Chapter12BasketBrownianPayoff
import Chapter12BasketTerminalKernel

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

theorem basket_payoff_time_derivative {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) (T : ℝ≥0) (hT : 0<T) :
    letI := finite_horizon_L2_nontrivial (T:ℝ) (show (0:ℝ)<T from hT)
    ∀ (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P),
    ∀ hlaw : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P,
    ∀ (D : Lp ℝ 2 P →ₗ.[ℝ] Lp (FiniteWienerHilbert d T) 2 P),D.IsClosed →
    (D.graph : Set _) = closure (range (cylinderPair P W univ dense_univ (fun h _ => hlaw h) 2 (by simp))) →
    ∀ (Z : Fin (d+1) → Ω → ℝ),(∀ j,Measurable (Z j)) →
    (∀ j,Z j =ᵐ[P] (W (brownianTimeDirection (j,⟨(T:ℝ),T.property,le_rfl⟩)) : Ω → ℝ)) →
    ∀ (A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ),A.det≠0 →
    ∀ (s wgt : Fin (d+1) → ℝ),0<s 0 → 0<wgt 0 → ∀ K discount : ℝ,
    let C := fun i w => wgt i*(s i*Real.exp (∑ j,A i j*Z j w))
    let V := fun w => ∑ i,C i w
    ∃ hi : MemLp (fun w => discount*max (V w-K) 0) 2 P,
    ∃ U : Lp (FiniteWienerHilbert d T) 2 P,
      (hi.toLp _,U) ∈ D.graph ∧
      ∀ j,(brownianDerivativeTime P T T.property U j : Ω × Icc (0:ℝ) T → ℝ)
        =ᵐ[P.prod (compactTimeMeasure T T.property)]
          (fun z => discount*(if K<V z.1 then (1:ℝ) else 0)*(∑ i,C i z.1*A i j)) := by
  letI := finite_horizon_L2_nontrivial (T:ℝ) (show (0:ℝ)<T from hT)
  intro W hlaw D hD hg Z hZm hZ A hA s wgt hs hwgt K discount
  let C := fun i w => wgt i*(s i*Real.exp (∑ j,A i j*Z j w))
  let V := fun w => ∑ i,C i w
  let q := fun w => discount*(if K<V w then (1:ℝ) else 0)
  have hC (i) : Measurable (C i) := by
    exact ((Real.measurable_exp.comp (Finset.measurable_sum _ (fun j _ => (hZm j).const_mul _))).const_mul _).const_mul _
  have hV : Measurable V := Finset.measurable_sum _ (fun i _ => hC i)
  have hq : Measurable q := (measurable_const.ite (measurableSet_lt measurable_const hV) measurable_const).const_mul discount
  obtain ⟨hi,hdi,hgraph⟩ := basket_brownian_payoff_graph P d T hT W hlaw D hD hg Z hZ A hA s wgt hs hwgt K discount
  refine ⟨hi,hdi.toLp _,hgraph,?_⟩
  intro j
  apply basket_terminal_derivative_time P d T T.property A C hC q hq
  filter_upwards [hdi.coeFn_toLp] with w hw
  rw [hw,smul_smul]

end Asakura.Chapter12
