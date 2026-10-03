import Chapter12FiniteSumGraphRaw
import Chapter12StockDerivative
import Chapter12CallGraphRaw

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Finite weighted lognormal baskets lie in the closed derivative domain;
the call derivative follows by smooth approximation at its atomless strike. -/
theorem basket_call_derivative_graph {Ω H ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD : D.IsClosed)
    (hg : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (A wgt : ι → ℝ) (h : ι → H) (K c : ℝ)
    (hno : P {w | (∑ i,wgt i*(A i*Real.exp (W (h i) w)))=K}=0) :
    let V := fun w => ∑ i,wgt i*(A i*Real.exp (W (h i) w))
    let U := fun w => ∑ i,(wgt i*(A i*Real.exp (W (h i) w))) • h i
    ∃ hi : MemLp (fun w => c*max (V w-K) 0) 2 P,
    ∃ hdi : MemLp (fun w => c • ((if K<V w then (1:ℝ) else 0) • U w)) 2 P,
      (hi.toLp _,hdi.toLp _) ∈ D.graph := by
  classical
  let F := fun i w => (wgt i*A i)*Real.exp (W (h i) w)
  let U := fun i w => F i w • h i
  have hstock := fun i => stock_exponential_derivative_graph P W S hS hcore 2 (by simp) D hD hg (wgt i*A i) (h i)
  choose hF hU hFU using hstock
  obtain ⟨hs,hus,hgs⟩ := finite_sum_derivative_graph_raw P 2 D F U hF hU hFU
  have hn : P {w | (∑ i,F i w)=K}=0 := by
    simpa only [F,mul_assoc] using hno
  obtain ⟨hc,hdc,hgc⟩ := closed_call_graph_raw P W S hS hcore D hD hg
    (fun w => ∑ i,F i w) (fun w => ∑ i,U i w) hs hus hgs K hn
  have hr := scale_derivative_graph_raw P 2 D _ _ hc hdc hgc c
  simpa only [F,U,mul_assoc] using hr

end Asakura.Chapter12
