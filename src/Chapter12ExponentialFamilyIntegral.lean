import Chapter12IntegralOfSobolevFamily
import Chapter12StockDerivative

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Integrating exponential Wiener variables: graph membership is derived
from the actual cylinder closure, rather than assumed for each time. -/
theorem exponential_wiener_family_integral
    {α Ω H : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    (μ : Measure α) [IsFiniteMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD : D.IsClosed)
    (hgraph : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by norm_num))))
    (A : α → ℝ) (hAm : Measurable A) (X : α × Ω → ℝ) (hXm : Measurable X)
    (v : α → H) (hvm : StronglyMeasurable v)
    (hXW : ∀ x, (fun w => X (x,w)) =ᵐ[P] (W (v x) : Ω → ℝ))
    (C : ℝ) (hC : 0 ≤ C) (hvb : ∀ x, ‖v x‖ ≤ C)
    (G : Ω → ℝ) (hG : MemLp G 2 P)
    (hSb : ∀ x, ∀ᵐ w ∂P, ‖A x * Real.exp (X (x,w))‖ ≤ ‖G w‖) :
    ∃ hL : ∀ x, MemLp (fun w => A x * Real.exp (X (x,w))) 2 P,
    ∃ hi : MemLp (fun w => ∫ x,A x * Real.exp (X (x,w)) ∂μ) 2 P,
      (hi.toLp _,∫ x,(ContinuousLinearMap.toSpanSingleton ℝ (v x)).compLp
        ((hL x).toLp _) ∂μ) ∈ D.graph := by
  have hs (x) := stock_exponential_derivative_graph P W S hS hcore 2 (by norm_num)
    D hD hgraph (A x) (v x)
  have hL (x) : MemLp (fun w => A x * Real.exp (X (x,w))) 2 P := by
    obtain ⟨hi,hdi,hd⟩ := hs x
    apply hi.ae_eq
    filter_upwards [hXW x] with w hw
    rw [hw]
  refine ⟨hL,?_⟩
  apply integrate_sobolev_scalar_direction_family μ P D hD
    (fun z => A z.1 * Real.exp (X z)) ((hAm.comp measurable_fst).mul hXm.exp)
    hL v hvm C hC hvb G hG hSb
  intro x
  obtain ⟨hi,hdi,hd⟩ := hs x
  have hv : (hL x).toLp _ = hi.toLp _ := by
    apply Lp.ext
    filter_upwards [(hL x).coeFn_toLp,hi.coeFn_toLp,hXW x] with w h1 h2 h3
    rw [h1,h2,h3]
  have hu : (ContinuousLinearMap.toSpanSingleton ℝ (v x)).compLp ((hL x).toLp _) =
      hdi.toLp _ := by
    apply Lp.ext
    filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ (v x)).coeFn_compLp ((hL x).toLp _),
      (hL x).coeFn_toLp,hdi.coeFn_toLp,hXW x] with w h1 h2 h3 h4
    rw [h1,h2,h3,h4]
    rfl
  rwa [hu,hv]

end Asakura.Chapter12
