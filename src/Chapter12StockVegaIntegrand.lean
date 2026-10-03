import Chapter12ClosedProductRaw
import Chapter12ConstantDerivativeGraph

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- The stock multiplied by its logarithmic volatility derivative belongs
 to the closed Sobolev graph; neither the product rule nor its moments
 are additional assumptions. -/
theorem stock_vega_integrand_graph {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderTriple q q p]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (Dp : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (Dq : Lp ℝ q P →ₗ.[ℝ] Lp H q P)
    (hDp : Dp.IsClosed) (hDq : Dq.IsClosed)
    (hgp : (Dp.graph : Set _) = closure (range (cylinderPair P W S hS hcore p hp)))
    (hgq : (Dq.graph : Set _) = closure (range (cylinderPair P W S hS hcore q hq)))
    (A σ b : ℝ) (h : H) :
    ∃ hi : MemLp (fun w => (A*Real.exp (W (σ • h) w))*(W h w+b)) p P,
    ∃ hdi : MemLp (fun w => ((A*Real.exp (W (σ • h) w))*(σ*(W h w+b)+1)) • h) p P,
      (hi.toLp _,hdi.toLp _) ∈ Dp.graph := by
  obtain ⟨hF,hU,hFU⟩ := stock_exponential_derivative_graph P W S hS hcore q hq Dq hDq hgq A (σ • h)
  obtain ⟨hG,hGV⟩ := affine_wiener_derivative_graph P W S hS hcore q hq Dq hDq hgq h b
  obtain ⟨hi,hdi,hg⟩ := closed_malliavin_product_raw P W S hS hcore p q hp hq Dp Dq hDp hgp hgq
    _ _ _ _ hF hG hU (memLp_const h) hFU hGV
  have he : (fun w => (W h w+b) • ((A*Real.exp (W (σ • h) w)) • (σ • h))+
      (A*Real.exp (W (σ • h) w)) • h) =
      (fun w => ((A*Real.exp (W (σ • h) w))*(σ*(W h w+b)+1)) • h) := by
    funext w
    rw [smul_smul,smul_smul,← add_smul]
    congr 1
    ring
  have hdi' := hdi.ae_eq (ae_of_all P (congrFun he))
  refine ⟨hi,hdi',?_⟩
  have hde : hdi.toLp _ = hdi'.toLp _ := by
    apply Lp.ext
    filter_upwards [hdi.coeFn_toLp,hdi'.coeFn_toLp] with w h1 h2
    rw [h1,h2]
    exact congrFun he w
  rwa [←hde]

end Asakura.Chapter12
