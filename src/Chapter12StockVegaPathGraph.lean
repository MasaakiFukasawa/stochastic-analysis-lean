import Chapter12StockVegaIntegrand
import Chapter12StockPathEnvelope

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem stock_vega_path_graph {Ω H : Type*} [MeasurableSpace Ω]
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
    (T : ℝ) (X : Ω → C(Icc (0:ℝ) T,ℝ)) (h : Icc (0:ℝ) T → H)
    (hXW : ∀ t, (fun w => X w t) =ᵐ[P] (W (h t) : Ω → ℝ))
    (x σ r : ℝ) (t : Icc (0:ℝ) T) :
    ∃ hi : MemLp (fun w => stockPathValue x σ r T (X w) t*(X w t-σ*t.val)) p P,
    ∃ hdi : MemLp (fun w => (stockPathValue x σ r T (X w) t*(σ*(X w t-σ*t.val)+1)) • h t) p P,
      (hi.toLp _,hdi.toLp _) ∈ Dp.graph := by
  let A := x*Real.exp ((r-σ^2/2)*t.val)
  obtain ⟨hi,hdi,hg⟩ := stock_vega_integrand_graph P W S hS hcore p q hp hq Dp Dq hDp hDq hgp hgq
    A σ (-σ*t.val) (h t)
  have hse : (fun w => A*Real.exp (W (σ • h t) w)) =ᵐ[P]
      (fun w => stockPathValue x σ r T (X w) t) := by
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul σ (W (h t)),hXW t] with w h1 h2
    rw [h1,Pi.smul_apply,←h2]
    dsimp [A,stockPathValue]
    rw [Real.exp_add]
    ring
  have he : (fun w => A*Real.exp (W (σ • h t) w)*(W (h t) w+ -σ*t.val)) =ᵐ[P]
      (fun w => stockPathValue x σ r T (X w) t*(X w t-σ*t.val)) := by
    filter_upwards [hse,hXW t] with w h1 h2
    rw [h1,←h2]
    ring
  have hue : (fun w => (A*Real.exp (W (σ • h t) w)*(σ*(W (h t) w+ -σ*t.val)+1)) • h t) =ᵐ[P]
      (fun w => (stockPathValue x σ r T (X w) t*(σ*(X w t-σ*t.val)+1)) • h t) := by
    filter_upwards [hse,hXW t] with w h1 h2
    rw [h1,←h2]
    congr 1
    ring
  have hi' := hi.ae_eq he
  have hdi' := hdi.ae_eq hue
  refine ⟨hi',hdi',?_⟩
  have hv : hi.toLp _ = hi'.toLp _ := Lp.ext (hi.coeFn_toLp.trans (he.trans hi'.coeFn_toLp.symm))
  have hu : hdi.toLp _ = hdi'.toLp _ := Lp.ext (hdi.coeFn_toLp.trans (hue.trans hdi'.coeFn_toLp.symm))
  rwa [←hv,←hu]

end Asakura.Chapter12
