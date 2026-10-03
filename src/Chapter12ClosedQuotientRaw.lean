import Chapter12ReciprocalRaw

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Quotient rule on the closed derivative graph, obtained from the
regularized reciprocal and Holder-continuous product, not postulated. -/
theorem closed_quotient_raw {Ω H : Type*} [MeasurableSpace Ω]
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
    (F G : Ω → ℝ) (U V : Ω → H)
    (hF : MemLp F q P) (hG : MemLp G q P) (hU : MemLp U q P) (hV : MemLp V q P)
    (hFU : (hF.toLp _,hU.toLp _) ∈ Dq.graph) (hGV : (hG.toLp _,hV.toLp _) ∈ Dq.graph)
    (hpos : ∀ᵐ w ∂P, 0 < G w)
    (hi : MemLp (fun w => (G w)⁻¹) q P)
    (hdi : MemLp (fun w => (-(G w)⁻¹^2) • V w) q P) :
    ∃ hQ : MemLp (fun w => F w/G w) p P,
    ∃ hDQ : MemLp (fun w => (G w)⁻¹ • U w-(F w/(G w)^2) • V w) p P,
      (hQ.toLp _,hDQ.toLp _) ∈ Dp.graph := by
  have hrec := closed_reciprocal_raw P W S hS hcore q hq Dq hDq hgq G V hG hV hGV hpos hi hdi
  obtain ⟨hQ,hDQ,hg⟩ := closed_malliavin_product_raw P W S hS hcore p q hp hq Dp Dq hDp hgp hgq
    F _ U _ hF hi hU hdi hFU hrec
  have hv : (fun w => F w*(G w)⁻¹) = (fun w => F w/G w) := by funext w; rw [div_eq_mul_inv]
  have hu : (fun w => (G w)⁻¹ • U w+F w • ((-(G w)⁻¹^2) • V w)) =
      (fun w => (G w)⁻¹ • U w-(F w/(G w)^2) • V w) := by
    funext w
    rw [smul_smul,mul_neg,neg_smul,←sub_eq_add_neg,div_eq_mul_inv,inv_pow]
  have hQ' := hQ.ae_eq (ae_of_all P (congrFun hv))
  have hDQ' := hDQ.ae_eq (ae_of_all P (congrFun hu))
  refine ⟨hQ',hDQ',?_⟩
  have he : hQ.toLp _ = hQ'.toLp _ := by
    apply Lp.ext
    filter_upwards [hQ.coeFn_toLp,hQ'.coeFn_toLp] with w h1 h2
    rw [h1,h2]
    exact congrFun hv w
  have hde : hDQ.toLp _ = hDQ'.toLp _ := by
    apply Lp.ext
    filter_upwards [hDQ.coeFn_toLp,hDQ'.coeFn_toLp] with w h1 h2
    rw [h1,h2]
    exact congrFun hu w
  rwa [←he,←hde]

end Asakura.Chapter12
