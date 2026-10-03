import Chapter12ClosedQuotientRaw
import Chapter12ClosedDirectionDivergenceRaw
import Chapter12ScaleGraphRaw

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

/-- Divergence of the quotient direction used by Asian Greeks. Every
closed-domain product, inverse, scaling and divergence step is connected. -/
theorem quotient_direction_divergence {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H] [CompleteSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderTriple q q p] [ENNReal.HolderTriple p p 2]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp2 : 2 ≤ p)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (Dp : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (Dq : Lp ℝ q P →ₗ.[ℝ] Lp H q P)
    (hDp : Dp.IsClosed) (hDq : Dq.IsClosed)
    (hg : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (hgp : (Dp.graph : Set _) = closure (range (cylinderPair P W S hS hcore p hp)))
    (hgq : (Dq.graph : Set _) = closure (range (cylinderPair P W S hS hcore q hq)))
    (F G : Ω → ℝ) (U V : Ω → H)
    (hF : MemLp F q P) (hG : MemLp G q P) (hU : MemLp U q P) (hV : MemLp V q P)
    (hFU : (hF.toLp _,hU.toLp _) ∈ Dq.graph) (hGV : (hG.toLp _,hV.toLp _) ∈ Dq.graph)
    (hpos : ∀ᵐ w ∂P, 0 < G w)
    (hi : MemLp (fun w => (G w)⁻¹) q P)
    (hdi : MemLp (fun w => (-(G w)⁻¹^2) • V w) q P) (c : ℝ) (h : H) :
    ∃ hv : MemLp (fun w => (c*F w/G w) • h) 2 P,
    ∃ hz : MemLp (fun w => (c*F w/G w)*W h w-
      c*(inner ℝ (U w) h/G w-F w*inner ℝ (V w) h/(G w)^2)) 2 P,
      IsDivergence D (hv.toLp _) (hz.toLp _) := by
  obtain ⟨hQ,hDQ,hQG⟩ := closed_quotient_raw P W S hS hcore p q hp hq Dp Dq hDp hDq hgp hgq
    F G U V hF hG hU hV hFU hGV hpos hi hdi
  obtain ⟨hR,hDR,hRG⟩ := scale_derivative_graph_raw P p Dp _ _ hQ hDQ hQG c
  obtain ⟨hv,hz,hd⟩ := closed_direction_divergence_raw P W S hS hcore p hp hp2 D Dp hg hgp
    _ _ hR hDR hRG h
  have he : (fun w => (c*(F w/G w)) • h) = (fun w => (c*F w/G w) • h) := by
    funext w
    rw [mul_div_assoc]
  have hze : (fun w => (c*(F w/G w))*W h w-inner ℝ
      (c • ((G w)⁻¹ • U w-(F w/(G w)^2) • V w)) h) =
      (fun w => (c*F w/G w)*W h w-c*(inner ℝ (U w) h/G w-F w*inner ℝ (V w) h/(G w)^2)) := by
    funext w
    rw [real_inner_smul_left,inner_sub_left,real_inner_smul_left,real_inner_smul_left]
    simp only [div_eq_mul_inv]
    ring
  have hv' := hv.ae_eq (ae_of_all P (congrFun he))
  have hz' := hz.ae_eq (ae_of_all P (congrFun hze))
  refine ⟨hv',hz',?_⟩
  have hve : hv.toLp _ = hv'.toLp _ := by
    apply Lp.ext
    filter_upwards [hv.coeFn_toLp,hv'.coeFn_toLp] with w h1 h2
    rw [h1,h2]
    exact congrFun he w
  have hzz : hz.toLp _ = hz'.toLp _ := by
    apply Lp.ext
    filter_upwards [hz.coeFn_toLp,hz'.coeFn_toLp] with w h1 h2
    rw [h1,h2]
    exact congrFun hze w
  rwa [←hve,←hzz]

end Asakura.Chapter12
