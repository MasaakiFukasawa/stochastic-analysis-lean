import Chapter12ClosedProductRule

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem closed_malliavin_product_raw {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderTriple q q p]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (Dp : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (Dq : Lp ℝ q P →ₗ.[ℝ] Lp H q P) (hDp : Dp.IsClosed)
    (hgp : (Dp.graph : Set _) = closure (range (cylinderPair P W S hS hcore p hp)))
    (hgq : (Dq.graph : Set _) = closure (range (cylinderPair P W S hS hcore q hq)))
    (F G : Ω → ℝ) (U V : Ω → H)
    (hF : MemLp F q P) (hG : MemLp G q P) (hU : MemLp U q P) (hV : MemLp V q P)
    (hFU : (hF.toLp _,hU.toLp _) ∈ Dq.graph) (hGV : (hG.toLp _,hV.toLp _) ∈ Dq.graph) :
    ∃ hi : MemLp (fun w => F w*G w) p P,
    ∃ hdi : MemLp (fun w => G w • U w+F w • V w) p P,
      (hi.toLp _,hdi.toLp _) ∈ Dp.graph := by
  have hi : MemLp (fun w => F w*G w) p P := hF.mul hG
  have hdi : MemLp (fun w => G w • U w+F w • V w) p P := (hG.smul hU).add (hF.smul hV)
  have hg := closed_malliavin_product_rule P W S hS hcore p q hp hq Dp Dq hDp hgp hgq
    (hF.toLp _) (hG.toLp _) (hU.toLp _) (hV.toLp _) hFU hGV
  let B := (ContinuousLinearMap.mul ℝ ℝ).holderL P q q p
  let C := (ContinuousLinearMap.lsmul ℝ ℝ (E := H)).holderL P q q p
  have hv : B (hF.toLp _) (hG.toLp _) = hi.toLp _ := by
    apply Lp.ext
    filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := p) (hF.toLp _) (hG.toLp _),
      hF.coeFn_toLp,hG.coeFn_toLp,hi.coeFn_toLp] with w h1 h2 h3 h4
    simp only [B,ContinuousLinearMap.holderL_apply_apply]
    rw [h1,h2,h3,h4]
    rfl
  have hu : C (hG.toLp _) (hU.toLp _)+C (hF.toLp _) (hV.toLp _) = hdi.toLp _ := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (C (hG.toLp _) (hU.toLp _)) (C (hF.toLp _) (hV.toLp _)),
      (ContinuousLinearMap.lsmul ℝ ℝ (E := H)).coeFn_holder (r := p) (hG.toLp _) (hU.toLp _),
      (ContinuousLinearMap.lsmul ℝ ℝ (E := H)).coeFn_holder (r := p) (hF.toLp _) (hV.toLp _),
      hF.coeFn_toLp,hG.coeFn_toLp,hU.coeFn_toLp,hV.coeFn_toLp,hdi.coeFn_toLp] with w h1 h2 h3 h4 h5 h6 h7 h8
    rw [h1,Pi.add_apply]
    simp only [C,ContinuousLinearMap.holderL_apply_apply]
    rw [h2,h3,h4,h5,h6,h7,h8]
    rfl
  refine ⟨hi,hdi,?_⟩
  change (B (hF.toLp _) (hG.toLp _),C (hG.toLp _) (hU.toLp _)+C (hF.toLp _) (hV.toLp _)) ∈ Dp.graph at hg
  rwa [hv,hu] at hg

end Asakura.Chapter12
