import Chapter12ClosedDirectionDivergence

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The weighted deterministic-direction divergence as actual random
variables, with all L2 membership obtained from the closed Sobolev graph. -/
theorem closed_direction_divergence_raw {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H] [CompleteSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] [ENNReal.HolderTriple q q 2] (hq : q ≠ ⊤) (hq2 : 2 ≤ q)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (Dq : Lp ℝ q P →ₗ.[ℝ] Lp H q P)
    (hg : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (hgq : (Dq.graph : Set _) = closure (range (cylinderPair P W S hS hcore q hq)))
    (F : Ω → ℝ) (U : Ω → H) (hF : MemLp F q P) (hU : MemLp U q P)
    (hFU : (hF.toLp _,hU.toLp _) ∈ Dq.graph) (h : H) :
    ∃ hv : MemLp (fun w => F w • h) 2 P,
    ∃ hz : MemLp (fun w => F w*W h w-inner ℝ (U w) h) 2 P,
      IsDivergence D (hv.toLp _) (hz.toLp _) := by
  have hW : MemLp (W h : Ω → ℝ) q P :=
    (linearSmoothCylinder h).value_memLp P W S hS hcore q hq
  have hv : MemLp (fun w => F w • h) 2 P :=
    (ContinuousLinearMap.toSpanSingleton ℝ h).comp_memLp' (hF.mono_exponent hq2)
  have hz : MemLp (fun w => F w*W h w-inner ℝ (U w) h) 2 P := by
    have hm : MemLp (fun w => F w*W h w) 2 P := hF.mul hW
    have hi : MemLp (fun w => inner ℝ (U w) h) 2 P := by
      convert (innerSL ℝ h).comp_memLp' (hU.mono_exponent hq2) using 1
      funext w
      exact real_inner_comm _ _
    exact hm.sub hi
  have hd := closed_direction_divergence P W S hS hcore q hq hq2 D Dq hg hgq
    (hF.toLp _) (hU.toLp _) hFU h
  have he : (ContinuousLinearMap.toSpanSingleton ℝ h).compLp
      (probabilityLpInclusion P 2 q hq2 (hF.toLp _)) = hv.toLp _ := by
    apply Lp.ext
    filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ h).coeFn_compLp
      (probabilityLpInclusion P 2 q hq2 (hF.toLp _)),
      probabilityLpInclusion_coe P 2 q hq2 (hF.toLp _),hF.coeFn_toLp,hv.coeFn_toLp] with w h1 h2 h3 h4
    rw [h1,h4]
    change (probabilityLpInclusion P 2 q hq2 (hF.toLp _) w) • h = _
    rw [h2,h3]
  let B := (ContinuousLinearMap.mul ℝ ℝ).holderL P q q 2
  let wh := (linearSmoothCylinder h).valueLp P W S hS hcore q hq
  let L := innerSL ℝ h
  let K := probabilityLpInclusion (E := H) P 2 q hq2
  have hz' : B (hF.toLp _) wh-L.compLp (K (hU.toLp _)) = hz.toLp _ := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (B (hF.toLp _) wh) (L.compLp (K (hU.toLp _))),
      (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (hF.toLp _) wh,
      L.coeFn_compLp (K (hU.toLp _)),probabilityLpInclusion_coe P 2 q hq2 (hU.toLp _),
      hF.coeFn_toLp,hU.coeFn_toLp,
      ((linearSmoothCylinder h).value_memLp P W S hS hcore q hq).coeFn_toLp,hz.coeFn_toLp] with w h1 h2 h3 h4 h5 h6 h7 h8
    rw [h1,Pi.sub_apply]
    simp only [B,ContinuousLinearMap.holderL_apply_apply]
    rw [h2,h3,h8]
    change hF.toLp _ w * wh w-inner ℝ h (K (hU.toLp _) w) = _
    rw [h4,h5,h6]
    dsimp only [wh,SmoothCylinder.valueLp]
    rw [h7,linear_cylinder_value,real_inner_comm h]
  refine ⟨hv,hz,?_⟩
  change IsDivergence D _ (B (hF.toLp _) wh-L.compLp (K (hU.toLp _))) at hd
  rwa [he,hz'] at hd

end Asakura.Chapter12
