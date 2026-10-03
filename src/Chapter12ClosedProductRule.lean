import Chapter12CylinderProductLp

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- Product rule on the closed domains. Hölder continuity gives the
limit in the target exponent from graph approximations at exponent q. -/
theorem closed_malliavin_product_rule {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderTriple q q p]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (Dp : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (Dq : Lp ℝ q P →ₗ.[ℝ] Lp H q P)
    (hDp : Dp.IsClosed)
    (hgp : (Dp.graph : Set _) = closure (range (cylinderPair P W S hS hcore p hp)))
    (hgq : (Dq.graph : Set _) = closure (range (cylinderPair P W S hS hcore q hq)))
    (F G : Lp ℝ q P) (U V : Lp H q P) (hFU : (F,U) ∈ Dq.graph) (hGV : (G,V) ∈ Dq.graph) :
    ((ContinuousLinearMap.mul ℝ ℝ).holderL P q q p F G,
      (ContinuousLinearMap.lsmul ℝ ℝ (E := H)).holderL P q q p G U+
      (ContinuousLinearMap.lsmul ℝ ℝ (E := H)).holderL P q q p F V) ∈ Dp.graph := by
  let B := (ContinuousLinearMap.mul ℝ ℝ).holderL P q q p
  let C := (ContinuousLinearMap.lsmul ℝ ℝ (E := H)).holderL P q q p
  let J := fun z : (Lp ℝ q P × Lp H q P) × (Lp ℝ q P × Lp H q P) =>
    (B z.1.1 z.2.1,C z.2.1 z.1.2+C z.1.1 z.2.2)
  have hJ : Continuous J := by
    exact (B.continuous₂.comp (continuous_fst.fst.prodMk continuous_snd.fst)).prodMk
      ((C.continuous₂.comp (continuous_snd.fst.prodMk continuous_fst.snd)).add
        (C.continuous₂.comp (continuous_fst.fst.prodMk continuous_snd.snd)))
  have h1 : (F,U) ∈ closure (range (cylinderPair P W S hS hcore q hq)) := by rwa [←hgq]
  have h2 : (G,V) ∈ closure (range (cylinderPair P W S hS hcore q hq)) := by rwa [←hgq]
  obtain ⟨z,hz,hzt⟩ := mem_closure_iff_seq_limit.mp h1
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp h2
  have hm (n) : J (z n,y n) ∈ (Dp.graph : Set (Lp ℝ p P × Lp H p P)) := by
    obtain ⟨c,hc⟩ := hz n
    obtain ⟨d,hd⟩ := hy n
    rw [←hc,←hd]
    change _ ∈ (Dp.graph : Set (Lp ℝ p P × Lp H p P))
    rw [show J (cylinderPair P W S hS hcore q hq c,cylinderPair P W S hS hcore q hq d) =
      cylinderPair P W S hS hcore p hp (mulSmoothCylinder c d) from
        (cylinder_product_Lp_pair P W S hS hcore p q hp hq c d).symm]
    rw [hgp]
    exact subset_closure (mem_range_self _)
  exact hDp.mem_of_tendsto ((hJ.tendsto ((F,U),(G,V))).comp (hzt.prodMk_nhds hyt))
    (Eventually.of_forall hm)

end Asakura.Chapter12
