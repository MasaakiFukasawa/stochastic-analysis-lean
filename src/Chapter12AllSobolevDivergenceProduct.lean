import Chapter12AllSobolevFirstGraph
import Chapter12ClosedDivergenceProduct
import Chapter12GreekDualExponents

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000

/-- The product formula applies in particular to both D-infinity inputs.
The derivative of G is obtained from its actual first completed jet and
all required fourth moments follow from the completed spaces. -/
theorem all_sobolev_divergence_product {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (D4 : Lp ℝ 4 P →ₗ.[ℝ] Lp H 4 P)
    (hg : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (hg4 : (D4.graph : Set _) = closure (range (cylinderPair P W S hS hcore 4 (by simp))))
    (hd : DenseRange (fun f : D.domain => (f : Lp ℝ 2 P)))
    (hdense : ∀ (q : ℝ≥0∞) [Fact (1≤q)] (hq : q≠⊤),
      DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (U : Lp H 2 P) (hU : HasAllVectorSobolevJets H P W S hS hcore U)
    (G : Ω → ℝ) (hG : HasAllSobolevJets H P W S hS hcore G) :
    ∃ (Z : Lp ℝ 2 P) (DG : Ω → H) (hG4 : MemLp G 4 P) (hDG : MemLp DG 4 P),
      IsDivergence D U Z ∧ HasAllSobolevJets H P W S hS hcore Z ∧
      (hG4.toLp _,hDG.toLp _)∈D4.graph ∧
      ∃ hi : MemLp (fun w => G w • U w) 2 P,
      ∃ hz : MemLp (fun w => G w*Z w-inner ℝ (DG w) (U w)) 2 P,
        IsDivergence D (hi.toLp _) (hz.toLp _) := by
  obtain ⟨Z,hUZ,hZ⟩ := divergence_all_sobolev_orders H P W S hS hcore D hg hd hdense U hU
  obtain ⟨DG,hG4,hDG,hgraph⟩ := all_sobolev_first_graph H P W S hS hcore G hG 4 (by simp) D4 hg4
  have hU4 := all_vector_sobolev_memLp H P W S hS hcore U hU 4 (by simp)
  have hZ4 := all_sobolev_memLp H P W S hS hcore Z hZ 4 (by simp)
  have hrel : IsDivergence D ((hU4.mono_exponent (by norm_num : (2:ℝ≥0∞)≤4)).toLp U)
      ((hZ4.mono_exponent (by norm_num : (2:ℝ≥0∞)≤4)).toLp Z) := by
    simpa only [Lp.toLp_coeFn] using hUZ
  obtain ⟨hi,hz,hprod⟩ := closed_divergence_product_raw P W S hS hcore 4 (by simp) (by norm_num)
    D D4 hg hg4 G Z DG U hG4 hZ4 hDG hU4 hgraph hrel
  exact ⟨Z,DG,hG4,hDG,hUZ,hZ,hgraph,hi,hz,hprod⟩

end Asakura.Chapter12
