import Chapter12SobolevExponentCompatibility

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem lower_exponent_graph_raw {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (Dp : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (Dq : Lp ℝ q P →ₗ.[ℝ] Lp H q P)
    (hgp : (Dp.graph : Set _) = closure (range (cylinderPair P W S hS hcore p hp)))
    (hgq : (Dq.graph : Set _) = closure (range (cylinderPair P W S hS hcore q hq)))
    (F : Ω → ℝ) (U : Ω → H) (hF : MemLp F q P) (hU : MemLp U q P)
    (hFU : (hF.toLp _,hU.toLp _) ∈ Dq.graph) :
    ((hF.mono_exponent hpq).toLp _,(hU.mono_exponent hpq).toLp _) ∈ Dp.graph := by
  have hg := closed_malliavin_exponent_compatibility P W S hS hcore p q hpq hp hq Dp Dq hgp hgq
    (hF.toLp _) (hU.toLp _) hFU
  have hv : probabilityLpInclusion P p q hpq (hF.toLp _) = (hF.mono_exponent hpq).toLp _ := by
    apply Lp.ext
    exact (probabilityLpInclusion_coe P p q hpq (hF.toLp _)).trans
      (hF.coeFn_toLp.trans (hF.mono_exponent hpq).coeFn_toLp.symm)
  have hu : probabilityLpInclusion P p q hpq (hU.toLp _) = (hU.mono_exponent hpq).toLp _ := by
    apply Lp.ext
    exact (probabilityLpInclusion_coe P p q hpq (hU.toLp _)).trans
      (hU.coeFn_toLp.trans (hU.mono_exponent hpq).coeFn_toLp.symm)
  rwa [hv,hu] at hg

end Asakura.Chapter12
