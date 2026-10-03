import Chapter12MalliavinC1Chain
import Chapter12CallClosedChain

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem smoothCallSlope_continuous (ε K : ℝ) (hε : 0 < ε) :
    Continuous (smoothCallSlope ε K) := by
  unfold smoothCallSlope
  apply Continuous.div_const
  apply continuous_const.add
  apply Continuous.div (continuous_id.sub continuous_const)
    (Real.continuous_sqrt.comp ((continuous_id.sub continuous_const).pow 2 |>.add continuous_const))
  intro x
  exact (Real.sqrt_pos.mpr (by positivity : 0 < (x-K)^2+ε^2)).ne'

/-- The call-payoff chain rule now uses the proved C1 rule, so no smooth
chain-rule graph membership remains as an external assumption. -/
theorem closed_malliavin_call_chain {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (hD : D.IsClosed)
    (hgraph : (D.graph : Set (Lp ℝ p P × Lp H p P)) =
      closure (range (cylinderPair P W S hS hcore p hp)))
    (F : Lp ℝ p P) (U : Lp H p P) (hFU : (F,U) ∈ D.graph)
    (K : ℝ) (hno : P {w | F w = K} = 0) :
    ∃ (hi : MemLp (fun w => max (F w-K) 0) p P)
      (hdi : MemLp (fun w => (if K < F w then (1:ℝ) else 0) • U w) p P),
      (hi.toLp _,hdi.toLp _) ∈ D.graph := by
  let ε := fun n : ℕ => (1:ℝ)/(n+1)
  have hε n : 0 < ε n := by dsimp only [ε]; positivity
  apply call_chain_by_closed_graph P p hp D hD F (Lp.stronglyMeasurable F).measurable
    (Lp.memLp F) U (Lp.memLp U) K hno ε hε tendsto_one_div_add_atTop_nhds_zero_nat
  intro n hi hdi
  have hb x : |smoothCallSlope (ε n) K x| ≤ 1 := by
    have hh := smoothCall_slope_bounds (ε n) K x (hε n)
    rw [abs_of_nonneg hh.1]
    exact hh.2
  obtain ⟨hdj,hm⟩ := closed_malliavin_C1_chain P W S hS hcore p hp D hD hgraph F U hFU
    (smoothCall (ε n) K) (smoothCallSlope (ε n) K)
    (fun x => smoothCall_derivative (ε n) K x (hε n)) (smoothCallSlope_continuous _ _ (hε n))
    1 zero_le_one hb
  have he : lipschitzCompositionLp P p (bounded_derivative_lipschitz
      (smoothCall (ε n) K) (smoothCallSlope (ε n) K)
      (fun x => smoothCall_derivative (ε n) K x (hε n)) 1 zero_le_one hb) F = hi.toLp _ := by
    apply Lp.ext
    exact (lipschitzCompositionLp_coe P p _ F).trans hi.coeFn_toLp.symm
  rw [he] at hm
  exact hm

end Asakura.Chapter12
