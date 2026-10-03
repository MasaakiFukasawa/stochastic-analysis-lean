import Chapter12MalliavinC1Chain

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem closed_C1_chain_raw_output {Ω H:Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P:Measure Ω) [IsProbabilityMeasure P] (W:H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u:Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤)
    (D:Lp ℝ p P →ₗ.[ℝ] Lp H p P) (hD:D.IsClosed)
    (hg:(D.graph:Set _)=closure (range (cylinderPair P W S hS hcore p hp)))
    (F:Lp ℝ p P) (U:Lp H p P) (hFU:(F,U)∈D.graph)
    (f df:ℝ → ℝ) (hd:∀x,HasDerivAt f (df x) x) (hdc:Continuous df)
    (C:ℝ) (hC:0≤C) (hb:∀x,|df x|≤C)
    (Y:Lp ℝ p P) (Z:Lp H p P)
    (hY:(Y:Ω → ℝ)=ᵐ[P] (fun w => f (F w)))
    (hZ:(Z:Ω → H)=ᵐ[P] (fun w => df (F w) • U w)) : (Y,Z)∈D.graph := by
  obtain ⟨hi,hg'⟩ := closed_malliavin_C1_chain P W S hS hcore p hp D hD hg F U hFU
    f df hd hdc C hC hb
  have heY:lipschitzCompositionLp P p (bounded_derivative_lipschitz f df hd C hC hb) F=Y :=
    Lp.ext ((lipschitzCompositionLp_coe P p _ F).trans hY.symm)
  have heZ:hi.toLp _=Z := Lp.ext (hi.coeFn_toLp.trans hZ.symm)
  rwa [heY,heZ] at hg'
end Asakura.Chapter12
#print axioms Asakura.Chapter12.closed_C1_chain_raw_output
