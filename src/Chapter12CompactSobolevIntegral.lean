import Chapter12ScalarDirectionIntegralPointwise
import Chapter12ClosedDerivativeIntegral

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Integration in the graph of the closed derivative, allowing the
 scalar coefficient of the derivative to differ from the integrand. -/
theorem compact_sobolev_integral
    {α Ω H : Type*} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
    [CompactSpace α] [T2Space α] [SecondCountableTopology α] [FirstCountableTopology α]
    [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure α) [IsFiniteMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp2 : 2 ≤ p)
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (hD : D.IsClosed)
    (F U : α × Ω → ℝ) (hFm : Measurable F) (hUm : Measurable U)
    (hFL : ∀ x, MemLp (fun w => F (x,w)) p P)
    (hUL : ∀ x, MemLp (fun w => U (x,w)) p P)
    (hFc : ∀ w, Continuous (fun x => F (x,w)))
    (hUc : ∀ w, Continuous (fun x => U (x,w)))
    (v : α → H) (hvc : Continuous v)
    (G K : Ω → ℝ) (hG : MemLp G p P) (hK : MemLp K p P)
    (hFb : ∀ x, ∀ᵐ w ∂P, ‖F (x,w)‖ ≤ ‖G w‖)
    (hUb : ∀ x, ∀ᵐ w ∂P, ‖U (x,w)‖ ≤ ‖K w‖)
    (hgraph : ∀ x, ((hFL x).toLp _,(ContinuousLinearMap.toSpanSingleton ℝ (v x)).compLp
      ((hUL x).toLp _)) ∈ D.graph) :
    ∃ hi : MemLp (fun w => ∫ x,F (x,w) ∂μ) p P,
    ∃ hdi : MemLp (fun w => ∫ x,U (x,w) • v x ∂μ) p P,
      (hi.toLp _,hdi.toLp _) ∈ D.graph := by
  let f := fun x => (hFL x).toLp (fun w => F (x,w))
  let u := fun x => (ContinuousLinearMap.toSpanSingleton ℝ (v x)).compLp ((hUL x).toLp _)
  have hfc : Continuous f := continuous_Lp_family_of_dominated_paths P p hp _ hFL
    (ae_of_all P hFc) G hG hFb
  have huc₀ := continuous_Lp_family_of_dominated_paths P p hp _ hUL
    (ae_of_all P hUc) K hK hUb
  let B := (ContinuousLinearMap.lsmul ℝ ℝ (E := H)).flip.compLpL₂ p P
  have huc : Continuous u := B.continuous₂.comp (hvc.prodMk huc₀)
  have hfi := hfc.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hui := huc.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hg := closed_derivative_integral μ D hD f u hfc.stronglyMeasurable huc.stronglyMeasurable
    hfi hui hgraph
  have he := Lp_bochner_integral_pointwise μ P p hp2 F hFm hFL hfi
  have hue := scalar_direction_integral_pointwise μ P p hp hp2 U hUm hUL hUc v hvc K hK hUb
  have hi := (Lp.memLp (∫ x,f x ∂μ)).ae_eq he
  have hdi := (Lp.memLp (∫ x,u x ∂μ)).ae_eq hue
  refine ⟨hi,hdi,?_⟩
  have hv : hi.toLp _ = ∫ x,f x ∂μ := Lp.ext (hi.coeFn_toLp.trans he.symm)
  have hu : hdi.toLp _ = ∫ x,u x ∂μ := Lp.ext (hdi.coeFn_toLp.trans hue.symm)
  rwa [hv,hu]

end Asakura.Chapter12
