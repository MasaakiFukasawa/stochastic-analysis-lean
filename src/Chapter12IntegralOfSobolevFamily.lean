import Chapter12ClosedDerivativeIntegral
import Chapter2L2BochnerPointwise

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Parameter integration of a family whose derivative is S(x) h(x).
The Lp-valued measurability and integrability are constructed from the
joint scalar function and one common L2 envelope. This is the exchange
used for the time moments of an Asian payoff. -/
theorem integrate_sobolev_scalar_direction_family
    {α Ω H : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (μ : Measure α) [IsFiniteMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD : D.IsClosed)
    (S : α × Ω → ℝ) (hSm : Measurable S)
    (hSL : ∀ x, MemLp (fun w => S (x,w)) 2 P)
    (v : α → H) (hvm : StronglyMeasurable v) (C : ℝ) (hC : 0 ≤ C)
    (hvb : ∀ x, ‖v x‖ ≤ C)
    (G : Ω → ℝ) (hG : MemLp G 2 P)
    (hSb : ∀ x, ∀ᵐ w ∂P, ‖S (x,w)‖ ≤ ‖G w‖)
    (hgraph : ∀ x, ((hSL x).toLp _,(ContinuousLinearMap.toSpanSingleton ℝ (v x)).compLp
      ((hSL x).toLp _)) ∈ D.graph) :
    ∃ hi : MemLp (fun w => ∫ x,S (x,w) ∂μ) 2 P,
      (hi.toLp _,∫ x,(ContinuousLinearMap.toSpanSingleton ℝ (v x)).compLp ((hSL x).toLp _) ∂μ) ∈ D.graph := by
  let F := fun x => (hSL x).toLp (fun w => S (x,w))
  let U := fun x => (ContinuousLinearMap.toSpanSingleton ℝ (v x)).compLp (F x)
  have hFm : StronglyMeasurable F := stronglyMeasurable_L2_sections P S hSm hSL
  have hFb (x) : ‖F x‖ ≤ ‖hG.toLp G‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(hSL x).coeFn_toLp,hG.coeFn_toLp,hSb x] with w h1 h2 h3
    change ‖(hSL x).toLp _ w‖ ≤ _
    rw [h1,h2]
    exact h3
  have hFi : Integrable F μ := Integrable.of_bound hFm.aestronglyMeasurable ‖hG.toLp G‖
    (ae_of_all μ hFb)
  let B := (ContinuousLinearMap.lsmul ℝ ℝ (E := H)).flip.compLpL₂ 2 P
  have hUm : StronglyMeasurable U := by
    exact B.continuous₂.comp_stronglyMeasurable (hvm.prodMk hFm)
  have hUb (x) : ‖U x‖ ≤ C*‖hG.toLp G‖ := by
    calc
      ‖U x‖ ≤ ‖ContinuousLinearMap.toSpanSingleton ℝ (v x)‖*‖F x‖ :=
        ContinuousLinearMap.norm_compLp_le _ _
      _ ≤ C*‖hG.toLp G‖ := by
        rw [ContinuousLinearMap.norm_toSpanSingleton]
        exact mul_le_mul (hvb x) (hFb x) (norm_nonneg _) hC
  have hUi : Integrable U μ := Integrable.of_bound hUm.aestronglyMeasurable (C*‖hG.toLp G‖)
    (ae_of_all μ hUb)
  have hm := closed_derivative_integral μ D hD F U hFm hUm hFi hUi hgraph
  have he := l2_bochner_integral_pointwise μ P S hSm hSL hFi
  have hi : MemLp (fun w => ∫ x,S (x,w) ∂μ) 2 P := (Lp.memLp (∫ x,F x ∂μ)).ae_eq he
  refine ⟨hi,?_⟩
  have he' : hi.toLp _ = ∫ x,F x ∂μ := Lp.ext (hi.coeFn_toLp.trans he.symm)
  rwa [he']

end Asakura.Chapter12
