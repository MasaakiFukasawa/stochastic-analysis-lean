import Chapter12GraphClosure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- Integration commutes with a closed derivative when the value and its
derivative are integrable together. This uses completeness of the graph,
not boundedness of D for the value norm alone. -/
theorem closed_derivative_integral {α E H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (μ : Measure α) (D : E →ₗ.[ℝ] H) (hD : D.IsClosed)
    (F : α → E) (U : α → H) (hF : StronglyMeasurable F) (hU : StronglyMeasurable U)
    (hFi : Integrable F μ) (hUi : Integrable U μ)
    (hFU : ∀ x, (F x,U x) ∈ D.graph) :
    (∫ x,F x ∂μ,∫ x,U x ∂μ) ∈ D.graph := by
  letI : CompleteSpace D.graph := hD.isComplete.completeSpace_coe
  let G : α → D.graph := fun x => ⟨(F x,U x),hFU x⟩
  have hm : StronglyMeasurable G := by
    apply (Embedding.comp_stronglyMeasurable_iff Topology.IsEmbedding.subtypeVal).mp
    exact hF.prodMk hU
  have hi : Integrable G μ := ⟨hm.aestronglyMeasurable,(hFi.prodMk hUi).hasFiniteIntegral⟩
  have he := D.graph.subtypeL.integral_comp_comm hi
  change (∫ x,(F x,U x) ∂μ) = ((∫ x,G x ∂μ : D.graph) : E × H) at he
  rw [integral_pair hFi hUi] at he
  rw [he]
  exact (∫ x,G x ∂μ : D.graph).property

end Asakura.Chapter12
