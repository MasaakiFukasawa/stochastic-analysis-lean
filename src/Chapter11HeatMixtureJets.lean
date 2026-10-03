import Chapter11WeightedHeatSmooth

open Set MeasureTheory
open scoped ContDiff
namespace Asakura.Chapter11
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] ContinuousMultilinearMap.seminormedAddCommGroup ContinuousMultilinearMap.seminormedAddCommGroup'

theorem weighted_heat_jets_integrable (L : ℝ) (hL : 0<L) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (z : ℝ × (ℝ)) (hz : 0<z.1 ∧ z.1<L) :
    Integrable (fun x => iteratedFDeriv ℝ n (fun q => Real.exp (weightedHeatExponent L x q)) z) μ := by
  have hU : IsOpen {q : ℝ × ℝ | 0<q.1 ∧ q.1<L} := (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
  have he (x : ℝ) := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun q => Real.exp (weightedHeatExponent L x q)) n hU hz
  have hKU : ({z} : Set (ℝ × (ℝ))) ⊆ {q : ℝ × ℝ | 0<q.1 ∧ q.1<L} := by simpa
  obtain ⟨B,hB,hbound⟩ := weighted_heat_all_order_bound L hL {z} isCompact_singleton hKU n
  have hi : Integrable (fun x => iteratedFDerivWithin ℝ n
      (fun q => Real.exp (weightedHeatExponent L x q)) {q : ℝ × ℝ | 0<q.1 ∧ q.1<L} z) μ :=
    (integrable_const B).mono' (weighted_heat_jets_continuous L n z hz).aestronglyMeasurable
      (ae_of_all _ (fun x => hbound x z (mem_singleton _)))
  simpa only [he] using hi

theorem weighted_heat_mixture_jet_apply (L : ℝ) (hL : 0<L) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (z : ℝ × (ℝ)) (hz : 0<z.1 ∧ z.1<L) (h : Fin n → ℝ × (ℝ)) :
    iteratedFDeriv ℝ n (fun q => ∫ x,Real.exp (weightedHeatExponent L x q) ∂μ) z h=
      ∫ x,iteratedFDeriv ℝ n (fun q => Real.exp (weightedHeatExponent L x q)) z h ∂μ := by
  have hU : IsOpen {q : ℝ × ℝ | 0<q.1 ∧ q.1<L} := (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
  have he := weighted_heat_mixture_derivative L hL μ n z hz
  simp_rw [iteratedFDerivWithin_of_isOpen n hU hz] at he
  rw [he,ContinuousMultilinearMap.integral_apply (weighted_heat_jets_integrable L hL μ n z hz)]

theorem weighted_heat_jet_apply_integrable (L : ℝ) (hL : 0<L) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (z : ℝ × (ℝ)) (hz : 0<z.1 ∧ z.1<L) (h : Fin n → ℝ × (ℝ)) :
    Integrable (fun x => iteratedFDeriv ℝ n (fun q => Real.exp (weightedHeatExponent L x q)) z h) μ :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℝ × (ℝ)) ℝ h).integrable_comp
    (weighted_heat_jets_integrable L hL μ n z hz)
end Asakura.Chapter11
