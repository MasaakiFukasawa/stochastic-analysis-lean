import Chapter9GaussianSmoothness

open Set MeasureTheory
open scoped ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] ContinuousMultilinearMap.seminormedAddCommGroup ContinuousMultilinearMap.seminormedAddCommGroup'

theorem ou_kernel_jets_integrable {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ]
    (n : ℕ) (z : ℝ × (Fin d → ℝ)) (hz : 0<z.1) :
    Integrable (fun x => iteratedFDeriv ℝ n (fun q => Real.exp (ouExponent x q)) z) μ := by
  have hU : IsOpen {q : ℝ × (Fin d → ℝ) | 0<q.1} := isOpen_lt continuous_const continuous_fst
  have he (x : Fin d → ℝ) := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun q => Real.exp (ouExponent x q)) n hU hz
  have hKU : ({z} : Set (ℝ × (Fin d → ℝ))) ⊆ {q | 0<q.1} := by simpa
  obtain ⟨B,hB,hbound⟩ := ou_kernel_all_order_compact_bound {z} isCompact_singleton hKU n
  have hi : Integrable (fun x => iteratedFDerivWithin ℝ n
      (fun q => Real.exp (ouExponent x q)) {q | 0<q.1} z) μ :=
    (integrable_const B).mono' (ou_kernel_jets_continuous n z hz).aestronglyMeasurable
      (ae_of_all _ (fun x => hbound x z (mem_singleton _)))
  simpa only [he] using hi

theorem ou_mixture_jet_apply {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ]
    (n : ℕ) (z : ℝ × (Fin d → ℝ)) (hz : 0<z.1) (h : Fin n → ℝ × (Fin d → ℝ)) :
    iteratedFDeriv ℝ n (fun q => ∫ x,Real.exp (ouExponent x q) ∂μ) z h=
      ∫ x,iteratedFDeriv ℝ n (fun q => Real.exp (ouExponent x q)) z h ∂μ := by
  have hU : IsOpen {q : ℝ × (Fin d → ℝ) | 0<q.1} := isOpen_lt continuous_const continuous_fst
  have he := ou_gaussian_mixture_derivative μ n z hz
  simp_rw [iteratedFDerivWithin_of_isOpen n hU hz] at he
  rw [he,ContinuousMultilinearMap.integral_apply (ou_kernel_jets_integrable μ n z hz)]

theorem ou_kernel_jet_apply_integrable {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ]
    (n : ℕ) (z : ℝ × (Fin d → ℝ)) (hz : 0<z.1) (h : Fin n → ℝ × (Fin d → ℝ)) :
    Integrable (fun x => iteratedFDeriv ℝ n (fun q => Real.exp (ouExponent x q)) z h) μ :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℝ × (Fin d → ℝ)) ℝ h).integrable_comp
    (ou_kernel_jets_integrable μ n z hz)
end Asakura.Chapter9
