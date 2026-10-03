import Chapter2RandomStieltjes
import Mathlib.Probability.Kernel.MeasurableLIntegral

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

/-- The joint measure exists even when the finite pathwise masses have
infinite expectation; a uniform finite-kernel bound is not assumed. -/
noncomputable def finiteKernelProduct (P : Measure Ω) (κ : Kernel Ω S)
    (hκ : ∀ ω, IsFiniteMeasure (κ ω)) : Measure (Ω × S) :=
  P.bind (fun ω => (κ ω).map (Prod.mk ω))

theorem finite_kernel_joint_measurable (κ : Kernel Ω S)
    (hκ : ∀ ω, IsFiniteMeasure (κ ω)) :
    Measurable (fun ω => (κ ω).map (Prod.mk ω)) := by
  apply Measure.measurable_of_measurable_coe
  intro B hB
  simp_rw [Measure.map_apply measurable_prodMk_left hB]
  exact Kernel.measurable_kernel_prodMk_left_of_finite hB hκ

theorem finite_kernel_product_apply (P : Measure Ω) (κ : Kernel Ω S)
    (hκ : ∀ ω, IsFiniteMeasure (κ ω)) (B : Set (Ω × S)) (hB : MeasurableSet B) :
    finiteKernelProduct P κ hκ B = ∫⁻ ω, κ ω (Prod.mk ω ⁻¹' B) ∂P := by
  rw [finiteKernelProduct,Measure.bind_apply hB (finite_kernel_joint_measurable κ hκ).aemeasurable]
  simp_rw [Measure.map_apply measurable_prodMk_left hB]

theorem finite_kernel_product_lintegral (P : Measure Ω) (κ : Kernel Ω S)
    (hκ : ∀ ω, IsFiniteMeasure (κ ω)) (f : Ω × S → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂finiteKernelProduct P κ hκ) = ∫⁻ ω, ∫⁻ r, f (ω,r) ∂κ ω ∂P := by
  rw [finiteKernelProduct,Measure.lintegral_bind (finite_kernel_joint_measurable κ hκ).aemeasurable hf.aemeasurable]
  congr 1
  funext ω
  exact lintegral_map hf measurable_prodMk_left

/-- Sigma-finiteness follows by partitioning according to each path's
finite total mass. No expected quadratic-variation bound is imposed. -/
theorem finite_kernel_product_sigmaFinite (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : Kernel Ω S) (hκ : ∀ ω, IsFiniteMeasure (κ ω)) :
    SigmaFinite (finiteKernelProduct P κ hκ) := by
  let B := fun n : ℕ => {ω | κ ω univ ≤ (n:ℝ≥0∞)} ×ˢ (univ : Set S)
  have hm n : MeasurableSet (B n) :=
    (measurableSet_le (κ.measurable_coe MeasurableSet.univ) measurable_const).prod MeasurableSet.univ
  refine ⟨B,fun _ => mem_univ _,?_,?_⟩
  · intro n
    rw [finite_kernel_product_apply P κ hκ (B n) (hm n)]
    apply lt_of_le_of_lt (b := (n:ℝ≥0∞)) _ (by simp)
    calc
      (∫⁻ ω, κ ω (Prod.mk ω ⁻¹' B n) ∂P) ≤ ∫⁻ _ : Ω, (n:ℝ≥0∞) ∂P := by
        apply lintegral_mono
        intro ω
        by_cases hω : κ ω univ ≤ (n:ℝ≥0∞)
        · simpa [B,hω] using hω
        · simp [B,hω]
      _ = (n:ℝ≥0∞) := by simp
  · apply Set.eq_univ_of_forall
    intro z
    have hn : κ z.1 univ < ∞ := (hκ z.1).measure_univ_lt_top
    obtain ⟨n,hn⟩ := ENNReal.exists_nat_gt hn.ne
    exact mem_iUnion.mpr ⟨n,⟨hn.le,mem_univ _⟩⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.finite_kernel_product_sigmaFinite
#print axioms Asakura.Chapter2Complete.finite_kernel_product_lintegral
