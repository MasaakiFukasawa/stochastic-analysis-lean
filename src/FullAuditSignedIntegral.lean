import ManuscriptDominated
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.FullAudit

/-- The simple-function step of independence of the signed-measure decomposition.
The equality on measurable sets is precisely equality of the two signed measures. -/
theorem signed_decomposition_simple {Ω : Type*} [MeasurableSpace Ω]
    (μ₁ μ₂ ν₁ ν₂ : Measure Ω)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (heq : ∀ E, MeasurableSet E → μ₁.real E-μ₂.real E=ν₁.real E-ν₂.real E)
    (f : SimpleFunc Ω ℝ) :
    (∫ x, f x ∂μ₁)-(∫ x, f x ∂μ₂) = (∫ x, f x ∂ν₁)-(∫ x, f x ∂ν₂) := by
  classical
  rw [f.integral_eq_sum f.integrable_of_isFiniteMeasure,
      f.integral_eq_sum f.integrable_of_isFiniteMeasure,
      f.integral_eq_sum f.integrable_of_isFiniteMeasure,
      f.integral_eq_sum f.integrable_of_isFiniteMeasure]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  simp only [smul_eq_mul]
  have h := heq (f ⁻¹' {y}) (f.measurableSet_fiber y)
  rw [← sub_mul, ← sub_mul, h]

/-- DCT applied separately to each positive measure, after a common simple approximation.
The library's approximation is bounded by 2|f|, which gives the same domination argument. -/
theorem signed_decomposition_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ₁ μ₂ ν₁ ν₂ : Measure Ω)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (heq : ∀ E, MeasurableSet E → μ₁.real E-μ₂.real E=ν₁.real E-ν₂.real E)
    (f : Ω → ℝ) (hf : Measurable f)
    (hf₁ : Integrable f μ₁) (hf₂ : Integrable f μ₂)
    (hg₁ : Integrable f ν₁) (hg₂ : Integrable f ν₂) :
    (∫ x, f x ∂μ₁)-(∫ x, f x ∂μ₂) = (∫ x, f x ∂ν₁)-(∫ x, f x ∂ν₂) := by
  let a : ℕ → SimpleFunc Ω ℝ := SimpleFunc.approxOn f hf univ 0 (mem_univ 0)
  have hconv (μ : Measure Ω) (hfi : Integrable f μ) :
      Tendsto (fun n => ∫ x, a n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    apply Asakura.manuscript_dominated_convergence μ (fun n x => a n x) f
      (fun x => ‖f x‖+‖f x‖) (fun n => (a n).measurable) hf
      (hf.norm.add hf.norm) (hfi.norm.add hfi.norm)
    · intro n
      exact Eventually.of_forall (fun x => SimpleFunc.norm_approxOn_zero_le hf (mem_univ 0) x n)
    · exact Eventually.of_forall (fun x => SimpleFunc.tendsto_approxOn hf
        (mem_univ 0) (by simp))
  have hleft := (hconv μ₁ hf₁).sub (hconv μ₂ hf₂)
  have hright := (hconv ν₁ hg₁).sub (hconv ν₂ hg₂)
  have hn : (fun n => (∫ x, a n x ∂μ₁)-(∫ x, a n x ∂μ₂)) =
      (fun n => (∫ x, a n x ∂ν₁)-(∫ x, a n x ∂ν₂)) := by
    funext n
    exact signed_decomposition_simple μ₁ μ₂ ν₁ ν₂ heq (a n)
  rw [hn] at hleft
  exact tendsto_nhds_unique hleft hright

/-- For the Jordan pair it suffices to assume integrability for the supplied
positive decomposition, using total variation domination as in the manuscript. -/
theorem signed_integral_independent_written {Ω : Type*} [MeasurableSpace Ω]
    (μ₁ μ₂ ν₁ ν₂ : Measure Ω)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (heq : ∀ E, MeasurableSet E → μ₁.real E-μ₂.real E=ν₁.real E-ν₂.real E)
    (hdom : ν₁+ν₂ ≤ μ₁+μ₂)
    (f : Ω → ℝ) (hf : Measurable f) (hfi : Integrable f (μ₁+μ₂)) :
    (∫ x, f x ∂ν₁)-(∫ x, f x ∂ν₂) = (∫ x, f x ∂μ₁)-(∫ x, f x ∂μ₂) := by
  have hν : Integrable f (ν₁+ν₂) := hfi.mono_measure hdom
  obtain ⟨hf₁,hf₂⟩ := integrable_add_measure.mp hfi
  obtain ⟨hg₁,hg₂⟩ := integrable_add_measure.mp hν
  exact (signed_decomposition_integral μ₁ μ₂ ν₁ ν₂ heq f hf hf₁ hf₂ hg₁ hg₂).symm

end Asakura.FullAudit
