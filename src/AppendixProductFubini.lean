import Mathlib.MeasureTheory.Integral.Prod
import FullAuditMonotoneClass

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.AppendixProduct

/-- Appendix A.5: measurable set sections. -/
theorem measurable_sections {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (Q : Set (X × Y)) (hQ : MeasurableSet Q) :
    (∀ x, MeasurableSet {y | (x,y) ∈ Q}) ∧
    (∀ y, MeasurableSet {x | (x,y) ∈ Q}) := by
  exact ⟨fun _ => measurable_prodMk_left hQ, fun _ => measurable_prodMk_right hQ⟩

/-- Appendix A.5: measurable real function sections. -/
theorem measurable_function_sections {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X × Y → ℝ) (hf : Measurable f) :
    (∀ x, Measurable (fun y => f (x,y))) ∧
    (∀ y, Measurable (fun x => f (x,y))) := by
  exact ⟨fun _ => hf.comp measurable_prodMk_left, fun _ => hf.comp measurable_prodMk_right⟩

/-- The product measure is sigma finite and agrees with rectangle products. -/
theorem product_measure_properties {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν] :
    SigmaFinite (μ.prod ν) ∧ ∀ A B, μ.prod ν (A ×ˢ B) = μ A * ν B := by
  exact ⟨inferInstance, fun A B => Measure.prod_prod A B⟩

/-- The set-section construction agrees in both orders with the product measure. -/
theorem product_measure_sections {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (Q : Set (X × Y)) (hQ : MeasurableSet Q) :
    Measurable (fun x => ν {y | (x,y) ∈ Q}) ∧
    Measurable (fun y => μ {x | (x,y) ∈ Q}) ∧
    μ.prod ν Q = ∫⁻ x, ν {y | (x,y) ∈ Q} ∂μ ∧
    μ.prod ν Q = ∫⁻ y, μ {x | (x,y) ∈ Q} ∂ν := by
  exact ⟨measurable_measure_prodMk_left hQ, measurable_measure_prodMk_right hQ,
    Measure.prod_apply hQ, Measure.prod_apply_symm hQ⟩

/-- Tonelli, including measurability of both partial integrals, infinite values allowed. -/
theorem tonelli {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (f : X × Y → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun x => ∫⁻ y, f (x,y) ∂ν) ∧
    Measurable (fun y => ∫⁻ x, f (x,y) ∂μ) ∧
    (∫⁻ z, f z ∂μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x,y) ∂ν ∂μ ∧
    (∫⁻ z, f z ∂μ.prod ν) = ∫⁻ y, ∫⁻ x, f (x,y) ∂μ ∂ν := by
  exact ⟨hf.lintegral_prod_right', hf.lintegral_prod_left',
    lintegral_prod _ hf.aemeasurable, (lintegral_prod _ hf.aemeasurable).trans
      (lintegral_lintegral_swap hf.aemeasurable)⟩

/-- Fubini, with integrable sections outside null sets and integrable partial integrals.
Lean's Bochner integral is zero for a nonintegrable section, matching the manuscript's convention. -/
theorem fubini {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (f : X × Y → ℝ) (hf : Integrable f (μ.prod ν)) :
    (∀ᵐ x ∂μ, Integrable (fun y => f (x,y)) ν) ∧
    (∀ᵐ y ∂ν, Integrable (fun x => f (x,y)) μ) ∧
    Integrable (fun x => ∫ y, f (x,y) ∂ν) μ ∧
    Integrable (fun y => ∫ x, f (x,y) ∂μ) ν ∧
    (∫ z, f z ∂μ.prod ν) = ∫ x, ∫ y, f (x,y) ∂ν ∂μ ∧
    (∫ z, f z ∂μ.prod ν) = ∫ y, ∫ x, f (x,y) ∂μ ∂ν := by
  exact ⟨hf.prod_right_ae, hf.prod_left_ae, hf.integral_prod_left, hf.integral_prod_right,
    integral_prod f hf, (integral_prod f hf).trans (integral_integral_swap hf)⟩

end Asakura.AppendixProduct
