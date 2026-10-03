import FullAuditNaturalFiltration
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set Filter
namespace Asakura.Chapter7
open Asakura.FullAudit
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def productSigma {Ω Γ : Type*} (G : MeasurableSpace Ω) (H : MeasurableSpace Γ) :
    MeasurableSpace (Ω × Γ) := @Prod.instMeasurableSpace Ω Γ G H

lemma product_sigma_mono {Ω Γ : Type*} {G G' : MeasurableSpace Ω} {H H' : MeasurableSpace Γ}
    (hG : G ≤ G') (hH : H ≤ H') : productSigma G H ≤ productSigma G' H' :=
  sup_le_sup (MeasurableSpace.comap_mono hG) (MeasurableSpace.comap_mono hH)

/-- Adding an independent probability coordinate preserves conditional
expectations of the original variables, even when both coordinate
filtrations are retained. This is the measure-theoretic step needed for
the independent Brownian-tail extension in the functional CLT. -/
theorem product_conditional_fst
    {Ω Γ : Type*} [m : MeasurableSpace Ω] [n : MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (G : MeasurableSpace Ω) (H : MeasurableSpace Γ) (hG : G ≤ m) (hH : H ≤ n)
    (f : Ω → ℝ) (hf : Integrable f P) :
    ((@Measure.prod Ω Γ m n P Q))[(fun z => f z.1)|productSigma G H] =ᵐ[(@Measure.prod Ω Γ m n P Q)]
      (fun z => P[f|G] z.1) := by
  letI : MeasurableSpace Ω := m
  letI : MeasurableSpace Γ := n
  have hle := product_sigma_mono hG hH
  have hi : Integrable (fun z : Ω × Γ => P[f|G] z.1) ((@Measure.prod Ω Γ m n P Q)) := integrable_condExp.comp_fst Q
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hle (hf.comp_fst Q)
    (fun E _ _ => hi.integrableOn) _
    ((stronglyMeasurable_condExp (μ := P) (m := G) (f := f)).comp_measurable
      (@measurable_fst Ω Γ G H)).aestronglyMeasurable
  intro E hE _
  have hEa : MeasurableSet[productSigma m n] E := hle E hE
  rw [← integral_indicator hEa,← integral_indicator hEa,
    integral_prod_symm _ (hi.indicator hEa),integral_prod_symm _ ((hf.comp_fst Q).indicator hEa)]
  apply integral_congr_ae
  apply ae_of_all
  intro b
  have hsec : MeasurableSet[G] {a | (a,b) ∈ E} :=
    hE.preimage (@measurable_prodMk_right Ω Γ G H b)
  change (∫ a,({a | (a,b) ∈ E}).indicator (P[f|G]) a ∂P) =
    ∫ a,({a | (a,b) ∈ E}).indicator f a ∂P
  rw [integral_indicator (hG _ hsec),integral_indicator (hG _ hsec)]
  exact setIntegral_condExp hG hf hsec

theorem product_conditional_snd
    {Ω Γ : Type*} [m : MeasurableSpace Ω] [n : MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (G : MeasurableSpace Ω) (H : MeasurableSpace Γ) (hG : G ≤ m) (hH : H ≤ n)
    (f : Γ → ℝ) (hf : Integrable f Q) :
    ((@Measure.prod Ω Γ m n P Q))[(fun z => f z.2)|productSigma G H] =ᵐ[(@Measure.prod Ω Γ m n P Q)]
      (fun z => Q[f|H] z.2) := by
  letI : MeasurableSpace Ω := m
  letI : MeasurableSpace Γ := n
  have hle := product_sigma_mono hG hH
  have hi : Integrable (fun z : Ω × Γ => Q[f|H] z.2) ((@Measure.prod Ω Γ m n P Q)) := integrable_condExp.comp_snd P
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hle (hf.comp_snd P)
    (fun E _ _ => hi.integrableOn) _
    ((stronglyMeasurable_condExp (μ := Q) (m := H) (f := f)).comp_measurable
      (@measurable_snd Ω Γ G H)).aestronglyMeasurable
  intro E hE _
  have hEa : MeasurableSet[productSigma m n] E := hle E hE
  rw [← integral_indicator hEa,← integral_indicator hEa,
    integral_prod _ (hi.indicator hEa),integral_prod _ ((hf.comp_snd P).indicator hEa)]
  apply integral_congr_ae
  apply ae_of_all
  intro a
  have hsec : MeasurableSet[H] {b | (a,b) ∈ E} :=
    hE.preimage (@measurable_prodMk_left Ω Γ G H a)
  change (∫ b,({b | (a,b) ∈ E}).indicator (Q[f|H]) b ∂Q) =
    ∫ b,({b | (a,b) ∈ E}).indicator f b ∂Q
  rw [integral_indicator (hH _ hsec),integral_indicator (hH _ hsec)]
  exact setIntegral_condExp hH hf hsec

end Asakura.Chapter7
