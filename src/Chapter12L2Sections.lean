import Chapter2L2SectionIntegrable
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- The Hilbert-valued section of a square-integrable joint function has the
same squared norm. This is the Fubini identification used for DF. -/
theorem l2_sections_isometry {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [SigmaFinite P] (ν : Measure S) [SigmaFinite ν]
    (f : Ω × S → ℝ) (hf : Measurable f) (hL : MemLp f 2 (P.prod ν)) :
    MemLp (l2Section ν f) 2 P ∧
      (∀ᵐ w ∂P, (l2Section ν f w : S → ℝ) =ᵐ[ν] (fun s => f (w,s))) ∧
      (∫ w, ‖l2Section ν f w‖^2 ∂P) = ∫ z, f z^2 ∂P.prod ν := by
  have hi := hL.integrable_sq
  have hsec : ∀ᵐ w ∂P, MemLp (fun s => f (w,s)) 2 ν := by
    filter_upwards [hi.prod_right_ae] with w hw
    exact (memLp_two_iff_integrable_sq
      (hf.comp measurable_prodMk_left).aestronglyMeasurable).2 hw
  have hcoe : ∀ᵐ w ∂P, (l2Section ν f w : S → ℝ) =ᵐ[ν] (fun s => f (w,s)) := by
    filter_upwards [hsec] with w hw
    simpa only [l2Section,dif_pos hw] using hw.coeFn_toLp
  have hn : (fun w => ‖l2Section ν f w‖^2) =ᵐ[P] (fun w => ∫ s, f (w,s)^2 ∂ν) := by
    filter_upwards [hcoe] with w hw
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hw] with s hs
    simp only [hs,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  have hmem : MemLp (l2Section ν f) 2 P := by
    apply (memLp_two_iff_integrable_sq_norm
      (stronglyMeasurable_l2Section ν f hf).aestronglyMeasurable).2
    exact hi.integral_prod_left.congr hn.symm
  exact ⟨hmem,hcoe,(integral_congr_ae hn).trans (integral_prod (fun z => f z^2) hi).symm⟩

/-- Inner products also agree with the joint-space integral, so testing DF
against step processes can be done in either realization of L2. -/
theorem l2_sections_inner {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [SigmaFinite P] (ν : Measure S) [SigmaFinite ν]
    (f g : Ω × S → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hL : MemLp f 2 (P.prod ν)) (hG : MemLp g 2 (P.prod ν)) :
    (∫ w, inner ℝ (l2Section ν f w) (l2Section ν g w) ∂P) =
      ∫ z, f z*g z ∂P.prod ν := by
  obtain ⟨_,hfc,_⟩ := l2_sections_isometry P ν f hf hL
  obtain ⟨_,hgc,_⟩ := l2_sections_isometry P ν g hg hG
  have hi : Integrable (fun z => f z*g z) (P.prod ν) := hL.integrable_mul hG
  calc
    _ = ∫ w, ∫ s, f (w,s)*g (w,s) ∂ν ∂P := by
      apply integral_congr_ae
      filter_upwards [hfc,hgc] with w hw hv
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hw,hv] with t ht hs
      rw [ht,hs]
      change g (w,t)*f (w,t) = f (w,t)*g (w,t)
      ring
    _ = _ := (integral_prod _ hi).symm

end Asakura.Chapter12
