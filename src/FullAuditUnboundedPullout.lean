import FullAuditConditionalExercises
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Supplement needed when the measurable factor in C3 is unbounded.
 Cover by measurable sets on which it is bounded, use bounded C3 under
 restriction, and then recover the full equality on their union. -/
theorem unbounded_pullout_by_restriction {Ω : Type*} {G m : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] (hG : G ≤ m)
    (f g : Ω → ℝ) (hf : StronglyMeasurable[G] f)
    (hfg : Integrable (f*g) P) (hg : Integrable g P) :
    P[f*g|G] =ᵐ[P] f*P[g|G] := by
  letI : MeasurableSpace Ω := m
  obtain ⟨A,hA,hcover⟩ := hf.exists_spanning_measurableSet_norm_le hG P
  simp_rw [forall_and] at hA
  obtain ⟨hAm,hAfin,hAb⟩ := hA
  have hlocal (n : ℕ) : ∀ᵐ ω ∂P.restrict (A n),
      P[f*g|G] ω = f ω*P[g|G] ω := by
    have hbound : ∀ᵐ ω ∂P.restrict (A n), ‖(A n).indicator f ω‖ ≤ (n:ℝ) := by
      apply ae_of_all _
      intro ω
      by_cases hω : ω ∈ A n
      · simpa only [indicator_of_mem hω] using hAb n ω hω
      · simp [hω]
    have h := condExp_stronglyMeasurable_mul_of_bound (μ := P.restrict (A n)) hG
      (hf.indicator (hAm n)) hg.integrableOn (n:ℝ) hbound
    have hif : (A n).indicator f =ᵐ[P.restrict (A n)] f :=
      indicator_ae_eq_restrict (f := f) (hG _ (hAm n))
    have hprod : ((A n).indicator f)*g =ᵐ[P.restrict (A n)] f*g :=
      hif.mul (EventuallyEq.refl _ _)
    have hce := condExp_congr_ae (m := G) hprod
    have hr1 := condExp_restrict_ae_eq_restrict hG (hAm n) hfg
    have hr2 := condExp_restrict_ae_eq_restrict hG (hAm n) hg
    filter_upwards [h,hce,hif,hr1,hr2] with ω hh hc hi h1 h2
    change P[f*g|G] ω = f ω*P[g|G] ω
    change (P.restrict (A n))[((A n).indicator f)*g|G] ω =
      (A n).indicator f ω*(P.restrict (A n))[g|G] ω at hh
    rw [← h1,← hc,hh,hi,h2]
  have hglobal (n : ℕ) : ∀ᵐ ω ∂P, ω ∈ A n → P[f*g|G] ω = f ω*P[g|G] ω :=
    ae_imp_of_ae_restrict (hlocal n)
  filter_upwards [ae_all_iff.mpr hglobal] with ω hω
  have hm : ω ∈ ⋃ n, A n := by rw [hcover]; trivial
  obtain ⟨n,hn⟩ := mem_iUnion.mp hm
  exact hω n hn

theorem unbounded_pullout_right {Ω : Type*} {G m : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] (hG : G ≤ m)
    (f g : Ω → ℝ) (hg : StronglyMeasurable[G] g)
    (hfg : Integrable (f*g) P) (hf : Integrable f P) :
    P[f*g|G] =ᵐ[P] P[f|G]*g := by
  have h := unbounded_pullout_by_restriction P hG g f hg (by simpa only [mul_comm] using hfg) hf
  simpa only [mul_comm] using h

end Asakura.FullAudit
