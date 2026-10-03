import Chapter2DifferentiableVariationExample
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete

/-- The displayed fundamental-calculus decomposition in the C1 example.
Derivatives are only needed in the interior of the finite interval. -/
theorem differentiable_variation_printed_formula
    (A D : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hA : ContinuousOn A (Icc 0 b)) (hD : ContinuousOn D (Icc 0 b))
    (hd : ∀ r ∈ Ioo 0 b, HasDerivAt A (D r) r) :
    (∀ t ∈ Icc 0 b, A t = A 0 + (∫ r in (0:ℝ)..t, max (D r) 0) -
      (∫ r in (0:ℝ)..t, max (-D r) 0)) ∧
    MonotoneOn (fun t => ∫ r in (0:ℝ)..t, max (D r) 0) (Icc 0 b) ∧
    MonotoneOn (fun t => ∫ r in (0:ℝ)..t, max (-D r) 0) (Icc 0 b) := by
  have hi (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 b)) (t : ℝ) (ht : t ∈ Icc 0 b) :
      IntervalIntegrable f volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 (hf.mono (Icc_subset_Icc le_rfl ht.2))
  have hm (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 b)) (hp : ∀ r, 0 ≤ f r) :
      MonotoneOn (fun t => ∫ r in (0:ℝ)..t, f r) (Icc 0 b) := by
    intro s hs t ht hst
    exact intervalIntegral.integral_mono_interval le_rfl hs.1 hst
      (.of_forall hp) (hi f hf t ht)
  refine ⟨?_,hm _ (hD.sup continuousOn_const) (fun _ => le_max_right _ _),
    hm _ (hD.neg.sup continuousOn_const) (fun _ => le_max_right _ _)⟩
  intro t ht
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hA.mono (Icc_subset_Icc le_rfl ht.2))
    (fun r hr => hd r ⟨hr.1,hr.2.trans_le ht.2⟩) (hi D hD t ht)
  have hdiff : (fun r => max (D r) 0-max (-D r) 0) = D := by
    funext r
    rcases le_total 0 (D r) with hr | hr
    · rw [max_eq_left hr,max_eq_right (neg_nonpos.mpr hr),sub_zero]
    · rw [max_eq_right hr,max_eq_left (neg_nonneg.mpr hr)]
      ring
  have hs := intervalIntegral.integral_sub
    (hi (fun r => max (D r) 0) (hD.sup continuousOn_const) t ht)
      (hi (fun r => max (-D r) 0) (hD.neg.sup continuousOn_const) t ht)
  change (∫ r in (0:ℝ)..t, max (D r) 0-max (-D r) 0) = _ at hs
  rw [hdiff,he] at hs
  linarith

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.differentiable_variation_printed_formula
