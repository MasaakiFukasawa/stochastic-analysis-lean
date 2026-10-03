import Chapter3WrittenLimits
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open MeasureTheory Set
open scoped Topology
namespace Asakura.FullAudit

/-- Integrating-factor argument, with a globally continuous representative.
The zero/nonzero drift cases are separated by b>0, exactly as in the manuscript. -/
theorem ch4_gronwall_global (u : ℝ → ℝ) (hu : Continuous u)
    (a b T : ℝ) (hb : 0 < b) (hT : 0 ≤ T)
    (hineq : ∀ t ∈ Icc 0 T, u t ≤ a + b * ∫ s in 0..t, u s) :
    ∀ t ∈ Icc 0 T, u t ≤ a * Real.exp (b*t) := by
  let v : ℝ → ℝ := fun t => a + b * ∫ s in 0..t, u s
  have hv (t : ℝ) : HasDerivAt v (b * u t) t := by
    simpa [v] using ((intervalIntegral.integral_hasDerivAt_right
      (hu.intervalIntegrable 0 t) hu.stronglyMeasurable.stronglyMeasurableAtFilter
      hu.continuousAt).const_mul b).const_add a
  let w : ℝ → ℝ := fun t => Real.exp (-b*t) * v t
  have hw (t : ℝ) : HasDerivAt w
      (Real.exp (-b*t) * b * (u t-v t)) t := by
    convert ((((hasDerivAt_id t).const_mul (-b)).exp).mul (hv t)) using 1 <;>
      first | rfl | (dsimp only [id]; ring)
  have hwcont : Continuous w := continuous_iff_continuousAt.mpr (fun x => (hw x).continuousAt)
  have hanti : AntitoneOn w (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hwcont.continuousOn
    · intro x hx
      exact (hw x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hw x).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos
      · positivity
      · exact sub_nonpos.mpr (hineq x (interior_subset hx))
  intro t ht
  have hwt := hanti (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩) ht ht.1
  have hw0 : w 0 = a := by simp [w,v]
  rw [hw0] at hwt
  have hprod := mul_le_mul_of_nonneg_left hwt (le_of_lt (Real.exp_pos (b*t)))
  have hexp : Real.exp (b*t) * Real.exp (-b*t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> congr 1 <;> ring
  change Real.exp (b*t) * (Real.exp (-b*t)*v t) ≤ _ at hprod
  rw [← mul_assoc, hexp, one_mul] at hprod
  exact (hineq t ht).trans (by simpa [mul_comm] using hprod)

/-- The manuscript's Gronwall lemma on its actual compact domain. We extend
u by constant endpoint values solely to apply the ordinary FTC. -/
theorem ch4_gronwall_written (u : ℝ → ℝ) (a b T : ℝ)
    (hT : 0 ≤ T) (hu : ContinuousOn u (Icc 0 T))
    (hb : 0 < b)
    (hineq : ∀ t ∈ Icc 0 T, u t ≤ a+b*∫ s in 0..t, u s) :
    ∀ t ∈ Icc 0 T, u t ≤ a*Real.exp (b*t) := by
  let c : ℝ → ℝ := fun x => max 0 (min T x)
  have hc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcmem (x : ℝ) : c x ∈ Icc 0 T := by
    exact ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩
  have hceq (x : ℝ) (hx : x ∈ Icc 0 T) : c x = x := by
    simp [c, min_eq_right hx.2, max_eq_right hx.1]
  have hext : Continuous (u ∘ c) := hu.comp_continuous hc hcmem
  have hint (t : ℝ) (ht : t ∈ Icc 0 T) :
      (∫ s in 0..t, (u ∘ c) s) = ∫ s in 0..t, u s := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc 0 t := by simpa [uIcc_of_le ht.1] using hx
    simp only [Function.comp_apply, hceq x ⟨hx'.1, hx'.2.trans ht.2⟩]
  have hbound := ch4_gronwall_global (u ∘ c) hext a b T hb hT (by
    intro t ht
    change u (c t) ≤ a + b * ∫ s in 0..t, (u ∘ c) s
    rw [hceq t ht, hint t ht]
    exact hineq t ht)
  intro t ht
  simpa [Function.comp_apply,hceq t ht] using hbound t ht

end Asakura.FullAudit
