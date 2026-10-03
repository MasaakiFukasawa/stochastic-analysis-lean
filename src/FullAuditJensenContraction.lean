import Chapter1WrittenJensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- Convexity of precisely the power of the absolute value used in the proof. -/
theorem norm_rpow_convex (p : ℝ) (hp : 1 ≤ p) : ConvexOn ℝ univ (fun x : ℝ => ‖x‖^p) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  have hn := (convexOn_univ_norm (E := ℝ)).2 hx hy ha hb hab
  have hpow := (convexOn_rpow hp).2 (norm_nonneg x) (norm_nonneg y) ha hb hab
  exact (Real.rpow_le_rpow (norm_nonneg _) hn (by linarith)).trans hpow

/-- The finite-p branch applies the manuscript's own rational-line Jensen proof,
then integrates; the Lp result is not supplied as an input. -/
theorem conditional_norm_power_written {Ω : Type*} {m G : MeasurableSpace Ω}
    (P : @Measure Ω m) [IsProbabilityMeasure P] (hG : G ≤ m)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞) (X : Ω → ℝ) (hX : MemLp X p P) :
    Integrable (fun ω => ‖P[X | G] ω‖^p.toReal) P ∧
      (∫ ω, ‖P[X | G] ω‖^p.toReal ∂P) ≤ ∫ ω, ‖X ω‖^p.toReal ∂P := by
  letI : MeasurableSpace Ω := m
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le hp)
  have hpR : 1 ≤ p.toReal := by rwa [← ENNReal.toReal_one,ENNReal.toReal_le_toReal ENNReal.one_ne_top hpt]
  have hXi := hX.integrable hp
  have hpow := hX.integrable_norm_rpow hp0 hpt
  have hj := Asakura.Chapter1Written.conditional_jensen_written (m := m) (G := G) (P := P) (X := X) hG (norm_rpow_convex _ hpR) hXi hpow
  have hi : Integrable (fun ω => ‖P[X | G] ω‖^p.toReal) P := by
    apply Integrable.mono_nonneg (g := P[fun ω => ‖X ω‖^p.toReal | G]) integrable_condExp
    · exact (Real.continuous_rpow_const (by positivity : 0 ≤ p.toReal)).comp_aestronglyMeasurable integrable_condExp.aestronglyMeasurable.norm
    · exact ae_of_all _ fun ω => Real.rpow_nonneg (norm_nonneg _) _
    · exact hj
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ ω, P[fun ω => ‖X ω‖^p.toReal | G] ω ∂P := integral_mono_ae hi integrable_condExp hj
    _ = _ := integral_condExp hG

/-- Both branches of the printed Lp contraction, including p=infinity. -/
theorem conditional_lp_contraction_written {Ω : Type*} {m G : MeasurableSpace Ω}
    (P : @Measure Ω m) [IsProbabilityMeasure P] (hG : G ≤ m)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (X : Ω → ℝ) (hX : MemLp X p P) :
    eLpNorm (P[X | G]) p P ≤ eLpNorm X p P := by
  letI : MeasurableSpace Ω := m
  by_cases hpt : p = ∞
  · subst p
    let C := (eLpNorm X ∞ P).toReal
    have he := eLpNorm_exponent_top hX.aestronglyMeasurable
    have hXb : ∀ᵐ ω ∂P, ‖X ω‖ ≤ C := by
      filter_upwards [ae_le_eLpNormEssSup (f := X) (μ := P)] with ω hω
      rw [← he] at hω
      have h := ENNReal.toReal_mono hX.eLpNorm_ne_top hω
      simpa only [toReal_enorm] using h
    have hXi := hX.integrable (by simp)
    have hl := condExp_mono (integrable_const (-C)) hXi (m := G)
      (hXb.mono fun ω hω => by have h := neg_abs_le (X ω); rw [← Real.norm_eq_abs] at h; linarith)
    have hu := condExp_mono hXi (integrable_const C) (m := G)
      (hXb.mono fun ω hω => (le_abs_self _).trans hω)
    have hb : ∀ᵐ ω ∂P, ‖P[X | G] ω‖ ≤ C := by
      filter_upwards [hl,hu] with ω hl hu
      simp only [condExp_const hG] at hl hu
      exact abs_le.mpr ⟨hl,hu⟩
    rw [eLpNorm_exponent_top integrable_condExp.aestronglyMeasurable]
    exact (eLpNormEssSup_le_of_ae_bound hb).trans_eq (ENNReal.ofReal_toReal hX.eLpNorm_ne_top)
  · have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le hp)
    have hpow := conditional_norm_power_written P hG p hp hpt X hX
    have hE : MemLp (P[X | G]) p P :=
      (integrable_norm_rpow_iff integrable_condExp.aestronglyMeasurable hp0 hpt).mp hpow.1
    rw [← ofReal_lpNorm hE,← ofReal_lpNorm hX]
    apply ENNReal.ofReal_le_ofReal
    rw [lpNorm_eq_integral_norm_rpow_toReal hp0 hpt integrable_condExp.aestronglyMeasurable,
      lpNorm_eq_integral_norm_rpow_toReal hp0 hpt hX.aestronglyMeasurable]
    exact Real.rpow_le_rpow (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _) hpow.2 (by positivity)

end Asakura.FullAudit
