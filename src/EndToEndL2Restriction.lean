import Chapter12LpZeroExtension
import WienerIntegralInterface

open MeasureTheory Set
open scoped ENNReal

namespace Asakura.EndToEnd

/-- Restrict deterministic integrands without choosing pointwise values. -/
noncomputable def L2Restriction {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (μ.restrict s) := by
  let R (f : Lp ℝ 2 μ) : Lp ℝ 2 (μ.restrict s) :=
    ((Lp.memLp f).restrict s).toLp f
  have hR (f : Lp ℝ 2 μ) : (R f : α → ℝ) =ᵐ[μ.restrict s] f :=
    ((Lp.memLp f).restrict s).coeFn_toLp
  let L : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 (μ.restrict s) :=
    { toFun := R
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [hR (f+g), hR f, hR g,
          (Lp.coeFn_add f g).filter_mono (ae_mono Measure.restrict_le_self),
          Lp.coeFn_add (R f) (R g)] with x h1 h2 h3 h4 h5
        rw [h1, h5]
        simpa only [Pi.add_apply, h2, h3] using h4
      map_smul' := by
        intro a f
        apply Lp.ext
        filter_upwards [hR (a • f), hR f,
          (Lp.coeFn_smul a f).filter_mono (ae_mono Measure.restrict_le_self),
          Lp.coeFn_smul a (R f)] with x h1 h2 h3 h4
        change R (a • f) x = (a • R f) x
        rw [h1, h4]
        simpa only [Pi.smul_apply, h2] using h3 }
  apply L.mkContinuous 1
  intro f
  change ‖((Lp.memLp f).restrict s).toLp f‖ ≤ 1 * ‖f‖
  rw [one_mul, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
    (eLpNorm_mono_measure f Measure.restrict_le_self)

theorem L2Restriction_coe {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α) (f : Lp ℝ 2 μ) :
    (L2Restriction μ s f : α → ℝ) =ᵐ[μ.restrict s] f :=
  ((Lp.memLp f).restrict s).coeFn_toLp

theorem positive_zero_extension_restriction (f : Lp ℝ 2 (volume : Measure ℝ))
    (hf : Asakura.PositiveSupported f) :
    Asakura.Chapter12.L2ZeroExtension volume (Ioi 0) measurableSet_Ioi
      (L2Restriction volume (Ioi 0) f) = f := by
  apply Lp.ext
  have hr := (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Ioi).mp
    (L2Restriction_coe volume (Ioi 0) f)
  filter_upwards [Asakura.Chapter12.L2ZeroExtension_coe volume (Ioi 0)
    measurableSet_Ioi (L2Restriction volume (Ioi 0) f), hr, hf] with x h1 h2 h3
  rw [h1, h2]
  by_cases hx : 0 < x
  · simp [hx]
  · simp [hx, h3 (le_of_not_gt hx)]

theorem positive_restriction_inner
    (f g : Lp ℝ 2 (volume : Measure ℝ))
    (hf : Asakura.PositiveSupported f) (hg : Asakura.PositiveSupported g) :
    inner ℝ (L2Restriction volume (Ioi 0) f) (L2Restriction volume (Ioi 0) g) =
      inner ℝ f g := by
  have h := (Asakura.Chapter12.L2ZeroExtension volume (Ioi 0) measurableSet_Ioi).inner_map_map
    (L2Restriction volume (Ioi 0) f) (L2Restriction volume (Ioi 0) g)
  rw [positive_zero_extension_restriction f hf,
    positive_zero_extension_restriction g hg] at h
  exact h.symm

end Asakura.EndToEnd

#print axioms Asakura.EndToEnd.L2Restriction
#print axioms Asakura.EndToEnd.positive_restriction_inner
