import Chapter2L2SectionIntegrable
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {E S : Type*} [MeasurableSpace E] [MeasurableSpace S]

theorem l2_set_integral_norm_bound (ν : Measure S) (B : Set S)
    (hB : MeasurableSet B) (hfin : ν B ≠ ∞) (f : S → ℝ) (hf : MemLp f 2 ν) :
    (∫ r in B, ‖f r‖ ∂ν) ≤
      ‖indicatorConstLp 2 hB hfin (1:ℝ)‖ * ‖hf.toLp f‖ := by
  have he := L2.inner_indicatorConstLp_eq_setIntegral_inner ℝ
    (hf.norm.toLp (fun r => ‖f r‖)) hB (1:ℝ) hfin
  simp only [Real.inner_apply,one_mul] at he
  have ha : (∫ r in B, (hf.norm.toLp (fun r => ‖f r‖)) r ∂ν) =
      ∫ r in B, ‖f r‖ ∂ν := integral_congr_ae (ae_restrict_of_ae hf.norm.coeFn_toLp)
  rw [ha] at he
  rw [← he]
  have hb := real_inner_le_norm (indicatorConstLp 2 hB hfin (1:ℝ)) (hf.norm.toLp (fun r => ‖f r‖))
  have hn : eLpNorm (fun r => ‖f r‖) 2 ν = eLpNorm f 2 ν := eLpNorm_norm f hf.aestronglyMeasurable
  simpa only [Lp.norm_toLp,hn] using hb

theorem l2_set_integral_eq_inner (ν : Measure S) (B : Set S)
    (hB : MeasurableSet B) (hfin : ν B ≠ ∞) (f : Lp ℝ 2 ν) :
    (∫ r in B, f r ∂ν) = inner ℝ (indicatorConstLp 2 hB hfin (1:ℝ)) f := by
  simpa only [Real.inner_apply,one_mul] using
    (L2.inner_indicatorConstLp_eq_setIntegral_inner ℝ f hB (1:ℝ) hfin).symm

/-- The Bochner integral of actual L2 sections agrees almost everywhere with
the ordinary pointwise parameter integral. It is not an assumed identification. -/
theorem l2_bochner_integral_pointwise
    (μ : Measure E) [SigmaFinite μ] (ν : Measure S) [SigmaFinite ν]
    (H : E × S → ℝ) (hH : Measurable H)
    (hL : ∀ x, MemLp (fun r => H (x,r)) 2 ν)
    (hI : Integrable (fun x => (hL x).toLp (fun r => H (x,r))) μ) :
    ((∫ x, (hL x).toLp (fun r => H (x,r)) ∂μ : Lp ℝ 2 ν) : S → ℝ)
      =ᵐ[ν] (fun r => ∫ x, H (x,r) ∂μ) := by
  let Z := fun x => (hL x).toLp (fun r => H (x,r))
  let z : Lp ℝ 2 ν := ∫ x, Z x ∂μ
  have hprod (B : Set S) (hB : MeasurableSet B) (hfin : ν B < ∞) :
      Integrable H (μ.prod (ν.restrict B)) := by
    letI : IsFiniteMeasure (ν.restrict B) := ⟨by simpa using hfin⟩
    apply (integrable_prod_iff hH.aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ (fun x => ((hL x).restrict B).integrable (by norm_num))
    · apply (hI.norm.const_mul ‖indicatorConstLp 2 hB hfin.ne (1:ℝ)‖).mono'
        (hH.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
      exact ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun r => norm_nonneg _))]
        exact l2_set_integral_norm_bound ν B hB hfin.ne _ (hL x))
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro B hB hfin
    exact integrableOn_Lp_of_measure_ne_top z (by norm_num) hfin.ne
  · intro B hB hfin
    exact (hprod B hB hfin).integral_prod_right
  · intro B hB hfin
    rw [l2_set_integral_eq_inner ν B hB hfin.ne]
    have he := (innerSL ℝ (indicatorConstLp 2 hB hfin.ne (1:ℝ))).integral_comp_comm hI
    change (∫ x, inner ℝ (indicatorConstLp 2 hB hfin.ne (1:ℝ)) (Z x) ∂μ) =
      inner ℝ (indicatorConstLp 2 hB hfin.ne (1:ℝ)) z at he
    rw [← he]
    calc
      (∫ x, inner ℝ (indicatorConstLp 2 hB hfin.ne (1:ℝ)) (Z x) ∂μ) =
          ∫ x, ∫ r in B, H (x,r) ∂ν ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by
          change inner ℝ (indicatorConstLp 2 hB hfin.ne (1:ℝ)) (Z x) = ∫ r in B, H (x,r) ∂ν
          rw [← l2_set_integral_eq_inner ν B hB hfin.ne]
          exact integral_congr_ae (ae_restrict_of_ae (hL x).coeFn_toLp))
      _ = ∫ r in B, ∫ x, H (x,r) ∂μ ∂ν := integral_integral_swap (hprod B hB hfin)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.l2_bochner_integral_pointwise
