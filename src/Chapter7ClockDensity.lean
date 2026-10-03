import FullAuditBVClamp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter7
open Asakura.FullAudit
set_option maxHeartbeats 1800000

lemma clamped_interval_intersection (a b : ℝ) (hab : a ≤ b) (s t : ℝ) (hst : s ≤ t) :
    Ioc (intervalClamp a b hab s) (intervalClamp a b hab t) = Ioc s t ∩ Ioc a b := by
  ext r
  change (max a (min b s) < r ∧ r ≤ max a (min b t)) ↔ (s < r ∧ r ≤ t) ∧ a < r ∧ r ≤ b
  grind

/-- The inverse-clock derivative identifies the entire Stieltjes measure,
not only its total mass. This licenses the subsequent weighted Ito-energy
calculation in the weak-solution construction. -/
theorem interval_stieltjes_density
    (a b : ℝ) (hab : a ≤ b) (A f : ℝ → ℝ)
    (hA : MonotoneOn A (Icc a b)) (hAc : ContinuousOn A (Icc a b))
    (hf : ContinuousOn f (Icc a b)) (hfn : ∀ r ∈ Icc a b,0 ≤ f r)
    (hd : ∀ r ∈ Ioo a b,HasDerivAt A (f r) r) :
    (intervalStieltjes a b hab A hA (fun r hr => (hAc r hr).mono inter_subset_left)).measure =
      (volume.restrict (Ioc a b)).withDensity (fun r => ENNReal.ofReal (f r)) := by
  letI := intervalStieltjes_finite a b hab A hA (fun r hr => (hAc r hr).mono inter_subset_left)
  have hfi : IntervalIntegrable f volume a b := hf.intervalIntegrable_of_Icc hab
  letI := isFiniteMeasure_withDensity_ofReal hfi.1.hasFiniteIntegral
  apply Measure.ext_of_Ioc
  intro s t hst
  let u := intervalClamp a b hab s
  let v := intervalClamp a b hab t
  have huv : u ≤ v := intervalClamp_mono a b hab hst.le
  have hu : u ∈ Icc a b := intervalClamp_mem a b hab s
  have hv : v ∈ Icc a b := intervalClamp_mem a b hab t
  have hsub : Icc u v ⊆ Icc a b := fun r hr => ⟨hu.1.trans hr.1,hr.2.trans hv.2⟩
  have hfi' : IntervalIntegrable f volume u v := (hf.mono hsub).intervalIntegrable_of_Icc huv
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv (hAc.mono hsub)
    (fun r hr => hd r ⟨hu.1.trans_lt hr.1,hr.2.trans_le hv.2⟩) hfi'
  rw [StieltjesFunction.measure_Ioc,withDensity_apply _ measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc]
  change ENNReal.ofReal (A v-A u) = ∫⁻ r in Ioc s t ∩ Ioc a b,ENNReal.ofReal (f r)
  rw [← clamped_interval_intersection a b hab s t hst.le]
  change ENNReal.ofReal (A v-A u) = ∫⁻ r in Ioc u v,ENNReal.ofReal (f r)
  rw [← ofReal_integral_eq_lintegral_ofReal hfi'.1
    ((ae_restrict_mem measurableSet_Ioc).mono fun r hr => hfn r (hsub ⟨hr.1.le,hr.2⟩)),
    ← intervalIntegral.integral_of_le huv,he]

/-- The exact energy cancellation used to turn the time-changed process
into a Brownian motion. The Stieltjes density is derived from the clock
ODE above, rather than supplied as an equality of measures. -/
theorem inverse_coefficient_clock_energy
    (a b : ℝ) (hab : a ≤ b) (A σ : ℝ → ℝ)
    (hA : MonotoneOn A (Icc a b)) (hAc : ContinuousOn A (Icc a b))
    (hσ : ContinuousOn σ (Icc a b)) (hσn : ∀ r ∈ Icc a b,σ r ≠ 0)
    (hd : ∀ r ∈ Ioo a b,HasDerivAt A ((σ r)^2) r) :
    (∫ r,(1/σ r)^2 ∂(intervalStieltjes a b hab A hA
      (fun r hr => (hAc r hr).mono inter_subset_left)).measure) = b-a := by
  rw [interval_stieltjes_density a b hab A (fun r => (σ r)^2) hA hAc
    (hσ.pow 2) (fun _ _ => sq_nonneg _) hd]
  have hi : IntervalIntegrable (fun r => (σ r)^2) volume a b := (hσ.pow 2).intervalIntegrable_of_Icc hab
  have hm : AEMeasurable (fun r => ENNReal.ofReal ((σ r)^2)) (volume.restrict (Ioc a b)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hi.1.aemeasurable
  rw [integral_withDensity_eq_integral_toReal_smul₀ hm
    (.of_forall (fun r => ENNReal.ofReal_lt_top))]
  have he : (fun r => (ENNReal.ofReal ((σ r)^2)).toReal • (1/σ r)^2) =ᵐ[volume.restrict (Ioc a b)]
      fun _ => (1:ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul]
    field_simp [hσn r ⟨hr.1.le,hr.2⟩]
  rw [integral_congr_ae he,← intervalIntegral.integral_of_le hab]
  simp

end Asakura.Chapter7
