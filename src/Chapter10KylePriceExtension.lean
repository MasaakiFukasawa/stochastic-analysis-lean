import Chapter10KyleOrderAdmissibility
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter10

/-- Absolute order integrability makes the price extend continuously to
maturity; no martingale convergence theorem or subsequence is needed. -/
theorem kyle_price_continuous_extension (α B p : ℝ → ℝ) (T p0 l σ : ℝ)
    (hT : 0<T) (hα : IntegrableOn α (Ioo 0 T) volume)
    (hB : ContinuousOn B (Icc 0 T))
    (hp : ∀ t∈Ioo 0 T,p t=p0+l*((∫ s in 0..t,α s)+σ*B t)) :
    Tendsto p (𝓝[<] T) (𝓝 (p0+l*((∫ s in 0..T,α s)+σ*B T))) := by
  have hα' : IntegrableOn α (Ioc 0 T) volume := by
    simpa only [IntegrableOn,Measure.restrict_congr_set Ioo_ae_eq_Ioc] using hα
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr hα'
  have hc : ContinuousOn (fun t => ∫ s in 0..t,α s) (Icc 0 T) := by
    simpa only [uIcc_of_le hT.le] using intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
  have hq : ContinuousWithinAt (fun t => p0+l*((∫ s in 0..t,α s)+σ*B t)) (Ioo 0 T) T :=
    (continuousWithinAt_const.add (continuousWithinAt_const.mul
      ((hc T ⟨hT.le,le_rfl⟩).add (continuousWithinAt_const.mul (hB T ⟨hT.le,le_rfl⟩))))).mono Ioo_subset_Icc_self
  have hqt := hq.tendsto
  rw [nhdsWithin_Ioo_eq_nhdsLT hT] at hqt
  apply hqt.congr'
  rw [← nhdsWithin_Ioo_eq_nhdsLT hT]
  exact (show ∀ᶠ t in 𝓝[Ioo (0:ℝ) T] T,t∈Ioo 0 T from self_mem_nhdsWithin).mono
    (fun t ht => (hp t ht).symm)

end Asakura.Chapter10
