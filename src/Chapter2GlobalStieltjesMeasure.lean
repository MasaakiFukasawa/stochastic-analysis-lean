import Chapter2FiniteKernelProduct
import Chapter2CompatibleMeasurePasting
import Chapter2StieltjesRestriction

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

theorem finite_kernel_product_restrict_congr
    (P : Measure Ω) (κ η : Kernel Ω S)
    (hκ : ∀ ω, IsFiniteMeasure (κ ω)) (hη : ∀ ω, IsFiniteMeasure (η ω))
    (C D : Set S) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (he : ∀ ω, (κ ω).restrict C = (η ω).restrict D) :
    (finiteKernelProduct P κ hκ).restrict (univ ×ˢ C) =
      (finiteKernelProduct P η hη).restrict (univ ×ˢ D) := by
  ext B hB
  rw [Measure.restrict_apply hB,Measure.restrict_apply hB,
    finite_kernel_product_apply P κ hκ _ (hB.inter (MeasurableSet.univ.prod hC)),
    finite_kernel_product_apply P η hη _ (hB.inter (MeasurableSet.univ.prod hD))]
  apply lintegral_congr
  intro ω
  have h := congrArg (fun μ : Measure S => μ (Prod.mk ω ⁻¹' B)) (he ω)
  rw [Measure.restrict_apply (measurable_prodMk_left hB),Measure.restrict_apply (measurable_prodMk_left hB)] at h
  simpa only [preimage_inter,mk_preimage_prod_right,mem_univ,ite_true] using h

/-- One actual sigma-finite sample-time Stieltjes measure is constructed
from A on all finite horizons. Terminal A_T and E[A_t] are not assumed finite.
The restrictions give precisely E[int f dA] on each original horizon. -/
theorem global_random_stieltjes_measure
    (P : Measure Ω) [IsProbabilityMeasure P]
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c)
    (A : Ω → ℝ → ℝ)
    (hA : ∀ n ω, MonotoneOn (A ω) (Icc 0 (c n)))
    (hAc : ∀ n ω, ContinuousOn (A ω) (Icc 0 (c n)))
    (hm : ∀ t, Measurable (fun ω => A ω t)) :
    ∃ ν : Measure (Ω × ℝ), SigmaFinite ν ∧
      ∀ n (f : Ω × ℝ → ℝ≥0∞), Measurable f →
      (∫⁻ z, f z ∂ν.restrict (univ ×ˢ Iic (c n))) =
        ∫⁻ ω, ∫⁻ r, f (ω,r)
          ∂(intervalStieltjes 0 (c n) (hc n) (A ω) (hA n ω)
            (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure ∂P := by
  let hr := fun n ω r (hr : r ∈ Icc 0 (c n)) => (hAc n ω r hr).mono (inter_subset_left (t := Ici r))
  let κ := fun n => randomStieltjesKernel 0 (c n) (hc n) A (hA n) (hr n) hm
  have hκ n ω : IsFiniteMeasure (κ n ω) := intervalStieltjes_finite _ _ _ _ _ _
  let μ := fun n => finiteKernelProduct P (κ n) (hκ n)
  let B := fun n : ℕ => (univ : Set Ω) ×ˢ Iic (c n)
  have hB n : MeasurableSet (B n) := MeasurableSet.univ.prod measurableSet_Iic
  have hselfpath n ω : (κ n ω).restrict (Iic (c n)) = κ n ω := by
    apply Measure.restrict_eq_self_of_ae_mem
    exact (interval_stieltjes_ae_mem_Ioc 0 (c n) (hc n) (A ω) (hA n ω) (hr n ω)).mono (fun r hr => hr.2)
  have hsmall j n (hjn : j ≤ n) ω : (κ n ω).restrict (Iic (c j)) = κ j ω := by
    exact (interval_stieltjes_restrict_Iic 0 (c n) (c j) (hc j) (hcm hjn)
      (A ω) (hA n ω) (hr n ω) (hA j ω) (hr j ω)).symm
  have hbig j n (hjn : j ≤ n) ω : (κ j ω).restrict (Iic (c n)) = κ j ω := by
    calc
      (κ j ω).restrict (Iic (c n)) = ((κ j ω).restrict (Iic (c j))).restrict (Iic (c n)) := by rw [hselfpath]
      _ = ((κ j ω).restrict (Iic (c n))).restrict (Iic (c j)) := Measure.restrict_comm measurableSet_Iic
      _ = (κ j ω).restrict (Iic (c j)) := Measure.restrict_restrict_of_subset (Iic_subset_Iic.mpr (hcm hjn))
      _ = κ j ω := hselfpath j ω
  have hself n : (μ n).restrict (B n) = μ n := by
    have h := finite_kernel_product_restrict_congr P (κ n) (κ n) (hκ n) (hκ n)
      (Iic (c n)) univ measurableSet_Iic MeasurableSet.univ (fun ω => by rw [hselfpath,Measure.restrict_univ])
    simpa only [univ_prod_univ,Measure.restrict_univ] using h
  have hcompat j n : (μ j).restrict (B n) = (μ n).restrict (B j) := by
    apply finite_kernel_product_restrict_congr P (κ j) (κ n) (hκ j) (hκ n)
      (Iic (c n)) (Iic (c j)) measurableSet_Iic measurableSet_Iic
    intro ω
    rcases le_total j n with hjn | hnj
    · rw [hbig j n hjn ω,hsmall j n hjn ω]
    · rw [hsmall n j hnj ω,hbig n j hnj ω]
  letI : ∀ n, SigmaFinite (μ n) := fun n => finite_kernel_product_sigmaFinite P (κ n) (hκ n)
  refine ⟨compatibleMeasurePaste μ B,compatible_measure_paste_sigmaFinite μ B hB,?_⟩
  intro n f hf
  rw [show univ ×ˢ Iic (c n) = B n from rfl,compatible_measure_paste_restrict μ B hB hself hcompat]
  exact finite_kernel_product_lintegral P (κ n) (hκ n) f hf

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.global_random_stieltjes_measure
