import Chapter2GlobalEnergyMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem finite_kernel_lintegral_measurable
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (κ : Kernel Ω S) (hκ : ∀ ω, IsFiniteMeasure (κ ω))
    (f : Ω × S → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun ω => ∫⁻ r, f (ω,r) ∂κ ω) := by
  have h := (Measure.measurable_lintegral hf).comp (finite_kernel_joint_measurable κ hκ)
  have he ω : (∫⁻ z, f z ∂(κ ω).map (Prod.mk ω)) = ∫⁻ r, f (ω,r) ∂κ ω :=
    lintegral_map hf measurable_prodMk_left
  change Measurable (fun ω => ∫⁻ z, f z ∂(κ ω).map (Prod.mk ω)) at h
  simpa only [he] using h

/-- Exact identification of the global sample-time energy with the
expectation of the increasing limit of pathwise Stieltjes integrals. -/
theorem global_stieltjes_energy_identity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c)
    (A : Ω → ℝ → ℝ)
    (hA : ∀ n ω, MonotoneOn (A ω) (Icc 0 (c n)))
    (hAc : ∀ n ω, ContinuousOn (A ω) (Icc 0 (c n)))
    (hm : ∀ t, Measurable (fun ω => A ω t)) :
    ∃ ν : Measure (Ω × ℝ), SigmaFinite ν ∧
      ∀ f : Ω × ℝ → ℝ≥0∞, Measurable f →
      (∫⁻ z, f z ∂ν) = ∫⁻ ω, ⨆ n, ∫⁻ r, f (ω,r)
        ∂(intervalStieltjes 0 (c n) (hc n) (A ω) (hA n ω)
          (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure ∂P := by
  obtain ⟨ν,hν,hlim,_⟩ := global_random_stieltjes_measure_with_limit P c hc hcm A hA hAc hm
  refine ⟨ν,hν,?_⟩
  intro f hf
  let hr := fun n ω r (hr : r ∈ Icc 0 (c n)) => (hAc n ω r hr).mono (inter_subset_left (t := Ici r))
  let κ := fun n => randomStieltjesKernel 0 (c n) (hc n) A (hA n) (hr n) hm
  have hκ n ω : IsFiniteMeasure (κ n ω) := intervalStieltjes_finite _ _ _ _ _ _
  let R := fun n ω => ∫⁻ r, f (ω,r) ∂κ n ω
  have hRm n : Measurable (R n) := finite_kernel_lintegral_measurable (κ n) (hκ n) f hf
  have hmono ω : Monotone (fun n => R n ω) := by
    intro j n hjn
    have he : κ j ω = (κ n ω).restrict (Iic (c j)) :=
      interval_stieltjes_restrict_Iic 0 (c n) (c j) (hc j) (hcm hjn)
        (A ω) (hA n ω) (hr n ω) (hA j ω) (hr j ω)
    change (∫⁻ r, f (ω,r) ∂κ j ω) ≤ ∫⁻ r, f (ω,r) ∂κ n ω
    rw [he]
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  have ht := lintegral_tendsto_of_tendsto_of_monotone (μ := P) (fun n => (hRm n).aemeasurable)
    (ae_of_all _ hmono) (ae_of_all _ (fun ω => tendsto_atTop_iSup (hmono ω)))
  exact tendsto_nhds_unique (hlim f hf) ht

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.global_stieltjes_energy_identity
