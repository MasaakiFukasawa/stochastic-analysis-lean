import Chapter2GlobalEnergyIdentity
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Finite L2 energy for the actual global Stieltjes measure supplies the
integrable terminal-energy variable and the pathwise increasing limit needed
by the terminal Ito construction. No terminal energy is assumed separately. -/
theorem global_l2_terminal_energy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c)
    (A : Ω → ℝ → ℝ)
    (hA : ∀ n ω, MonotoneOn (A ω) (Icc 0 (c n)))
    (hAc : ∀ n ω, ContinuousOn (A ω) (Icc 0 (c n)))
    (hm : ∀ t, Measurable (fun ω => A ω t))
    (ν : Measure (Ω × ℝ))
    (hν : ∀ f : Ω × ℝ → ℝ≥0∞, Measurable f →
      (∫⁻ z, f z ∂ν) = ∫⁻ ω, ⨆ n, ∫⁻ r, f (ω,r)
        ∂(intervalStieltjes 0 (c n) (hc n) (A ω) (hA n ω)
          (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure ∂P)
    (H : Ω × ℝ → ℝ) (hH : Measurable H) (hL : MemLp H 2 ν) :
    ∃ CT : Ω → ℝ, Integrable CT P ∧ (∀ ω, 0 ≤ CT ω) ∧
      (∀ n, ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)^2)
        (intervalStieltjes 0 (c n) (hc n) (A ω) (hA n ω)
          (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => ∫ r, H (ω,r)^2
        ∂(intervalStieltjes 0 (c n) (hc n) (A ω) (hA n ω)
          (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure) atTop (𝓝 (CT ω))) ∧
      (∫ ω, CT ω ∂P) = ∫ z, H z^2 ∂ν := by
  let hr := fun n ω r (hr : r ∈ Icc 0 (c n)) => (hAc n ω r hr).mono (inter_subset_left (t := Ici r))
  let κ := fun n => randomStieltjesKernel 0 (c n) (hc n) A (hA n) (hr n) hm
  have hκ n ω : IsFiniteMeasure (κ n ω) := intervalStieltjes_finite _ _ _ _ _ _
  let f := fun z => ENNReal.ofReal (H z^2)
  have hf : Measurable f := (hH.pow_const 2).ennreal_ofReal
  let R := fun n ω => ∫⁻ r, f (ω,r) ∂κ n ω
  have hRm n : Measurable (R n) := finite_kernel_lintegral_measurable (κ n) (hκ n) f hf
  let Q := fun ω => ⨆ n, R n ω
  have hQm : Measurable Q := Measurable.iSup hRm
  have hmono ω : Monotone (fun n => R n ω) := by
    intro j n hjn
    have he : κ j ω = (κ n ω).restrict (Iic (c j)) :=
      interval_stieltjes_restrict_Iic 0 (c n) (c j) (hc j) (hcm hjn)
        (A ω) (hA n ω) (hr n ω) (hA j ω) (hr j ω)
    change (∫⁻ r, f (ω,r) ∂κ j ω) ≤ ∫⁻ r, f (ω,r) ∂κ n ω
    rw [he]
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  have hi : Integrable (fun z => H z^2) ν :=
    (memLp_two_iff_integrable_sq hL.aestronglyMeasurable).1 hL
  have hQeq : (∫⁻ ω, Q ω ∂P) = ENNReal.ofReal (∫ z, H z^2 ∂ν) := by
    have hh := hν f hf
    change (∫⁻ z, f z ∂ν) = ∫⁻ ω, Q ω ∂P at hh
    rw [← hh]
    exact (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun z => sq_nonneg _))).symm
  have hQfin : (∫⁻ ω, Q ω ∂P) < ∞ := by rw [hQeq]; exact ENNReal.ofReal_lt_top
  have hQa : ∀ᵐ ω ∂P, Q ω < ∞ := ae_lt_top hQm hQfin.ne
  let CT := fun ω => (Q ω).toReal
  have hCT : Integrable CT P := integrable_toReal_of_lintegral_ne_top hQm.aemeasurable hQfin.ne
  have hp : ∀ᵐ ω ∂P, ∀ n, Integrable (fun r => H (ω,r)^2) (κ n ω) := by
    filter_upwards [hQa] with ω hω
    intro n
    refine ⟨((hH.comp measurable_prodMk_left).pow_const 2).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs,abs_sq]
    exact (le_iSup (fun n => R n ω) n).trans_lt hω
  have he ω n (hn : Integrable (fun r => H (ω,r)^2) (κ n ω)) :
      (∫ r, H (ω,r)^2 ∂κ n ω) = (R n ω).toReal := by
    have hh := ofReal_integral_eq_lintegral_ofReal hn (ae_of_all _ (fun r => sq_nonneg (H (ω,r))))
    have ht := congrArg ENNReal.toReal hh
    rw [ENNReal.toReal_ofReal (integral_nonneg (fun r => sq_nonneg _))] at ht
    exact ht
  refine ⟨CT,hCT,fun ω => ENNReal.toReal_nonneg,fun n => hp.mono (fun ω hω => hω n),?_,?_⟩
  · filter_upwards [hQa,hp] with ω hω hiω
    have ht := (ENNReal.continuousAt_toReal hω.ne).tendsto.comp (tendsto_atTop_iSup (hmono ω))
    change Tendsto (fun n => ∫ r, H (ω,r)^2 ∂κ n ω) atTop (𝓝 (CT ω))
    have hei : (fun n => ∫ r, H (ω,r)^2 ∂κ n ω) = fun n => (R n ω).toReal :=
      funext (fun n => he ω n (hiω n))
    rw [hei]
    exact ht
  · rw [integral_toReal hQm.aemeasurable hQa,hQeq,ENNReal.toReal_ofReal]
    exact integral_nonneg (fun z => sq_nonneg _)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.global_l2_terminal_energy
