import Chapter2FiniteKernelIntegrability
import Chapter2L2SectionIntegrable
import Chapter2EnergyNorm

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Restricting a global sample-time energy to a finite random-measure
horizon supplies both pathwise integrability and integrable expectations. -/
theorem finite_kernel_square_energy
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (ν : Measure (Ω × S))
    (κ : Kernel Ω S) (hκ : ∀ ω, IsFiniteMeasure (κ ω))
    (hdom : ∀ f : Ω × S → ℝ≥0∞, Measurable f →
      (∫⁻ ω, ∫⁻ r, f (ω,r) ∂κ ω ∂P) ≤ ∫⁻ z, f z ∂ν)
    (H : Ω × S → ℝ) (hH : Measurable H) (hL : MemLp H 2 ν) :
    (∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)^2) (κ ω)) ∧
    Integrable (fun ω => ∫ r, H (ω,r)^2 ∂κ ω) P ∧
    (∫ ω, ∫ r, H (ω,r)^2 ∂κ ω ∂P) ≤ ∫ z, H z^2 ∂ν := by
  let f := fun z => ENNReal.ofReal (H z^2)
  have hf : Measurable f := (hH.pow_const 2).ennreal_ofReal
  let R := fun ω => ∫⁻ r, f (ω,r) ∂κ ω
  have hRm : Measurable R := finite_kernel_lintegral_measurable κ hκ f hf
  have hi := (memLp_two_iff_integrable_sq hL.aestronglyMeasurable).mp hL
  have he : (∫⁻ z, f z ∂ν) = ENNReal.ofReal (∫ z, H z^2 ∂ν) :=
    (ofReal_integral_eq_lintegral_ofReal hi (.of_forall (fun z => sq_nonneg _))).symm
  have hb : (∫⁻ ω, R ω ∂P) ≤ ENNReal.ofReal (∫ z, H z^2 ∂ν) := by
    exact (hdom f hf).trans_eq he
  have hfin : (∫⁻ ω, R ω ∂P) < ∞ := hb.trans_lt ENNReal.ofReal_lt_top
  have hRa := ae_lt_top hRm hfin.ne
  have hp : ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)^2) (κ ω) := by
    filter_upwards [hRa] with ω hω
    refine ⟨((hH.comp measurable_prodMk_left).pow_const 2).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simpa only [Real.norm_eq_abs,abs_sq] using hω
  have hEq : (fun ω => ∫ r, H (ω,r)^2 ∂κ ω) =ᵐ[P] (fun ω => (R ω).toReal) := by
    filter_upwards [hp] with ω hω
    have h := congrArg ENNReal.toReal
      (ofReal_integral_eq_lintegral_ofReal hω (.of_forall (fun r => sq_nonneg (H (ω,r)))))
    simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun r => sq_nonneg _))] using h
  refine ⟨hp,(integrable_toReal_of_lintegral_ne_top hRm.aemeasurable hfin.ne).congr hEq.symm,?_⟩
  rw [integral_congr_ae hEq,integral_toReal hRm.aemeasurable hRa]
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun z => sq_nonneg _))] using ht

/-- The original mixed L1(L2) norm controls every finite-horizon mixed
energy norm. Thus the printed Fubini proof needs no new integrability
hypothesis at its finite-time covariance step. -/
theorem finite_kernel_parameter_energy
    {E Ω S : Type*} [MeasurableSpace E] [MeasurableSpace Ω] [MeasurableSpace S]
    (μ : Measure E) (P : Measure Ω) [SigmaFinite P]
    (ν : Measure (Ω × S)) [SigmaFinite ν]
    (κ : Kernel Ω S) (hκ : ∀ ω, IsFiniteMeasure (κ ω))
    (hdom : ∀ f : Ω × S → ℝ≥0∞, Measurable f →
      (∫⁻ ω, ∫⁻ r, f (ω,r) ∂κ ω ∂P) ≤ ∫⁻ z, f z ∂ν)
    (H : E × (Ω × S) → ℝ) (hH : Measurable H)
    (hN : (∫⁻ x, eLpNorm (fun z => H (x,z)) 2 ν ∂μ) < ∞) :
    (∀ᵐ x ∂μ, ∀ᵐ ω ∂P, Integrable (fun r => H (x,(ω,r))^2) (κ ω)) ∧
    (∀ᵐ x ∂μ, Integrable (fun ω => ∫ r, H (x,(ω,r))^2 ∂κ ω) P) ∧
    Integrable (fun x => Real.sqrt (∫ ω, ∫ r, H (x,(ω,r))^2 ∂κ ω ∂P)) μ := by
  have hmem : ∀ᵐ x ∂μ, MemLp (fun z => H (x,z)) 2 ν := by
    simpa only [memLp_iff] using ae_lt_top (measurable_L2_section_norm ν H hH) hN.ne
  have hx := hmem.mono (fun x hx => finite_kernel_square_energy P ν κ hκ hdom _
    (hH.comp measurable_prodMk_left) hx)
  refine ⟨hx.mono (fun x h => h.1),hx.mono (fun x h => h.2.1),?_⟩
  let K : Kernel (E × Ω) S := ⟨fun z => κ z.2,κ.measurable.comp measurable_snd⟩
  have hK z : IsFiniteMeasure (K z) := hκ z.2
  have hHm : Measurable (fun z : (E × Ω) × S => H (z.1.1,(z.1.2,z.2))^2) :=
    (hH.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).pow_const 2
  have hEm : Measurable (fun z : E × Ω => ∫ r, H (z.1,(z.2,r))^2 ∂κ z.2) :=
    finite_kernel_integral_measurable K hK _ hHm
  have hNm := ((hEm.stronglyMeasurable.integral_prod_right' (ν := P)).measurable).sqrt
  have hbound : ∀ᵐ x ∂μ, Real.sqrt (∫ ω, ∫ r, H (x,(ω,r))^2 ∂κ ω ∂P) ≤
      (eLpNorm (fun z => H (x,z)) 2 ν).toReal := by
    filter_upwards [hmem,hx] with x hmx hex
    have he := congrArg ENNReal.toReal (real_eLpNorm_two_energy ν _ hmx)
    rw [← ENNReal.toReal_rpow,ENNReal.toReal_ofReal (integral_nonneg (fun z => sq_nonneg _))] at he
    rw [he,← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hex.2.2
  have hInt := integrable_toReal_of_lintegral_ne_top (measurable_L2_section_norm ν H hH).aemeasurable hN.ne
  exact hInt.mono' hNm.aestronglyMeasurable (hbound.mono (fun x hx => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] using hx))

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.finite_kernel_parameter_energy
