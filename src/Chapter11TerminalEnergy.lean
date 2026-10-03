import Chapter11HedgeEnergy
import Mathlib.Analysis.Calculus.FDeriv.Measurable

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- The monotone-convergence step needs only a uniform bound on the
preterminal energies; no integrability at maturity is presupposed. -/
theorem nonnegative_integrable_increasing_union {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (f : E → ℝ) (hf : Measurable f) (hn : ∀ x,0≤f x)
    (s : ℕ → Set E) (hs : Monotone s) (hi : ∀ n,IntegrableOn f (s n) μ)
    (K : ℝ) (hb : ∀ n,(∫ x in s n,f x ∂μ)≤K) :
    IntegrableOn f (⋃ n,s n) μ ∧ (∫ x in ⋃ n,s n,f x ∂μ)≤K := by
  have hl : (∫⁻ x in ⋃ n,s n,ENNReal.ofReal (f x) ∂μ)≤ENNReal.ofReal K := by
    rw [setLIntegral_iUnion_of_directed _ hs.directed_le]
    apply iSup_le
    intro n
    rw [←ofReal_integral_eq_lintegral_ofReal (hi n) (ae_of_all _ hn)]
    exact ENNReal.ofReal_le_ofReal (hb n)
  have hfi : IntegrableOn f (⋃ n,s n) μ :=
    ⟨hf.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal (ae_of_all _ hn)).mpr (hl.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hfi,?_⟩
  have hK : 0≤K := (integral_nonneg hn).trans (hb 0)
  rw [←ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hn)] at hl
  exact (ENNReal.ofReal_le_ofReal_iff hK).mp hl

/-- Turn the random path energy estimate into integrability on the
product of time and probability, using the actual Fubini theorem. -/
theorem square_energy_product_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : Ω × ℝ → ℝ) (hH : Measurable H)
    (R : ℝ) (hR : 0≤R)
    (hpath : ∀ᵐ w ∂P,IntervalIntegrable (fun r => H (w,r)^2) volume 0 R)
    (hi : Integrable (fun w => ∫ r in 0..R,H (w,r)^2) P) :
    Integrable (fun z => H z^2) (P.prod (volume.restrict (Ioc 0 R))) := by
  apply (integrable_prod_iff ((hH.pow_const 2).aestronglyMeasurable)).mpr
  refine ⟨hpath.mono fun w hw => hw.1,?_⟩
  simpa only [Real.norm_eq_abs,abs_sq,intervalIntegral.integral_of_le hR] using hi

/-- Passing through an increasing exhaustion of [0,T) proves the finite
terminal energy used to extend the stochastic integral to maturity. -/
theorem terminal_square_energy_from_prefix_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : Ω × ℝ → ℝ) (hH : Measurable H)
    (T K : ℝ) (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c)
    (hu : (⋃ n,Ioc (0:ℝ) (c n))=Ioo 0 T)
    (hpath : ∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => H (w,r)^2) volume 0 (c n))
    (hi : ∀ n,Integrable (fun w => ∫ r in 0..c n,H (w,r)^2) P)
    (hb : ∀ n,(∫ w,(∫ r in 0..c n,H (w,r)^2) ∂P)≤K) :
    Integrable (fun z => H z^2) (P.prod (volume.restrict (Ioo 0 T))) ∧
      (∫ z,H z^2 ∂P.prod (volume.restrict (Ioo 0 T)))≤K := by
  let s := fun n => (univ : Set Ω) ×ˢ Ioc (0:ℝ) (c n)
  have he (A : Set ℝ) : P.prod (volume.restrict A)=(P.prod volume).restrict ((univ : Set Ω) ×ˢ A) := by
    simpa only [Measure.restrict_univ] using Measure.prod_restrict (μ:=P) (ν:=volume) univ A
  have hsi n : IntegrableOn (fun z => H z^2) (s n) (P.prod volume) := by
    change Integrable (fun z => H z^2) ((P.prod volume).restrict ((univ : Set Ω) ×ˢ Ioc 0 (c n)))
    rw [←he]
    exact square_energy_product_integrable P H hH (c n) (hc n) (hpath n) (hi n)
  have hsb n : (∫ z in s n,H z^2 ∂P.prod volume)≤K := by
    rw [←he,integral_prod _ (square_energy_product_integrable P H hH (c n) (hc n) (hpath n) (hi n))]
    simpa only [intervalIntegral.integral_of_le (hc n)] using hb n
  have hsm : Monotone s := fun i j hij => prod_mono subset_rfl (Ioc_subset_Ioc_right (hcm hij))
  have huu : (⋃ n,s n)=(univ : Set Ω) ×ˢ Ioo 0 T := by
    ext z
    simp only [s,mem_iUnion,mem_prod,mem_univ,true_and]
    simpa only [mem_iUnion] using Set.ext_iff.mp hu z.2
  have hh := nonnegative_integrable_increasing_union (P.prod volume) (fun z => H z^2)
    (hH.pow_const 2) (fun z => sq_nonneg _) s hsm hsi K hsb
  unfold IntegrableOn at hh
  rw [huu,←he] at hh
  exact hh

end Asakura.Chapter11
