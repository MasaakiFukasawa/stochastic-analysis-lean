import FullAuditBVClamp
import FullAuditMonotoneRing

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- The measure-theoretic inequality on R, with the interval-to-monotone-class
step proved separately and all subsequent variation/integral steps connected. -/
theorem stieltjes_integral_real_intervals (α β : Measure ℝ) [IsFiniteMeasure α] [IsFiniteMeasure β]
    (ν : SignedMeasure ℝ)
    (hc : ∀ s t, s ≤ t → |ν (Ioc s t)| ≤ Real.sqrt (α.real (Ioc s t))*Real.sqrt (β.real (Ioc s t)))
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, ENNReal.ofReal |f x*g x| ∂ν.totalVariation) ≤
      (∫⁻ x, ENNReal.ofReal ((f x)^2) ∂α)^(1/2:ℝ)*
      (∫⁻ x, ENNReal.ofReal ((g x)^2) ∂β)^(1/2:ℝ) := by
  have hb := signed_cs_real_intervals α β ν hc
  have hv (E : Set ℝ) (hE : MeasurableSet E) :
      ν.totalVariation E ≤ (α E)^(1/2:ℝ)*(β E)^(1/2:ℝ) := by
    have h := signed_cs_totalVariation α β ν hb hE
    rwa [ENNReal.ofReal_mul (Real.sqrt_nonneg _),finite_sqrt_mass α E,finite_sqrt_mass β E] at h
  have h := cs_measurable_integral α β ν.totalVariation hv
    (fun x => ENNReal.ofReal |f x|) (fun x => ENNReal.ofReal |g x|)
    (by simpa only [Real.norm_eq_abs] using hf.norm.ennreal_ofReal)
    (by simpa only [Real.norm_eq_abs] using hg.norm.ennreal_ofReal)
    (fun _ => ENNReal.ofReal_ne_top) (fun _ => ENNReal.ofReal_ne_top)
  simpa only [abs_mul,ENNReal.ofReal_mul (abs_nonneg _),← ENNReal.ofReal_pow (abs_nonneg _),sq_abs] using h

/-- The appendix theorem for actual right-continuous functions on [a,b].
The constant extensions construct the measures; the integrals retain the
original half-open domain, and dV is identified with |dC| above. -/
theorem stieltjes_written (a b : ℝ) (hab : a ≤ b) (A B C : ℝ → ℝ)
    (hA : MonotoneOn A (Icc a b)) (hB : MonotoneOn B (Icc a b))
    (hrA : ∀ x ∈ Icc a b, ContinuousWithinAt A (Icc a b ∩ Ici x) x)
    (hrB : ∀ x ∈ Icc a b, ContinuousWithinAt B (Icc a b ∩ Ici x) x)
    (hC : BoundedVariationOn C (Icc a b))
    (hrC : ∀ x ∈ Icc a b, ContinuousWithinAt C (Icc a b ∩ Ici x) x)
    (hc : ∀ s t, a ≤ s → s < t → t ≤ b →
      |C t-C s| ≤ Real.sqrt (A t-A s)*Real.sqrt (B t-B s))
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g) :
    let hVC := intervalClamp_boundedVariation a b hab C hC
    let hRC := intervalClamp_right_continuous a b hab C hrC
    (∫⁻ x in Ioc a b, ENNReal.ofReal |f x*g x|
      ∂(bvVariation (C ∘ intervalClamp a b hab) hVC hRC a).measure) ≤
      (∫⁻ x in Ioc a b, ENNReal.ofReal ((f x)^2) ∂(intervalStieltjes a b hab A hA hrA).measure)^(1/2:ℝ)*
      (∫⁻ x in Ioc a b, ENNReal.ofReal ((g x)^2) ∂(intervalStieltjes a b hab B hB hrB).measure)^(1/2:ℝ) := by
  dsimp only
  let hVC := intervalClamp_boundedVariation a b hab C hC
  let hRC := intervalClamp_right_continuous a b hab C hrC
  let ν := bvSigned (C ∘ intervalClamp a b hab) hVC hRC a
  let α := (intervalStieltjes a b hab A hA hrA).measure
  let β := (intervalStieltjes a b hab B hB hrB).measure
  letI : IsFiniteMeasure α := intervalStieltjes_finite a b hab A hA hrA
  letI : IsFiniteMeasure β := intervalStieltjes_finite a b hab B hB hrB
  have hmass : ∀ s t, s ≤ t → |ν (Ioc s t)| ≤ Real.sqrt (α.real (Ioc s t))*Real.sqrt (β.real (Ioc s t)) := by
    intro s t hst
    rw [bvSigned_Ioc _ hVC hRC a s t hst,intervalStieltjes_Ioc_real a b hab A hA hrA s t hst,
      intervalStieltjes_Ioc_real a b hab B hB hrB s t hst]
    dsimp only [Function.comp_def]
    have hstc := intervalClamp_mono a b hab hst
    rcases hstc.eq_or_lt with he|hlt
    · simp only [he,sub_self,abs_zero,Real.sqrt_zero,mul_zero,le_refl]
    · exact hc _ _ (intervalClamp_mem a b hab s).1 hlt (intervalClamp_mem a b hab t).2
  have h := stieltjes_integral_real_intervals α β ν hmass ((Ioc a b).indicator f) ((Ioc a b).indicator g)
    (hf.indicator measurableSet_Ioc) (hg.indicator measurableSet_Ioc)
  have hfg : (fun x => ENNReal.ofReal |(Ioc a b).indicator f x*(Ioc a b).indicator g x|) =
      (Ioc a b).indicator (fun x => ENNReal.ofReal |f x*g x|) := by
    funext x
    by_cases hx : x ∈ Ioc a b <;> simp [Set.indicator,hx]
  have hf2 : (fun x => ENNReal.ofReal (((Ioc a b).indicator f x)^2)) =
      (Ioc a b).indicator (fun x => ENNReal.ofReal ((f x)^2)) := by
    funext x
    by_cases hx : x ∈ Ioc a b <;> simp [Set.indicator,hx]
  have hg2 : (fun x => ENNReal.ofReal (((Ioc a b).indicator g x)^2)) =
      (Ioc a b).indicator (fun x => ENNReal.ofReal ((g x)^2)) := by
    funext x
    by_cases hx : x ∈ Ioc a b <;> simp [Set.indicator,hx]
  rw [hfg,hf2,hg2,lintegral_indicator measurableSet_Ioc,lintegral_indicator measurableSet_Ioc,
    lintegral_indicator measurableSet_Ioc,bvSigned_totalVariation] at h
  exact h

end Asakura.FullAudit
