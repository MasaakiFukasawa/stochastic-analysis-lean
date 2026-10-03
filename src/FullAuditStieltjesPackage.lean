import FullAuditStieltjesWritten

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
set_option maxHeartbeats 500000

/-- Package the appendix construction as actual finite measures and a signed
 measure characterized by their increments on the original interval. -/
theorem stieltjes_interval_package (a b : ℝ) (hab : a ≤ b) (A B C : ℝ → ℝ)
    (hA : MonotoneOn A (Icc a b)) (hB : MonotoneOn B (Icc a b))
    (hrA : ∀ x ∈ Icc a b, ContinuousWithinAt A (Icc a b ∩ Ici x) x)
    (hrB : ∀ x ∈ Icc a b, ContinuousWithinAt B (Icc a b ∩ Ici x) x)
    (hC : BoundedVariationOn C (Icc a b))
    (hrC : ∀ x ∈ Icc a b, ContinuousWithinAt C (Icc a b ∩ Ici x) x)
    (hc : ∀ s t, a ≤ s → s < t → t ≤ b →
      |C t-C s| ≤ Real.sqrt (A t-A s)*Real.sqrt (B t-B s)) :
    ∃ (α β : Measure ℝ) (ν : SignedMeasure ℝ), IsFiniteMeasure α ∧ IsFiniteMeasure β ∧
      (∀ s t, a ≤ s → s ≤ t → t ≤ b →
        α.real (Ioc s t) = A t-A s ∧ β.real (Ioc s t) = B t-B s ∧ ν (Ioc s t) = C t-C s) ∧
      (∀ f g : ℝ → ℝ, Measurable f → Measurable g →
        (∫⁻ x, ENNReal.ofReal |f x*g x| ∂ν.totalVariation) ≤
          (∫⁻ x, ENNReal.ofReal (f x^2) ∂α)^(1/2:ℝ)*
          (∫⁻ x, ENNReal.ofReal (g x^2) ∂β)^(1/2:ℝ)) := by
  let hVC := intervalClamp_boundedVariation a b hab C hC
  let hRC := intervalClamp_right_continuous a b hab C hrC
  let ν := bvSigned (C ∘ intervalClamp a b hab) hVC hRC a
  let α := (intervalStieltjes a b hab A hA hrA).measure
  let β := (intervalStieltjes a b hab B hB hrB).measure
  letI : IsFiniteMeasure α := intervalStieltjes_finite a b hab A hA hrA
  letI : IsFiniteMeasure β := intervalStieltjes_finite a b hab B hB hrB
  refine ⟨α,β,ν,inferInstance,inferInstance,?_,?_⟩
  · intro s t has hst htb
    have hs : s ∈ Icc a b := ⟨has,hst.trans htb⟩
    have ht : t ∈ Icc a b := ⟨has.trans hst,htb⟩
    rw [intervalStieltjes_Ioc_real a b hab A hA hrA s t hst,
      intervalStieltjes_Ioc_real a b hab B hB hrB s t hst,
      bvSigned_Ioc _ hVC hRC a s t hst]
    simp only [Function.comp_def,intervalClamp_eq a b hab hs,intervalClamp_eq a b hab ht,and_self]
  · intro f g hf hg
    apply stieltjes_integral_real_intervals α β ν _ f g hf hg
    intro s t hst
    rw [bvSigned_Ioc _ hVC hRC a s t hst,intervalStieltjes_Ioc_real a b hab A hA hrA s t hst,
      intervalStieltjes_Ioc_real a b hab B hB hrB s t hst]
    dsimp only [Function.comp_def]
    have hstc := intervalClamp_mono a b hab hst
    rcases hstc.eq_or_lt with he | hlt
    · simp only [he,sub_self,abs_zero,Real.sqrt_zero,mul_zero,le_refl]
    · exact hc _ _ (intervalClamp_mem a b hab s).1 hlt (intervalClamp_mem a b hab t).2

end Asakura.FullAudit
