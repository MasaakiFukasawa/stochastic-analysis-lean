import FullAuditStieltjesPackage

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- KW for the actual clamped Stieltjes measures, with integrands only
measurable on the time interval. The endpoint can be chosen pathwise. -/
theorem canonical_interval_kw (b : ℝ) (hb : 0 ≤ b) (A B C : ℝ → ℝ)
    (hA : MonotoneOn A (Icc 0 b)) (hB : MonotoneOn B (Icc 0 b))
    (hrA : ∀ x ∈ Icc 0 b, ContinuousWithinAt A (Icc 0 b ∩ Ici x) x)
    (hrB : ∀ x ∈ Icc 0 b, ContinuousWithinAt B (Icc 0 b ∩ Ici x) x)
    (hC : BoundedVariationOn C (Icc 0 b))
    (hrC : ∀ x ∈ Icc 0 b, ContinuousWithinAt C (Icc 0 b ∩ Ici x) x)
    (hc : ∀ s t, 0 ≤ s → s < t → t ≤ b →
      |C t-C s| ≤ Real.sqrt (A t-A s)*Real.sqrt (B t-B s))
    (f g : Icc (0:ℝ) b → ℝ) (hf : Measurable f) (hg : Measurable g) :
    let α := (intervalStieltjes 0 b hb A hA hrA).measure
    let β := (intervalStieltjes 0 b hb B hB hrB).measure
    let ν := bvSigned (C ∘ intervalClamp 0 b hb)
      (intervalClamp_boundedVariation 0 b hb C hC)
      (intervalClamp_right_continuous 0 b hb C hrC) 0
    (∫⁻ x, ENNReal.ofReal |f (projIcc 0 b hb x)*g (projIcc 0 b hb x)| ∂ν.totalVariation) ≤
      (∫⁻ x, ENNReal.ofReal (f (projIcc 0 b hb x)^2) ∂α)^(1/2:ℝ)*
      (∫⁻ x, ENNReal.ofReal (g (projIcc 0 b hb x)^2) ∂β)^(1/2:ℝ) := by
  intro α β ν
  letI : IsFiniteMeasure α := intervalStieltjes_finite 0 b hb A hA hrA
  letI : IsFiniteMeasure β := intervalStieltjes_finite 0 b hb B hB hrB
  apply stieltjes_integral_real_intervals α β ν _ _ _
    (hf.comp continuous_projIcc.measurable) (hg.comp continuous_projIcc.measurable)
  intro s t hst
  rw [bvSigned_Ioc,intervalStieltjes_Ioc_real,intervalStieltjes_Ioc_real]
  · dsimp only [Function.comp_def]
    rcases (intervalClamp_mono 0 b hb hst).eq_or_lt with he | hlt
    · simp only [he,sub_self,abs_zero,Real.sqrt_zero,mul_zero,le_refl]
    · exact hc _ _ (intervalClamp_mem 0 b hb s).1 hlt (intervalClamp_mem 0 b hb t).2
  all_goals exact hst

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.canonical_interval_kw
