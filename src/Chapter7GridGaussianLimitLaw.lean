import Chapter7BrownianQuadraticStatistic
import Chapter7BrownianProjectionLaw

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

lemma scaled_brownian_gaussian_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (c t : ℝ) (hc : 0≤c) (ht : 0≤t) :
    HasLaw (fun w => Real.sqrt c*B.W 0 (realTimeClamp t) w)
      (gaussianReal 0 ⟨c*t,mul_nonneg hc ht⟩) P := by
  have hLaw := (brownian_projection_law P B 0 t le_rfl ht (fun _ => Real.sqrt c)).1
  have hv : (⟨(t-0)*(∑ _i : Fin 1,(Real.sqrt c)^2),
      mul_nonneg (sub_nonneg.mpr ht) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))⟩ : ℝ≥0)=
      ⟨c*t,mul_nonneg hc ht⟩ := by
    apply NNReal.eq
    simp only [sub_zero,Fin.sum_univ_one,Real.sq_sqrt hc]
    ring
  rw [hv] at hLaw
  apply hLaw.congr
  have hz : realTimeClamp 0=(⊥ : HalfClosedTime) := by apply Subtype.ext; simp [realTimeClamp]
  filter_upwards [(B.martingale 0).initial P B.F] with w hw
  simp only [Fin.sum_univ_one,hz,hw,Pi.zero_apply,sub_zero]

end Asakura.Chapter7
