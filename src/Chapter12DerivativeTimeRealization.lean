import Chapter12L2SectionSurjective
import Chapter12FiniteCompactTime

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

noncomputable def timeRealization {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (T : ℝ) (hT : 0 ≤ T)
    (U : Lp (Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) 2 P) :
    Lp ℝ 2 (P.prod (compactTimeMeasure T hT)) :=
  (l2SectionsEquiv P (compactTimeMeasure T hT)).symm
    ((finiteTimeToCompact T hT).toContinuousLinearMap.compLp U)

theorem timeRealization_coe {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (T : ℝ) (hT : 0 ≤ T)
    (U : Lp (Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) 2 P) :
    ∀ᵐ w ∂P, (fun t => timeRealization P T hT U (w,t)) =ᵐ[compactTimeMeasure T hT]
      (finiteTimeToCompact T hT (U w) : Icc (0:ℝ) T → ℝ) := by
  let v := (finiteTimeToCompact T hT).toContinuousLinearMap.compLp U
  let f := timeRealization P T hT U
  have he : l2SectionLp P (compactTimeMeasure T hT) f = v :=
    (l2SectionsEquiv P (compactTimeMeasure T hT)).apply_symm_apply v
  have hc := l2SectionLp_coe P (compactTimeMeasure T hT) f
  rw [he] at hc
  filter_upwards [hc,(finiteTimeToCompact T hT).toContinuousLinearMap.coeFn_compLp U] with w hw hv
  change (v w : Icc (0:ℝ) T → ℝ) =ᵐ[compactTimeMeasure T hT] _ at hw
  rw [show v w = finiteTimeToCompact T hT (U w) from hv] at hw
  exact hw.symm

/-- The time realization turns the directional pairing in Gaussian IBP
into exactly the joint-space step test used for the adapted projection. -/
theorem timeRealization_interval_test {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (T : ℝ) (hT : 0 ≤ T)
    (U : Lp (Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) 2 P)
    (a b : Icc (0:ℝ) T) (G : Ω → ℝ) (hG : MemLp G 2 P) :
    (∫ w,G w*inner ℝ (U w) (finiteTimeIntervalVector T a b) ∂P) =
      ∫ z,timeRealization P T hT U z*(Ico a b).indicator (fun _ => G z.1) z.2
        ∂P.prod (compactTimeMeasure T hT) := by
  let μ := compactTimeMeasure T hT
  let f := timeRealization P T hT U
  have hstep : MemLp (fun z : Ω × Icc (0:ℝ) T => (Ico a b).indicator (fun _ => G z.1) z.2)
      2 (P.prod μ) := by
    have hh := (hG.comp_fst μ).indicator (MeasurableSet.univ.prod (measurableSet_Ico (a := a) (b := b)))
    convert hh using 1
    funext z
    by_cases hz : z.2 ∈ Ico a b <;> simp [hz]
  have hi : Integrable (fun z => f z*(Ico a b).indicator (fun _ => G z.1) z.2) (P.prod μ) :=
    (Lp.memLp f).integrable_mul hstep
  change _ = ∫ z,f z*(Ico a b).indicator (fun _ => G z.1) z.2 ∂P.prod μ
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [timeRealization_coe P T hT U] with w hw
  rw [finite_compact_interval_inner T hT a b (U w)]
  calc
    _ = ∫ t in Ico a b, G w*finiteTimeToCompact T hT (U w) t ∂μ :=
      (integral_const_mul _ _).symm
    _ = ∫ t,(Ico a b).indicator (fun t => G w*finiteTimeToCompact T hT (U w) t) t ∂μ :=
      (integral_indicator measurableSet_Ico).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hw] with t ht
      rw [ht]
      by_cases h : t ∈ Ico a b <;> simp [h,mul_comm]

end Asakura.Chapter12
