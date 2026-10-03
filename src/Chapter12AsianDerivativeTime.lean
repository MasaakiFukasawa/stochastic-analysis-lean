import Chapter12AsianRemainingMoment

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- The actual joint L2 realization of the H-valued moment derivative is
sigma times the remaining stock-price moment, not merely a directional pairing. -/
theorem asian_moment_derivative_time {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (i : Fin (d+1))
    (T : ℝ) (hT : 0≤T) (x σ r : ℝ) (j : ℕ)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X)
    (U : Lp (FiniteWienerHilbert d T) 2 P)
    (hU : (U : Ω → FiniteWienerHilbert d T) =ᵐ[P]
      (fun w => asianMomentGradient T hT x σ r j (fun t => brownianTimeDirection (i,t)) (X w))) :
    (brownianDerivativeTime P T hT U i : Ω × Icc (0:ℝ) T → ℝ) =ᵐ[P.prod (compactTimeMeasure T hT)]
      (fun z => σ*asianRemainingMoment T hT x σ r j (X z.1) z.2) := by
  have hc := (brownianCoordinateProjection T i).coeFn_compLp U
  have hr := timeRealization_coe P T hT ((brownianCoordinateProjection T i).compLp U)
  have hm := ((asian_remaining_moment_measurable T hT x σ r j).comp
    ((hXm.comp measurable_fst).prodMk measurable_snd)).const_mul σ
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (Lp.stronglyMeasurable (brownianDerivativeTime P T hT U i)).measurable hm)).mpr
  filter_upwards [hc,hr,hU] with w hcw hrw huw
  rw [hcw,huw] at hrw
  exact hrw.trans (asian_moment_time_kernel i T hT x σ r j (X w))

end Asakura.Chapter12
