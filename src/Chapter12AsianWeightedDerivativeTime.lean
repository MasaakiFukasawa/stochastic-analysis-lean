import Chapter12AsianDerivativeTime

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Random scalar factors, including the exercise indicator, commute with
the time realization of the stock-moment derivative. -/
theorem asian_weighted_moment_derivative_time {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (i : Fin (d+1))
    (T : ℝ) (hT : 0≤T) (x σ r : ℝ) (j : ℕ)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X)
    (q : Ω → ℝ) (hqm : Measurable q)
    (U : Lp (FiniteWienerHilbert d T) 2 P)
    (hU : (U : Ω → FiniteWienerHilbert d T) =ᵐ[P]
      (fun w => q w • asianMomentGradient T hT x σ r j (fun t => brownianTimeDirection (i,t)) (X w))) :
    (brownianDerivativeTime P T hT U i : Ω × Icc (0:ℝ) T → ℝ) =ᵐ[P.prod (compactTimeMeasure T hT)]
      (fun z => q z.1*(σ*asianRemainingMoment T hT x σ r j (X z.1) z.2)) := by
  have hc := (brownianCoordinateProjection T i).coeFn_compLp U
  have hr := timeRealization_coe P T hT ((brownianCoordinateProjection T i).compLp U)
  have hm := (hqm.comp measurable_fst).mul
    (((asian_remaining_moment_measurable T hT x σ r j).comp
      ((hXm.comp measurable_fst).prodMk measurable_snd)).const_mul σ)
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (Lp.stronglyMeasurable (brownianDerivativeTime P T hT U i)).measurable hm)).mpr
  filter_upwards [hc,hr,hU] with w hcw hrw huw
  rw [hcw,huw,map_smul,map_smul] at hrw
  have hsc := Lp.coeFn_smul (q w) (finiteTimeToCompact T hT (brownianCoordinateProjection T i
    (asianMomentGradient T hT x σ r j (fun t => brownianTimeDirection (i,t)) (X w))))
  filter_upwards [hrw,hsc,asian_moment_time_kernel i T hT x σ r j (X w)] with t ht hs hk
  change timeRealization P T hT ((brownianCoordinateProjection T i).compLp U) (w,t) =
    q w*(σ*asianRemainingMoment T hT x σ r j (X w) t)
  rw [ht,hs,Pi.smul_apply,smul_eq_mul,hk]
  rfl

end Asakura.Chapter12
