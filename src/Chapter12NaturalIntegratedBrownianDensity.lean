import Chapter12IntegratedBrownianDensity
import Chapter12FiniteWienerInformation
import Chapter12NaturalBrownianInformation
import Chapter12SingleCoordinateIsometry

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- The example's smooth positive density, starting only with an actual
continuous Brownian motion. No Wiener-map, covariance, or density hypotheses
are left to the caller. -/
theorem natural_integrated_brownian_smooth_density {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t,Measurable (B t))
    (hc : ∀ w,Continuous (fun t => B t w)) (T : ℝ≥0) (hT : 0<T) :
    ∃ ρ : (Fin 2 → ℝ) → ℝ,ContDiff ℝ ⊤ ρ ∧ (∀ x,0<ρ x) ∧
      HasLaw (fun w => ![B T w,
        ∫ t : Icc (0:ℝ) T,B ⟨t.val,t.property.1⟩ w ∂compactTimeMeasure T T.property])
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) P := by
  let BS := naturalBrownianSystem P B hB hm hc
  obtain ⟨I,hI,hIm,hinc⟩ := finite_horizon_wiener_information P BS T T.property
  let J := singleCoordinateIsometry (H := Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic (T:ℝ)))) (0 : Fin 1)
  let W := I.comp J
  have hW (h) : HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P := by
    change HasLaw (I (J h) : Ω → ℝ) _ P
    simpa only [J.norm_map] using hI (J h)
  let X := fun z : Icc (0:ℝ) T × Ω => B ⟨z.1.val,z.1.property.1⟩ z.2
  have hXm : Measurable X := by
    change Measurable (Function.uncurry (fun t : Icc (0:ℝ) T => B ⟨t.val,t.property.1⟩))
    apply measurable_uncurry_of_continuous_of_measurable
    · intro w
      exact (hc w).comp (continuous_subtype_val.subtype_mk (fun t : Icc (0:ℝ) T => t.property.1))
    · intro t
      exact hm _
  have he (t : Icc (0:ℝ) T) : (W (finiteTimeIntervalVector T 0 t.val) : Ω → ℝ) =ᵐ[P]
      (fun w => X (t,w)) := by
    have hh := hinc 0 0 t.val le_rfl t.property.1 t.property.2
    have hz : realTimeClamp (T := (⊤:EReal)) 0=⊥ :=
      Subtype.ext (real_time_clamp_eq 0 le_rfl le_top)
    rw [hz] at hh
    filter_upwards [hh,(BS.martingale 0).initial P BS.F] with w hw h0
    change I (J (finiteTimeIntervalVector T 0 t.val)) w=X (t,w)
    change I (J (finiteTimeIntervalVector T 0 t.val)) w=_ at hw
    rw [hw,h0]
    simp only [Pi.zero_apply,sub_zero]
    exact natural_brownian_coordinate P B hB hm hc T (0,t) w
  obtain ⟨ρ,hs,hp,hl⟩ := integrated_brownian_smooth_density P T (show (0:ℝ)<T from hT) W hW X hXm he
  exact ⟨ρ,hs,hp,hl⟩

end Asakura.Chapter12
