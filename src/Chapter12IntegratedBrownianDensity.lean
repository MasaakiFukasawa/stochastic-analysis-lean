import Chapter12IntegratedBrownianGram
import Chapter12IntegratedWienerCoordinate
import Chapter12TwoWienerSmoothDensity

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

/-- The two coordinates in the example have an everywhere positive smooth
density; the time integral here is of the original Brownian coordinates. -/
theorem integrated_brownian_smooth_density {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (hT : 0<T)
    (W : Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hlaw : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (B : Icc (0:ℝ) T × Ω → ℝ) (hm : Measurable B)
    (he : ∀ t,(W (finiteTimeIntervalVector T 0 t.val) : Ω → ℝ) =ᵐ[P] (fun w => B (t,w))) :
    ∃ ρ : (Fin 2 → ℝ) → ℝ,ContDiff ℝ ⊤ ρ ∧ (∀ x,0<ρ x) ∧
      HasLaw (fun w => ![B (⟨T,hT.le,le_rfl⟩,w),
        ∫ t : Icc (0:ℝ) T,B (t,w) ∂compactTimeMeasure T hT.le])
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) P := by
  have hb : Real.sqrt T≠0 := (Real.sqrt_pos.mpr hT).ne'
  have hc : Real.sqrt (T^3/12)≠0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hbb := Real.sq_sqrt hT.le
  have hcc := Real.sq_sqrt (show 0≤T^3/12 by positivity)
  obtain ⟨ρ,hs,hp,hl⟩ := two_wiener_smooth_positive_density P W hlaw
    (finiteTimeIntervalVector T 0 T) (integratedBrownianDirection T hT.le)
    (T/2) (Real.sqrt T) (Real.sqrt (T^3/12)) hb hc
    (by rw [hbb]; exact finite_prefix_terminal_inner T T hT.le le_rfl)
    (by rw [hbb,integrated_brownian_cross_inner T hT.le]; ring)
    (by rw [hbb,hcc,integrated_brownian_direction_inner T hT.le]; ring)
  refine ⟨ρ,hs,hp,hl.congr ?_⟩
  filter_upwards [he ⟨T,hT.le,le_rfl⟩,integrated_wiener_coordinate P T hT.le W B hm he]
    with w ht hi
  funext i
  fin_cases i
  · exact ht.symm
  · exact hi.symm

end Asakura.Chapter12
