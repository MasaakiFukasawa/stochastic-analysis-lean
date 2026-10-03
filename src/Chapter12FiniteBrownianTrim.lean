import Chapter12BrownianCylinderDensity
import Chapter12FiniteWienerInformation
import Chapter12TrimWiener

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Wiener integration on the probability space restricted to F_T. Future
Brownian information is not assumed to belong to the terminal sigma algebra. -/
theorem finite_brownian_trim_wiener {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (B : BrownianSystem P (d+1)) (T : ℝ) (hT : 0 ≤ T) :
    ∃ W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 (P.trim (B.le (realTimeClamp T))),
      (∀ h, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩)
        (P.trim (B.le (realTimeClamp T)))) ∧
      (∀ z, brownianTimeCoordinate P B T z =ᵐ[P.trim (B.le (realTimeClamp T))]
        (W (brownianTimeDirection z) : Ω → ℝ)) := by
  obtain ⟨I,hG,hmeas,hinc⟩ := finite_horizon_wiener_information P B T hT
  obtain ⟨W,he,hW⟩ := wiener_isometry_on_trim P _ (B.le (realTimeClamp T)) I hmeas hG
  refine ⟨W,hW,fun z => ?_⟩
  have hzero : realTimeClamp (T := (⊤:EReal)) 0 = ⊥ :=
    Subtype.ext (real_time_clamp_eq 0 le_rfl le_top)
  have hx : brownianTimeCoordinate P B T z =ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ) := by
    have h := hinc z.1 0 z.2.val le_rfl z.2.property.1 z.2.property.2
    rw [hzero] at h
    filter_upwards [h,(B.martingale z.1).initial P B.F,he (brownianTimeDirection z)] with w hw h0 hew
    change B.W z.1 (realTimeClamp z.2.val) w = _
    dsimp only [brownianTimeDirection] at hew ⊢
    rw [hew,hw,h0]
    simp
  exact (brownian_time_coordinate_measurable P B T z).stronglyMeasurable.ae_eq_trim_of_stronglyMeasurable
    (B.le (realTimeClamp T)) (Lp.stronglyMeasurable (W (brownianTimeDirection z))) hx

end Asakura.Chapter12
