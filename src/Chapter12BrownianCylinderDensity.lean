import Chapter12FiniteWienerIndicator
import Chapter12FiniteWienerNontrivial
import Chapter12ConcreteCylinderDensity

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

abbrev FiniteWienerHilbert (d : ℕ) (T : ℝ) :=
  PiLp 2 (fun _ : Fin (d+1) => Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)))

abbrev BrownianTimeCoordinates (d : ℕ) (T : ℝ) := Fin (d+1) × Icc (0:ℝ) T

noncomputable def brownianTimeCoordinate {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (B : BrownianSystem P (d+1)) (T : ℝ) (z : BrownianTimeCoordinates d T) : Ω → ℝ :=
  B.W z.1 (realTimeClamp z.2.val)

noncomputable def brownianTimeDirection {d : ℕ} {T : ℝ}
    (z : BrownianTimeCoordinates d T) : FiniteWienerHilbert d T :=
  WithLp.toLp 2 (Pi.single z.1 (finiteTimeIntervalVector T 0 z.2.val))


theorem brownian_time_coordinate_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (B : BrownianSystem P (d+1)) (T : ℝ) (z : BrownianTimeCoordinates d T) :
    Measurable[B.F (realTimeClamp T)] (brownianTimeCoordinate P B T z) := by
  have hf : realTimeClamp (T := (⊤:EReal)) z.2.val < ⊤ := by
    change (realTimeClamp (T := (⊤:EReal)) z.2.val).val < (⊤:EReal)
    rw [real_time_clamp_eq _ z.2.property.1 le_top]
    exact EReal.coe_lt_top _
  exact ((B.martingale z.1).adapted P B.F _ hf).mono
    (B.mono (real_time_clamp_mono z.2.property.2)) le_rfl

theorem brownian_time_coordinate_continuous {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (B : BrownianSystem P (d+1)) (T : ℝ) (w : Ω) :
    Continuous (fun z => brownianTimeCoordinate P B T z w) := by
  apply continuous_prod_of_discrete_left.mpr
  intro i
  apply continuous_iff_continuousAt.mpr
  intro t
  have hf : realTimeClamp (T := (⊤:EReal)) t.val < ⊤ := by
    change (realTimeClamp (T := (⊤:EReal)) t.val).val < (⊤:EReal)
    rw [real_time_clamp_eq _ t.property.1 le_top]
    exact EReal.coe_lt_top _
  exact ((B.martingale i).path P B.F w _ hf).comp
    (f := fun s : Icc (0:ℝ) T => realTimeClamp s.val)
    (real_time_clamp_continuous.comp continuous_subtype_val).continuousAt

end Asakura.Chapter12
