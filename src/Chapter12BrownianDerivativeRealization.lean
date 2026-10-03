import Chapter12DerivativeTimeRealization
import Chapter12BrownianCylinderDensity

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

noncomputable def brownianCoordinateProjection {d : ℕ} (T : ℝ) (i : Fin (d+1)) :
    FiniteWienerHilbert d T →L[ℝ] Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)) :=
  PiLp.proj 2 (fun _ : Fin (d+1) => Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) i

theorem brownian_interval_inner {d : ℕ} (T : ℝ) (i : Fin (d+1)) (a b : ℝ)
    (u : FiniteWienerHilbert d T) :
    inner ℝ u (WithLp.toLp 2 (Pi.single i (finiteTimeIntervalVector T a b))) =
      inner ℝ (brownianCoordinateProjection T i u) (finiteTimeIntervalVector T a b) := by
  classical
  rw [PiLp.inner_apply,Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same]
    rfl
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

noncomputable def brownianDerivativeTime {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ} (T : ℝ) (hT : 0 ≤ T)
    (U : Lp (FiniteWienerHilbert d T) 2 P) (i : Fin (d+1)) :
    Lp ℝ 2 (P.prod (compactTimeMeasure T hT)) :=
  timeRealization P T hT ((brownianCoordinateProjection T i).compLp U)

theorem brownian_derivative_interval_test {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ} (T : ℝ) (hT : 0 ≤ T)
    (U : Lp (FiniteWienerHilbert d T) 2 P) (i : Fin (d+1))
    (a b : Icc (0:ℝ) T) (G : Ω → ℝ) (hG : MemLp G 2 P) :
    (∫ w,G w*inner ℝ (U w) (WithLp.toLp 2 (Pi.single i (finiteTimeIntervalVector T a b))) ∂P) =
      ∫ z,brownianDerivativeTime P T hT U i z*(Ico a b).indicator (fun _ => G z.1) z.2
        ∂P.prod (compactTimeMeasure T hT) := by
  have hc := (brownianCoordinateProjection T i).coeFn_compLp U
  calc
    _ = ∫ w,G w*inner ℝ ((brownianCoordinateProjection T i).compLp U w)
        (finiteTimeIntervalVector T a b) ∂P := by
      apply integral_congr_ae
      filter_upwards [hc] with w hw
      rw [brownian_interval_inner,hw]
    _ = _ := timeRealization_interval_test P T hT _ a b G hG

end Asakura.Chapter12
