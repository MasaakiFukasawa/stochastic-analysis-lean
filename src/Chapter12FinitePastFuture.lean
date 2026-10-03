import Chapter12BrownianCylinderDensity
import Chapter12PastFutureDirections

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- The actual scalar time directions used in the finite Wiener map are
orthogonal when one is supported before a and the other after a. -/
theorem finite_interval_past_future (T s a b : ℝ) (hsa : s ≤ a) :
    ⟪finiteTimeIntervalVector T 0 s,finiteTimeIntervalVector T a b⟫ = 0 := by
  apply past_future_time_orthogonal _ a
  · have he : (finiteTimeIntervalVector T 0 s : ℝ → ℝ) =ᵐ[(volume.restrict (Ioi (0:ℝ))).restrict (Iic T)]
        (Ioc 0 s).indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
    filter_upwards [he] with t ht
    intro hat
    rw [ht]
    exact indicator_of_notMem (by intro h; exact (not_le.mpr (hsa.trans_lt hat)) h.2) _
  · have he : (finiteTimeIntervalVector T a b : ℝ → ℝ) =ᵐ[(volume.restrict (Ioi (0:ℝ))).restrict (Iic T)]
        (Ioc a b).indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
    filter_upwards [he] with t ht
    intro hta
    rw [ht]
    exact indicator_of_notMem (by intro h; exact (not_lt.mpr hta) h.1) _

/-- This includes arbitrary coordinate indices in the multidimensional
Brownian system, with the same half-open interval convention as Ito integration. -/
theorem finite_brownian_past_future {d : ℕ} {T : ℝ}
    (z : BrownianTimeCoordinates d T) (i : Fin (d+1)) (a b : ℝ) (hza : z.2.val ≤ a) :
    inner ℝ (brownianTimeDirection z)
      (WithLp.toLp 2 (Pi.single i (finiteTimeIntervalVector T a b)) : FiniteWienerHilbert d T) = 0 := by
  classical
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro j _
  change inner ℝ ((Pi.single z.1 (finiteTimeIntervalVector T 0 z.2.val) : Fin (d+1) → _) j)
    ((Pi.single i (finiteTimeIntervalVector T a b) : Fin (d+1) → _) j) = 0
  by_cases hj : j = z.1
  · subst j
    by_cases hi : z.1 = i
    · subst i
      simpa only [Pi.single_eq_same] using finite_interval_past_future T z.2.val a b hza
    · simp [Pi.single_eq_of_ne hi]
  · simp [Pi.single_eq_of_ne hj]

end Asakura.Chapter12
