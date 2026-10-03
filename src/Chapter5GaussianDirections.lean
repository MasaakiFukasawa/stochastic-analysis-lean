import Chapter5GaussianCoordinateIBP
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem gaussian_product_first_moment (d : ℕ) :
    Integrable (fun z : Fin d → ℝ => z) (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  apply integrable_pi_iff.mpr
  intro i
  exact integrable_comp_eval (μ := fun _ : Fin d => gaussianReal 0 1) (i := i) (f := fun z : ℝ => z)
    ((memLp_id_gaussianReal' 1 (by norm_num)).integrable (by norm_num))

theorem insertNth_hasDerivAt (n : ℕ) (i : Fin (n+1)) (x : Fin n → ℝ) (y : ℝ) :
    HasDerivAt (fun u : ℝ => (i.insertNth u x : Fin (n+1) → ℝ))
      (Pi.single i 1 : Fin (n+1) → ℝ) y := by
  apply hasDerivAt_pi.mpr
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Fin.insertNth_apply_same,Pi.single_eq_same] using hasDerivAt_id' y
  · obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq hj
    rw [← hk]
    simpa using hasDerivAt_const y (x k)

end Asakura.Chapter5
