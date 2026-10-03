import Chapter5GaussianCoordinateIBPIntegrable
import Chapter5GaussianDirections
import FullAuditGaussianGrowth

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter5
open Asakura.FullAudit
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

lemma lipschitz_affine_average_memLp_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [IsProbabilityMeasure ν]
    (hi : MemLp (fun z : E => z) 2 ν) (f : E → ℝ) (C : ℝ≥0) (hl : LipschitzWith C f)
    (x : E) (s : ℝ) : MemLp (fun z => f (x+s • z)) 2 ν := by
  have hu : MemLp (fun z => x+s • z) 2 ν := (memLp_const x).add (hi.const_smul s)
  have hlf : LipschitzWith C (fun y => f y-f 0) := LipschitzWith.of_dist_le_mul fun a b => by
    simpa only [dist_eq_norm,sub_sub_sub_cancel_right] using hl.dist_le_mul a b
  have hf := hlf.comp_memLp (sub_self (f 0)) hu
  convert hf.add (memLp_const (f 0)) using 1
  funext z
  simp only [Function.comp_def,Pi.add_apply,sub_add_cancel]

/-- The growth allowed by a bounded gradient supplies the Gaussian
integrability needed by integration by parts, including the linear
Gaussian factor. No bound on f itself or its Hessian is used. -/
lemma gaussian_lipschitz_coordinate_integrable
    (n : ℕ) (i : Fin (n+1)) (f : (Fin (n+1) → ℝ) → ℝ)
    (C : ℝ≥0) (hl : LipschitzWith C f) (x : Fin (n+1) → ℝ) (t : ℝ) :
    Integrable (fun z => z i*f (x+Real.sqrt t • z)) (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) := by
  have hi : MemLp (fun z : Fin (n+1) → ℝ => z) 2 (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) :=
    finite_gaussian_all_moments 2 (by norm_num)
  have hz := (LipschitzWith.eval (α := fun _ : Fin (n+1) => ℝ) i).comp_memLp (by simp) hi
  exact hz.integrable_mul (lipschitz_affine_average_memLp_two _ hi f C hl x (Real.sqrt t))

end Asakura.Chapter5
