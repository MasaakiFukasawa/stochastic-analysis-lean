import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Probability.Notation

open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 1600000

theorem lipschitz_sub_constant {E F : Type*} [PseudoMetricSpace E]
    [NormedAddCommGroup F] (g : E → F) (K : ℝ≥0) (hg : LipschitzWith K g) (a : F) :
    LipschitzWith K (fun x => g x-a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_sub_right] using hg.dist_le_mul x y

noncomputable def finiteLpComposition {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (P : Measure Ω) [IsFiniteMeasure P] (p : ℝ≥0∞)
    (g : E → F) (K : ℝ≥0) (hg : LipschitzWith K g) (u : Lp E p P) : Lp F p P :=
  (lipschitz_sub_constant g K hg (g 0)).compLp (sub_self _) u+(memLp_const (g 0)).toLp (fun _ : Ω => g 0)

theorem finiteLpComposition_coe {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (P : Measure Ω) [IsFiniteMeasure P] (p : ℝ≥0∞)
    (g : E → F) (K : ℝ≥0) (hg : LipschitzWith K g) (u : Lp E p P) :
    (finiteLpComposition P p g K hg u : Ω → F)=ᵐ[P] (fun w => g (u w)) := by
  unfold finiteLpComposition
  filter_upwards [Lp.coeFn_add ((lipschitz_sub_constant g K hg (g 0)).compLp (sub_self _) u)
      ((memLp_const (g 0)).toLp (fun _ : Ω => g 0)),
    (lipschitz_sub_constant g K hg (g 0)).coeFn_compLp (sub_self _) u,
    (memLp_const (g 0)).coeFn_toLp] with w ha hb hc
  rw [ha,Pi.add_apply,hb,hc]
  exact sub_add_cancel _ _

theorem finiteLpComposition_continuous {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (P : Measure Ω) [IsFiniteMeasure P] (p : ℝ≥0∞) [Fact (1≤p)]
    (g : E → F) (K : ℝ≥0) (hg : LipschitzWith K g) :
    Continuous (finiteLpComposition P p g K hg) :=
  ((lipschitz_sub_constant g K hg (g 0)).continuous_compLp (sub_self _)).add continuous_const
end Asakura.Chapter12
#print axioms Asakura.Chapter12.finiteLpComposition_continuous
