import Chapter12CylinderLp
import Chapter1WrittenConvergence
import Mathlib.MeasureTheory.Function.UniformIntegrable

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The bounded upgrade used in the manuscript's cylinder density proof.
The incoming convergence is the already proved Chapter 1 L2 convergence. -/
theorem bounded_L2_to_Lp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (p : ℝ≥0∞)
    (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (f : ℕ → Lp ℝ 2 P) (g : Lp ℝ 2 P)
    (hlim : Tendsto f atTop (𝓝 g)) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n, ∀ᵐ ω ∂P, |f n ω| ≤ C)
    (hg : ∀ᵐ ω ∂P, |g ω| ≤ C) :
    Tendsto (fun n => eLpNorm (fun ω => f n ω-g ω) p P) atTop (𝓝 0) := by
  have hi : MemLp (g : Ω → ℝ) p P :=
    MemLp.of_bound (Lp.memLp g).aestronglyMeasurable C hg
  have hc : UnifIntegrable (fun _ : ℕ => fun _ : Ω => C) p P :=
    unifIntegrable_const hp hpt (memLp_const C)
  have hui : UnifIntegrable (fun n ω => f n ω) p P :=
    hc.ae_mono (fun n => (Lp.memLp (f n)).aestronglyMeasurable) (fun n => by
      filter_upwards [hf n] with ω hω
      rw [← ofReal_norm,← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs,abs_of_nonneg hC] using hω))
  exact tendsto_Lp_finite_of_tendstoInMeasure hp hpt
    (fun n => (Lp.memLp (f n)).aestronglyMeasurable) hi hui
    (tendstoInMeasure_of_tendsto_Lp hlim)

end Asakura.Chapter12
