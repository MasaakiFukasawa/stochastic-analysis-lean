import Chapter12BoundedLpConvergence

open MeasureTheory Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The dominated convergence step used when smoothing a fixed random
variable and its derivative. -/
theorem dominated_Lp_limit {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (P : Measure Ω) [IsFiniteMeasure P]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (f : ℕ → Ω → E) (g : Ω → E) (B : Ω → E) (hB : MemLp B p P)
    (hf : ∀ n, AEStronglyMeasurable (f n) P) (hg : MemLp g p P)
    (hb : ∀ n, ∀ᵐ w ∂P, ‖f n w‖ ≤ ‖B w‖)
    (ht : ∀ᵐ w ∂P, Tendsto (fun n => f n w) atTop (𝓝 (g w))) :
    Tendsto (fun n => eLpNorm (f n-g) p P) atTop (𝓝 0) := by
  apply tendsto_Lp_finite_of_tendsto_ae hp hpt hf hg
  · exact (unifIntegrable_const hp hpt hB).ae_mono hf (fun n => (hb n).mono fun w hw => by
      dsimp only
      rw [← ofReal_norm,← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hw)
  · exact ht

end Asakura.Chapter12
