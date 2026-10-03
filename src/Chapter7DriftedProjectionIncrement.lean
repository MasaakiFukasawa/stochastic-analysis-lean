import Chapter7DriftCovarianceEntry

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4

noncomputable def driftedProjectionProcess {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (b : ℝ → Ω → ℝ) (x : Ω → ℝ) (t : ℝ) (w : Ω) : ℝ :=
    x w+(∫ r in 0..t,b r w)+∑ j,u j*B.W j (realTimeClamp t) w

lemma drifted_projection_increment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (b : ℝ → Ω → ℝ) (x : Ω → ℝ)
    (hbc : ∀ w,Continuous (fun r => b r w)) (s t : ℝ) (w : Ω) :
    driftedProjectionProcess B u b x t w-driftedProjectionProcess B u b x s w=
      (∫ r in s..t,b r w)+∑ j,u j*(B.W j (realTimeClamp t) w-B.W j (realTimeClamp s) w) := by
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hbc w).intervalIntegrable 0 s) ((hbc w).intervalIntegrable s t)
  dsimp only [driftedProjectionProcess]
  simp only [mul_sub,sum_sub_distrib]
  linarith

noncomputable def realizedProcessEntry {Ω : Type*} (X Y : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (w : Ω) : ℝ :=
  (1/T)*∑ k : Fin n,(X (((k:ℝ)+1)*(T/n)) w-X ((k:ℝ)*(T/n)) w)*
    (Y (((k:ℝ)+1)*(T/n)) w-Y ((k:ℝ)*(T/n)) w)

end Asakura.Chapter7
