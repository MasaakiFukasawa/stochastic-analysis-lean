import Chapter7ClosedFiniteCLT
import Chapter7ClosedAdaptedness

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4

/-- Endpoint adaptedness is derived from continuity, not required as an
additional assumption in the closed finite-horizon CLT. -/
theorem finite_martingale_clt_written
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a : ℝ≥0) [Fact (0 ≤ ((a:ℝ):EReal))] (ha0 : 0 < a)
    (F : ClosedTime ((a:ℝ):EReal) → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (M C : ℕ → ClosedTime ((a:ℝ):EReal) → Ω → ℝ)
    (hM : ∀ n,LocalMProcessWitness P F (M n))
    (hC : ∀ n,LocalCovarianceWitness P F (M n) (M n) (C n))
    (hMc : ∀ n w,Continuous (fun t => M n t w))
    (hCc : ∀ n w,Continuous (fun t => C n t w))
    (hp : ∀ t : ℝ≥0,t ≤ a → TendstoInMeasure P (fun n => C n (realTimeClamp t)) atTop (fun _ => (t:ℝ))) :
    ∃ (Γ : Type) (q : MeasurableSpace Γ) (Q : Measure Γ) (hQ : IsProbabilityMeasure Q),
    letI := q
    letI := hQ
    ∃ B0 : BrownianSystem (P.prod Q) 1,
      TendstoInDistribution (fun n => finiteClosedPath a (M n) (hMc n)) atTop
        (fun z => pathRestriction a (brownianContinuousPath B0 z)) (fun _ => P) (P.prod Q) := by
  have haE : 0 < ((a:ℝ):EReal) := by exact_mod_cast ha0
  exact closed_finite_martingale_clt P a ha0 F hF hle hnull M C hM hC
    (fun n => closed_adapted_of_open_continuous haE F hF (M n) ((hM n).adapted P F) (hMc n)) hMc
    (fun n => closed_adapted_of_open_continuous haE F hF (C n) ((hC n).adapted P F (hM n) (hM n)) (hCc n)) hCc hp

end Asakura.Chapter7
