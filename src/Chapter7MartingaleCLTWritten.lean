import Chapter7MartingaleCLT
import Chapter7BrownianExists

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4

/-- The half-line statement needs no pre-existing independent noise: the
Brownian probability space is constructed and the original laws converge. -/
theorem martingale_clt_written
    {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (M C : ℕ → HalfClosedTime → Ω → ℝ)
    (hM : ∀ n,LocalMProcessWitness P F (M n))
    (hC : ∀ n,LocalCovarianceWitness P F (M n) (M n) (C n))
    (hp : ∀ t : ℝ≥0,TendstoInMeasure P (fun n => C n (realTimeClamp t)) atTop (fun _ => (t:ℝ))) :
    ∃ (Γ : Type) (q : MeasurableSpace Γ) (Q : Measure Γ) (hQ : IsProbabilityMeasure Q),
    letI := q
    letI := hQ
    ∃ B0 : BrownianSystem (P.prod Q) 1,
      TendstoInDistribution (fun n => localContinuousPath (M n) ((hM n).path P F)) atTop
        (brownianContinuousPath B0) (fun _ => P) (P.prod Q) := by
  obtain ⟨Γ,q,Q,hQ,⟨B⟩⟩ := brownian_system_exists
  letI := q
  letI := hQ
  obtain ⟨B0,hlim⟩ := martingale_clt_with_independent_driver P Q F hF hle M C hM hC hp B
  exact ⟨Γ,q,Q,hQ,B0,hlim⟩

end Asakura.Chapter7
