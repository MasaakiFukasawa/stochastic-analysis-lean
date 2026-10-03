import Chapter8MartingaleCLTVarying
import Chapter7BrownianExists

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace Asakura.Chapter8
open Asakura.Chapter7 Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4

/-- The chapter-7 CLT with a separate filtration for each row, as required
by the long-time rescaling M_(T_n t)/sqrt(T_n). The Brownian extension is
constructed, and no common martingale filtration is presumed. -/
theorem martingale_clt_varying_filtration_written
    {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → HalfClosedTime → MeasurableSpace Ω)
    (hF : ∀ n,Monotone (F n)) (hle : ∀ n t,F n t ≤ m)
    (M C : ℕ → HalfClosedTime → Ω → ℝ)
    (hM : ∀ n,LocalMProcessWitness P (F n) (M n))
    (hC : ∀ n,LocalCovarianceWitness P (F n) (M n) (M n) (C n))
    (hp : ∀ t : ℝ≥0,TendstoInMeasure P (fun n => C n (realTimeClamp t)) atTop (fun _ => (t:ℝ))) :
    ∃ (Γ : Type) (q : MeasurableSpace Γ) (Q : Measure Γ) (hQ : IsProbabilityMeasure Q),
    letI := q
    letI := hQ
    ∃ B0 : BrownianSystem (P.prod Q) 1,
      TendstoInDistribution (fun n => localContinuousPath (M n) ((hM n).path P (F n))) atTop
        (brownianContinuousPath B0) (fun _ => P) (P.prod Q) := by
  obtain ⟨Γ,q,Q,hQ,⟨B⟩⟩ := brownian_system_exists
  letI := q
  letI := hQ
  obtain ⟨B0,hlim⟩ := martingale_clt_varying_filtration_with_driver P Q F hF hle M C hM hC hp B
  exact ⟨Γ,q,Q,hQ,B0,hlim⟩

end Asakura.Chapter8
