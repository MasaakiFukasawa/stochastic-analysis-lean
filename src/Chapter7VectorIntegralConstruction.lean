import Chapter7VectorIntegralCovariances
import Chapter5LocalPathBrownianIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter7
open Asakura.Chapter6 Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- Construct actual vector Brownian integrals from pathwise local square
integrability and progressiveness, allowing the grid integrands of the CLT. -/
theorem locally_square_integrable_vector_integrals
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {noise : ℕ} (B : BrownianSystem P noise)
    (H : Fin noise → Ω × ℝ → ℝ) (hHm : ∀ i,Measurable (H i))
    (hHp : ∀ i b,0 < b → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => H i (z.1,z.2.val)))
    (hi : ∀ i b,0 < b → ∀ᵐ w ∂P,IntervalIntegrable (fun r => H i (w,r)^2) volume 0 b) :
    ∃ N : Fin noise → HalfClosedTime → Ω → ℝ,
      (∀ i,LocalMProcessWitness P B.F (N i)) ∧
      (∀ i,ItoCovarianceFormula P B.F (B.W i) (H i) (N i)) := by
  have hT : (0:EReal) < ⊤ := by simp
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  have hex i : ∃ N : HalfClosedTime → Ω → ℝ,LocalMProcessWitness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W i) (H i) N := by
    apply brownian_local_path_energy_integral_constructed P hT B.F B.mono B.le B.null
      (B.W i) (B.C i i) (B.martingale i) (B.cov i i) c hc hcm hcT hct hcut hcc
    · intro n w r hr
      simpa using B.clock i i w r hr.1
    · exact hHm i
    · intro n
      exact hHp i (c n) (hc n)
    · intro n
      exact hi i (c n) (hc n)
  choose N hN hNI using hex
  exact ⟨N,hN,hNI⟩

end Asakura.Chapter7
