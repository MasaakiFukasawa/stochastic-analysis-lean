import Chapter6BoundedVectorCovariance
import Chapter5LocalPathBrownianIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- Construction of the density martingale from continuous progressively measurable
vector coefficients, without a deterministic bound on them. -/
theorem continuous_vector_integrals_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {noise : ℕ} (B : BrownianSystem P noise)
    (H : Fin noise → Ω × ℝ → ℝ) (hHm : ∀ i,Measurable (H i))
    (hHp : ∀ i b,0 < b → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => H i (z.1,z.2.val)))
    (hHc : ∀ i w,Continuous (fun r => H i (w,r))) :
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
      exact ae_of_all _ fun w => by
        exact (((hHc i w).pow 2).continuousOn.intervalIntegrable_of_Icc (μ := volume) (hc n).le)
  choose N hN hNI using hex
  exact ⟨N,hN,hNI⟩

end Asakura.Chapter6
