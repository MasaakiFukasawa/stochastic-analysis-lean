import FullAuditDiscreteVariation

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Asakura.EndToEnd

/-- The discrete total variation theorem with the successive refinement and
generating-union assumptions used in the manuscript. -/
theorem discrete_variation
    {Ω : Type*} {m : MeasurableSpace Ω}
    (ν : SignedMeasure Ω) (J : ℕ → Finpartition (univ : Set Ω))
    (hJ : ∀ n, ∀ E ∈ (J n).parts, MeasurableSet E)
    (href : ∀ n, J (n + 1) ≤ J n)
    (hgen : MeasurableSpace.generateFrom
      (⋃ n, ((J n).parts : Set (Set Ω))) = m) :
    Monotone (fun n => ∑ E ∈ (J n).parts, |ν E|) ∧
    Tendsto (fun n => ∑ E ∈ (J n).parts, |ν E|)
      atTop (𝓝 (ν.totalVariation.real univ)) := by
  apply Asakura.FullAudit.discrete_variation_written ν J hJ
    (antitone_nat_of_succ_le href)
  rwa [Asakura.FullAudit.partition_generating_union] at hgen

end Asakura.EndToEnd

#print axioms Asakura.EndToEnd.discrete_variation
