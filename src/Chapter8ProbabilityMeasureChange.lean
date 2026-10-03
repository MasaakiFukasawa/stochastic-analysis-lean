import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Filter
open scoped Topology
namespace Asakura.Chapter8

/-- Convergence in probability transfers to an absolutely continuous
finite measure; no square-integrable likelihood ratio is required. -/
theorem probability_absolutely_continuous {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (P Q : Measure Ω) [IsFiniteMeasure Q]
    (hQP : Q ≪ P) (X : ℕ → Ω → E) (Y : Ω → E)
    (hX : ∀ n,AEStronglyMeasurable (X n) Q)
    (hlim : TendstoInMeasure P X atTop Y) : TendstoInMeasure Q X atTop Y := by
  apply (exists_seq_tendstoInMeasure_atTop_iff hX).mpr
  intro ns hns
  obtain ⟨ms,hms,hae⟩ := (hlim.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  exact ⟨ms,hms,hQP.ae_le hae⟩
end Asakura.Chapter8
