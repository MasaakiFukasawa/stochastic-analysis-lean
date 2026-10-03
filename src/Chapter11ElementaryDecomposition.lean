import Chapter11SignedStepCumulative

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter2Complete
set_option maxHeartbeats 1600000

/-- The elementary sums depend on the price increments, not on the
 semimartingale decomposition or the probability measure. -/
theorem elementary_gains_decomposition {ι : Type*} (ξ : SignedMeasure ℝ)
    [NullSingletonClass ξ.totalVariation] (s : Finset ι) (a b G : ι → ℝ)
    (hab : ∀ i∈s,a i≤b i) (d : ℝ) (A M N : ℝ → ℝ)
    (hξ : ∀ i∈s,ξ (Ioc (min (a i) d) (min (b i) d))=A (min (b i) d)-A (min (a i) d))
    (he : ∀ i∈s,N (min (b i) d)-N (min (a i) d)=
      (M (min (b i) d)-M (min (a i) d))+(A (min (b i) d)-A (min (a i) d))) :
    (∑ i∈s,G i*(N (min (b i) d)-N (min (a i) d)))=
      (∑ i∈s,G i*(M (min (b i) d)-M (min (a i) d)))+
        signedCumulative ξ (fun r => ∑ i∈s,(Ioc (a i) (b i)).indicator (fun _ => G i) r) d := by
  rw [signed_step_cumulative_Ioc ξ s a b G hab d,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hξ i hi,he i hi,mul_add]

end Asakura.Chapter11
