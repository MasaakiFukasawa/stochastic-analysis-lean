import Chapter4FiniteCovarianceSum
import Chapter3IdentityItoIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem finite_ito_sum
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    {ι : Type*} (s : Finset ι) (H : ι → Ω × ℝ → ℝ) (N : ι → ClosedTime T → Ω → ℝ)
    (hI : ∀ i∈s,ItoCovarianceFormula P F W (H i) (N i)) :
    ItoCovarianceFormula P F W (fun z => ∑ i∈s,H i z) (fun t w => ∑ i∈s,N i t w) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hi := identity_ito_integral P hT F hF hle hnull W hW
    have hz := hi.add_smul P F hF hle W W W (fun _ => 1) (fun _ => 1) hi (-1)
    simpa only [neg_one_mul,neg_add_cancel,Finset.sum_empty] using hz
  | @insert i s hi ih =>
    have hh := (hI i (Finset.mem_insert_self _ _)).add_smul P F hF hle W (N i)
      (fun t w => ∑ j∈s,N j t w) (H i) (fun z => ∑ j∈s,H j z)
      (ih (fun j hj => hI j (Finset.mem_insert_of_mem hj))) 1
    simpa only [one_mul,Finset.sum_insert hi] using hh

theorem constant_ito_integral
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W) (a : ℝ) :
    ItoCovarianceFormula P F W (fun _ => a) (fun t w => a*W t w) := by
  have hi := identity_ito_integral P hT F hF hle hnull W hW
  convert hi.add_smul P F hF hle W W W (fun _ => 1) (fun _ => 1) hi (a-1) using 1 <;>
    ext z w <;> ring

end Asakura.Chapter4
