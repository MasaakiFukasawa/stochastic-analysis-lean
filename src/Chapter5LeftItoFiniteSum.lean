import Chapter5FiniteGridLeft
import Chapter3IdentityItoIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Finite addition retains the actual Ito characterization and M²,
including an empty family. -/
theorem finite_M2_ito_sum
    {Ω ι : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (W : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (H : ι → Ω × ℝ → ℝ) (Z : ι → ClosedTime T → Ω → ℝ) (s : Finset ι)
    (hZ : ∀ i∈s,ContinuousM2Witness P F (Z i))
    (hI : ∀ i∈s,ItoCovarianceFormula P F W (H i) (Z i)) :
    ContinuousM2Witness P F (fun t w => ∑ i∈s,Z i t w) ∧
      ItoCovarianceFormula P F W (fun z => ∑ i∈s,H i z) (fun t w => ∑ i∈s,Z i t w) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := Asakura.Chapter3Complete.identity_ito_integral P hT F hF hle hnull W hW
    have hz := h.add_smul P F hF hle W W W (fun _ => 1) (fun _ => 1) h (-1)
    constructor
    · simp only [Finset.sum_empty]
      exact ContinuousM2Witness.zero P F
    · simpa using hz
  | @insert i s hi ih =>
    have hs := ih (fun j hj => hZ j (Finset.mem_insert_of_mem hj))
      (fun j hj => hI j (Finset.mem_insert_of_mem hj))
    constructor
    · simp only [Finset.sum_insert hi]
      exact (hZ i (Finset.mem_insert_self ..)).add P F hs.1
    · simpa only [Finset.sum_insert hi,one_mul] using
        (hI i (Finset.mem_insert_self ..)).add_smul P F hF hle W _ _ _ _ hs.2 1

end Asakura.Chapter5
