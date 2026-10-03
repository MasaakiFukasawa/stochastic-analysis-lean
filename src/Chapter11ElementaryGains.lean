import Chapter4UnboundedElementaryIto
import Chapter4FiniteItoSum
import Chapter3SemimartingaleFiniteSums

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- An actual finite elementary gains process and its covariance
 characterization, for a general continuous local martingale. -/
theorem finite_elementary_gains {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (G : ι → Ω → ℝ)
    (ha : ∀ i∈s,0≤a i) (hab : ∀ i∈s,a i≤b i)
    (hGm : ∀ i∈s,Measurable[F (realTimeClamp (a i))] (G i))
    (hG : ∀ i∈s,MemLp (G i) ∞ P) :
    let Y := fun t w => ∑ i∈s,G i w*(X (min (realTimeClamp (b i)) t) w-X (min (realTimeClamp (a i)) t) w)
    LocalMProcessWitness P F Y ∧ ItoCovarianceFormula P F X
      (fun z => ∑ i∈s,(Ioc (a i) (b i)).indicator (fun _ => G i z.1) z.2) Y := by
  classical
  let Y := fun i t w => G i w*(X (min (realTimeClamp (b i)) t) w-X (min (realTimeClamp (a i)) t) w)
  have hy i (hi : i∈s) : LocalMProcessWitness P F (Y i) :=
    elementary_integral_local_martingale P F hF hle X hX _ _ (real_time_clamp_mono (hab i hi)) (G i) (hGm i hi) (hG i hi)
  refine ⟨local_process_finset_sum P F hF hle s Y hy (by simpa only [zero_mul] using hX.smul P F 0),?_⟩
  exact finite_ito_sum P hT F hF hle hnull X hX s
    (fun i z => (Ioc (a i) (b i)).indicator (fun _ => G i z.1) z.2) Y
    (fun i hi => unbounded_elementary_ito_formula P hT F hF hle hnull X hX (a i) (b i) (ha i hi) (hab i hi) (G i) (hGm i hi) (hy i hi))

end Asakura.Chapter11
