import Chapter5FiniteItoSum
import Chapter5CeilPrefix

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- The integral of the ceiling-pasted integrand agrees, on each finite
prefix, with the actual finite sum of interval integrals. -/
theorem pasted_integral_prefix_identification
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (X J : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hJ : LocalMProcessWitness P F J)
    (H : ℕ → Ω × ℝ → ℝ) (M : ℕ → ClosedTime T → Ω → ℝ)
    (hM : ∀ j,LocalMProcessWitness P F (M j))
    (hI : ∀ (j : ℕ),ItoCovarianceFormula P F X
      (fun z => (Ioc (j:ℝ) (j+1)).indicator (fun r => H j (z.1,r)) z.2) (M j))
    (hGm : ∀ w,Measurable (fun r => H (Nat.ceil r-1) (w,r)))
    (hJI : ItoCovarianceFormula P F X (fun z => H (Nat.ceil z.2-1) z) J) (N : ℕ) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → J (min (realTimeClamp (N:ℝ)) t) w=∑ j∈Finset.range N,M j t w := by
  have hstop : ∀ t,MeasurableSet[F t] {w : Ω | realTimeClamp (T := T) (N:ℝ)≤t} := by
    intro t
    by_cases hh : realTimeClamp (T := T) (N:ℝ)≤t <;> simp [hh]
  have hJs := hJ.stopped P F hF hle (fun _ => realTimeClamp (N:ℝ)) hstop
  have hst := stopped_ito_covariance_formula P hT F hF hle hnull X J
    (fun z => H (Nat.ceil z.2-1) z) hX hJ hGm hJI (N:ℝ) (Nat.cast_nonneg N)
  have hsum := ito_covariance_range_sum P F hF hle X hX
    (fun j z => (Ioc (j:ℝ) (j+1)).indicator (fun r => H j (z.1,r)) z.2) M hM hI N
  have he : (fun z : Ω × ℝ => (Ioc (0:ℝ) N).indicator (fun r => H (Nat.ceil r-1) (z.1,r)) z.2)=
      (fun z => ∑ j∈Finset.range N,(Ioc (j:ℝ) (j+1)).indicator (fun r => H j (z.1,r)) z.2) := by
    funext z
    exact ceil_integrand_prefix_sum H N z.1 z.2
  rw [he] at hst
  exact hst.unique P hT F hF hle hnull X _ _ _ hX hJs hsum.1 hsum.2

end Asakura.Chapter5
