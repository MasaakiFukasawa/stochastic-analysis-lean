import Chapter5ObservationIntegrandRegularity
import Chapter5PastObservationIntegral
import Chapter5ZeroIto

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Only current observation coordinates remain in the stochastic part
of the interval formula; the time coordinate and all past coordinates vanish. -/
theorem observation_integrals_remove_past
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    {d k : ℕ} (W : Fin d → ClosedTime T → Ω → ℝ)
    (hW : ∀ i,LocalMProcessWitness P F (W i))
    (index : Fin k → Fin d) (active : Fin k → Prop) [DecidablePred active]
    (τ : Fin k → ℝ) (hτ : ∀ i,0≤τ i)
    (a b : ℝ) (ha : 0≤a) (hab : a≤b) (hbT : (b:EReal)<T)
    (hpast : ∀ i,¬active i → τ i≤a)
    (f : (Fin (k+1) → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (N : Fin (k+1) → ClosedTime T → Ω → ℝ)
    (hN : ∀ i,LocalMProcessWitness P F (N i))
    (hI : let X := fun j t w => W (index j) (min (realTimeClamp (τ j)) t) w
      let K := fun t (_ : Ω) => (finitePrefixTime (T := T) b (ha.trans hab) t).val
      let XX : Fin (k+1) → ClosedTime T → Ω → ℝ := Fin.cons K X
      let M : Fin (k+1) → ClosedTime T → Ω → ℝ := Fin.cons (fun _ _ => (0:ℝ)) X
      ∀ i,ItoCovarianceFormula P F (M i)
        (fun z => fderiv ℝ f (fun j => XX j (realTimeClamp z.2) z.1) (Pi.single i 1)) (N i)) :
    (fun w => ∑ i : Fin (k+1),(N i (realTimeClamp b) w-N i (realTimeClamp a) w)) =ᵐ[P]
      fun w => ∑ j ∈ Finset.univ.filter active,(N j.succ (realTimeClamp b) w-N j.succ (realTimeClamp a) w) := by
  classical
  let X := fun j t w => W (index j) (min (realTimeClamp (τ j)) t) w
  let K := fun t (_ : Ω) => (finitePrefixTime (T := T) b (ha.trans hab) t).val
  let XX : Fin (k+1) → ClosedTime T → Ω → ℝ := Fin.cons K X
  let H := fun i (z : Ω × ℝ) => fderiv ℝ f (fun j => XX j (realTimeClamp z.2) z.1) (Pi.single i 1)
  have hr i := observation_integrand_regularity P hT F hF hle W hW index τ b (ha.trans hab) f hf i
  have hta : realTimeClamp (T := T) a<⊤ := by
    change (realTimeClamp a:EReal)<T
    rw [real_time_clamp_eq a ha ((EReal.coe_le_coe hab).trans hbT.le)]
    exact (EReal.coe_le_coe hab).trans_lt hbT
  have htb : realTimeClamp (T := T) b<⊤ := by
    change (realTimeClamp b:EReal)<T
    rw [real_time_clamp_eq b (ha.trans hab) hbT.le]
    exact hbT
  have h0 := integral_against_zero_martingale P hT F hF hle hnull (N 0) (H 0) (hN 0) (hI 0)
  have hp : ∀ᵐ w ∂P,∀ j,¬active j → N j.succ (realTimeClamp b) w=N j.succ (realTimeClamp a) w := by
    apply ae_all_iff.mpr
    intro j
    by_cases hj : active j
    · exact ae_of_all _ fun _ h => False.elim (h hj)
    · have hc := past_observation_integral_constant P hT F hF hle hnull (W (index j)) (N j.succ)
        (hW (index j)) (hN j.succ) (H j.succ) (hr j.succ).1 (hr j.succ).2.1 (hr j.succ).2.2
        (τ j) (hτ j) (hI j.succ)
      filter_upwards [hc] with w hw
      intro _
      exact hw _ _ htb hta (real_time_clamp_mono ((hpast j hj).trans hab)) (real_time_clamp_mono (hpast j hj))
  filter_upwards [h0,hp] with w hw hpw
  rw [Fin.sum_univ_succ,hw _ htb,hw _ hta,sub_self,zero_add,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : active j
  · simp [hj]
  · simp [hj,hpw j hj]

end Asakura.Chapter5
