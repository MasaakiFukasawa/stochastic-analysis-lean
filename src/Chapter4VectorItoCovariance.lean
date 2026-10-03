import Chapter4ItoPairDensity
import Chapter4CovarianceSumsDensity

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

/-- The covariance matrix of vector Ito integrals against independent
Brownian components is the time integral of H times its transpose. -/
theorem vector_ito_covariance_density
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W : Fin noise → ClosedTime T → Ω → ℝ)
    (B : Fin noise → Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hB : ∀ j k,LocalCovarianceWitness P F (W j) (W k) (B j k))
    (hclock : ∀ j k w (r : ℝ),0≤r → (r:EReal)<T → B j k (realTimeClamp r) w=if j=k then r else 0)
    (H N : Fin dim → Fin noise → ClosedTime T → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P F (N i j))
    (hHa : ∀ i j t,t<⊤ → Measurable[F t] (H i j t))
    (hHc : ∀ i j w t,t<⊤ → ContinuousAt (fun s => H i j s w) t)
    (hNI : ∀ i j,ItoCovarianceFormula P F (W j) (fun z => H i j (realTimeClamp z.2) z.1) (N i j))
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := T) (c n)) :
    ∃ C : Fin dim → Fin dim → ClosedTime T → Ω → ℝ,
      (∀ i l,LocalCovarianceWitness P F (fun t w => ∑ j,N i j t w) (fun t w => ∑ j,N l j t w) (C i l)) ∧
      (∀ i l n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),C i l (realTimeClamp r) w=
        ∫ s in 0..r,∑ j,H i j (realTimeClamp s) w*H l j (realTimeClamp s) w) := by
  classical
  have hpair i l j k : ∃ D : ClosedTime T → Ω → ℝ,LocalCovarianceWitness P F (N i j) (N l k) D ∧
      ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),D (realTimeClamp r) w=
        ∫ s in 0..r,H i j (realTimeClamp s) w*H l k (realTimeClamp s) w*(if j=k then 1 else 0) := by
    apply continuous_ito_pair_density P hT F hF hle hnull (W j) (W k) (N i j) (N l k) (B j k)
      (hW j) (hW k) (hN i j) (hN l k) (hB j k) (H i j) (H l k)
      (hHa i j) (hHc i j) (hHa l k) (hHc l k) (hNI i j) (hNI l k)
      (fun _ => if j=k then 1 else 0) (fun _ => measurable_const) c hc hcm hcT hcc
      (fun _ => ae_of_all _ fun _ => intervalIntegrable_const)
    intro n
    apply ae_of_all
    intro w r hr
    rw [hclock j k w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))]
    by_cases hjk : j=k <;> simp [hjk]
  choose D hD hDE using hpair
  let C := fun i l t w => ∑ k,∑ j,D i l j k t w
  refine ⟨C,fun i l => covariance_two_finite_sums P hT F hF hle (N i) (N l) (D i l) (hD i l),?_⟩
  intro i l n
  have hreal i j w : ContinuousOn (fun r => H i j (realTimeClamp r) w) (Icc 0 (c n)) := by
    intro r hr
    exact ((hHc i j w _ (real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n)))).comp
      real_time_clamp_continuous.continuousAt).continuousWithinAt
  have hi j k : ∀ᵐ w ∂P,IntervalIntegrable
      (fun r => H i j (realTimeClamp r) w*H l k (realTimeClamp r) w*(if j=k then 1 else 0)) volume 0 (c n) :=
    ae_of_all _ fun w => (((hreal i j w).mul (hreal l k w)).mul continuousOn_const).intervalIntegrable_of_Icc (hc n)
  have hh := finite_sum_density_identity P (D i l)
    (fun j k z => H i j (realTimeClamp z.2) z.1*H l k (realTimeClamp z.2) z.1*(if j=k then 1 else 0))
    (c n) (hc n) hi (fun j k => hDE i l j k n)
  filter_upwards [hh] with w hw
  intro r hr
  rw [show C i l (realTimeClamp r) w=∑ k,∑ j,D i l j k (realTimeClamp r) w from rfl,hw r hr]
  apply intervalIntegral.integral_congr
  intro s _
  simp

end Asakura.Chapter4
