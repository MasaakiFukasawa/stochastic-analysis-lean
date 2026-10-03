import Chapter4RealBorelCoefficientDomain
import Chapter4VectorSolutionPowerMoment
import Chapter4VectorRealPath
import Chapter4VectorSDEInitial

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem global_sde_power_moment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) (hTinf : T=⊤) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hC : ∀ j,LocalCovarianceWitness P F (W j) (W j) (C j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → C j (realTimeClamp r) w=r)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hμ : ∀ i,Measurable (μ i)) (hσ : ∀ i j,Measurable (σ i j))
    (L : ℝ) (hL : 0≤L)
    (hμg : ∀ i x,(μ i x)^2≤L*(1+‖x‖^2))
    (hσg : ∀ i j x,(σ i j x)^2≤L*(1+‖x‖^2))
    (p : ℝ) (hp : 2≤p)
    (ξ : Ω → Fin dim → ℝ) (hξm : Measurable[m] ξ) (hξi : MemLp ξ (ENNReal.ofReal p) P)
    (X : ClosedTime T → Ω → Fin dim → ℝ)
    (ha : ∀ t,t<⊤ → Measurable[F t] (X t))
    (hc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (N : Fin dim → Fin noise → ClosedTime T → Ω → ℝ)
    (hn : ∀ i j,LocalMProcessWitness P F (N i j))
    (hI : ∀ i j,ItoCovarianceFormula P F (W j) (fun z => σ i j (X (realTimeClamp z.2) z.1)) (N i j))
    (he : ∀ᵐ w ∂P,∀ r : ℝ,0≤r → (r:EReal)<T → ∀ i,
      X (realTimeClamp r) w i=ξ w i+(∫ s in 0..r,μ i (X (realTimeClamp s) w))+∑ j,N i j (realTimeClamp r) w)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) :
    MemLp (realVectorPath X hc R hRT) (ENNReal.ofReal p) P := by
  letI : MeasurableSpace Ω := m
  have hbelow r : realTimeClamp (T := T) r<⊤ := by
    apply (real_time_clamp_mono (le_max_left r 0)).trans_lt
    apply real_time_below (max r 0) (le_max_right r 0)
    simp [hTinf]
  have hXm r : Measurable[m] (X (realTimeClamp r)) := (ha _ (hbelow r)).mono (hle _) le_rfl
  have hXc w : Continuous (fun r => X (realTimeClamp r) w) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (hc w _ (hbelow r)).comp real_time_clamp_continuous.continuousAt
  let Y := realVectorPath X hc R hRT
  have hYa r : Measurable[F (realTimeClamp r.val)] (fun w => Y w r) := ha _ (hbelow r.val)
  have hYm : Measurable[m] Y := ContinuousMap.measurable_iff_eval.mpr (fun r => (hYa r).mono (hle _) le_rfl)
  let G := fun i j (z : Ω × ℝ) => σ i j (X (realTimeClamp z.2) z.1)
  let U := fun i (z : Ω × ℝ) => μ i (X (realTimeClamp z.2) z.1)
  have hdom i j := real_borel_coefficient_domain F hF (fun r => X (realTimeClamp r)) hXm hXc
    (fun r _ => ha _ (hbelow r)) (σ i j) (hσ i j) L hL (hσg i j)
  have hUm i := (real_borel_coefficient_domain F hF (fun r => X (realTimeClamp r)) hXm hXc
    (fun r _ => ha _ (hbelow r)) (μ i) (hμ i) L hL (hμg i)).1
  have hrep : ∀ᵐ w ∂P,∀ r i,Y w r i=ξ w i+(∫ s in 0..r.val,U i (w,s))+∑ j,N i j (realTimeClamp r.val) w :=
    he.mono (fun w hw r i => hw r.val r.property.1 ((EReal.coe_le_coe r.property.2).trans_lt hRT) i)
  have hinit := finite_sde_initial_value P F R hR hRT Y ξ U N hn hrep
  obtain ⟨c,hc0,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  have hξm' i : Measurable[m] (fun w => ξ w i) := (measurable_pi_apply i).comp hξm
  have hξi' i : MemLp (fun w => ξ w i) (ENNReal.ofReal p) P := by
    apply hξi.of_le_mul (c := 1) (hξm' i).aestronglyMeasurable
    exact .of_forall (fun w => by simpa only [one_mul] using norm_le_pi_norm (ξ w) i)
  let K := L^(p/2)*(2:ℝ)^(p/2)
  have hK : 0≤K := by dsimp [K]; positivity
  apply vector_solution_power_moment P hT F hF hle hnull W C N hW hC hn
    c hc0 hcm hcT hct hcut hcc
    (fun j n w r hr => hclock j w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n)))
    G (fun i j n => (hdom i j).2.1 (c n) (hc0 n).le)
    (fun i j n => .of_forall ((hdom i j).2.2 (c n) (hc0 n).le)) hI
    R hR hRT p hp Y hYm hYa ((memLp_congr_ae hinit).2 hξi)
    (fun i w => ξ w i) hξm' hξi' U hUm (fun i j => (hdom i j).1) K hK _ _ hrep
  · intro i w r hr
    rw [projIcc_of_mem hR hr]
    simpa only [U,Y,realVectorPath,ContinuousMap.coe_mk,abs_norm] using
      square_growth_power_bound (μ i (X (realTimeClamp r) w)) ‖X (realTimeClamp r) w‖ L p hL (by linarith only [hp]) (hμg i _)
  · intro i j w r hr
    rw [projIcc_of_mem hR hr]
    simpa only [G,Y,realVectorPath,ContinuousMap.coe_mk,abs_norm] using
      square_growth_power_bound (σ i j (X (realTimeClamp r) w)) ‖X (realTimeClamp r) w‖ L p hL (by linarith only [hp]) (hσg i j _)

end Asakura.Chapter4.Vector
