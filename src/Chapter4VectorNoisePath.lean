import Chapter4VectorFiniteLift
import Chapter4VectorCoefficientEnergy
import Chapter4ClockRegularity
import Chapter4BrownianFiniteMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- Construct one matrix coefficient's Ito integral against one Brownian
coordinate, retaining both the local process and its finite L² path. -/
theorem noise_path_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hC : LocalCovarianceWitness P F W W C)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → C (realTimeClamp r) w=r)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ))
    (ha : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y w r))
    (b : (Fin dim → ℝ) → ℝ) (hb : Continuous b)
    (hi : MemLp (fun z : Ω × ℝ => b (Y z.1 (projIcc 0 R hR z.2))) 2
      (P.prod (volume.restrict (Ioc (0:ℝ) R)))) :
    ∃ (N : ClosedTime T → Ω → ℝ) (Z : Ω → C(Icc (0:ℝ) R,ℝ)),
      LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F W
        (fun z => b (Y z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))) N ∧
      Measurable[m] Z ∧ MemLp Z 2 P ∧
      (∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Z w r)) ∧
      (∀ w r,Z w r=N (realTimeClamp r.val) w) ∧
      (∫ w,‖Z w‖^2 ∂P)≤4*(∫ w,(∫ s in 0..R,b (Y w (projIcc 0 R hR s))^2) ∂P) := by
  letI : MeasurableSpace Ω := m
  let H := fun t w => b (Y w (finitePrefixTime (T := T) R hR t))
  have hY := finite_path_lift_regular F hF R hR hRT.le Y ha
  have hHa t (_ht : t<⊤) := hb.measurable.comp (hY.1 t)
  have hHc w t (_ht : t<⊤) := (hb.comp (hY.2 w)).continuousAt (x := t)
  have hreg := open_process_real_regularity F H hHa hHc
  obtain ⟨N,hN,hNI⟩ := continuous_adapted_ito_exists P hT F hF hle hnull W hW
    (fun z => H (realTimeClamp z.2) z.1) hreg.1 hreg.2
  have henergy w : (∫ s in 0..R,H (realTimeClamp s) w^2)=
      ∫ s in 0..R,b (Y w (projIcc 0 R hR s))^2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s∈Icc 0 R := by simpa [uIcc_of_le hR] using hs
    dsimp only [H]
    rw [finite_path_lift_real R hR hRT.le Y w s hs']
  have hsquare := (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).1 hi
  have hEi : Integrable (fun w => ∫ s in 0..R,H (realTimeClamp s) w^2) P := by
    simp_rw [henergy,intervalIntegral.integral_of_le hR]
    exact hsquare.integral_prod_left
  obtain ⟨hCm,hCc⟩ := clock_regular_from_identity C hclock
  obtain ⟨hNc,hNi,hNb⟩ := brownian_ito_finite_path_moment P hT F hF hle hnull W C H N hW hC hCm hCc hclock
    hHa hHc hN hNI R hR hRT hEi
  refine ⟨N,finiteRealPath N R hNc,hN,hNI,
    finite_real_path_measurable F hle N R hRT hNc (hN.adapted P F),hNi,?_,fun _ _ => rfl,?_⟩
  · intro r
    exact hN.adapted P F _ (real_time_below r.val r.property.1 ((EReal.coe_le_coe r.property.2).trans_lt hRT))
  · simpa only [henergy] using hNb

end Asakura.Chapter4.Vector
