import Chapter12ScalarStockGains
import Chapter11ReplicationIntegrability
import Chapter2ProgressiveEnergySpace
import Chapter2ItoIntegrandEncoding

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter11
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem geometric_discount_identity (x σ r t w : ℝ) :
    Real.exp (-r*t)*geometricFlow x r σ ![t,w]=geometricFlow x 0 σ ![t,w] := by
  simp only [geometricFlow,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [← mul_assoc,mul_comm (Real.exp (-r*t)) x,mul_assoc,← Real.exp_add]
  congr 2
  ring

/-- The constructed Brownian hedge has the actual stock-integral identity,
portfolio balance, and all finite-horizon stock/bank integrability conditions. -/
theorem scalar_replication_domains {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (i : Fin d) (x σ r c : ℝ) (hx : 0<x) (hσ : σ≠0)
    (φ : progressiveEnergyIntegrands B.F canonicalClock (P.prod (volume.restrict (Ioi (0:ℝ)))))
    (N : HalfClosedTime → Ω → ℝ) (hN : ContinuousM2Witness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W i) φ.val N) :
    let S := fun z : Ω × ℝ => geometricFlow x r σ ![z.2,B.W i (realTimeClamp z.2) z.1]
    let H := fun z => φ.val z/(σ*(Real.exp (-r*z.2)*S z))
    let η := fun z : Ω × ℝ => c+N (realTimeClamp z.2) z.1-φ.val z/σ
    ∃ Y : HalfClosedTime → Ω → ℝ,LocalMProcessWitness P B.F Y ∧
      ItoCovarianceFormula P B.F Y H N ∧
      (∀ᵐ w ∂P,∀ t : ℝ,0≤t → Real.exp (-r*t)*S (w,t)=x+Y (realTimeClamp t) w) ∧
      (∀ w t,H (w,t)*S (w,t)+η (w,t)*Real.exp (r*t)=
        Real.exp (r*t)*(c+N (realTimeClamp t) w)) ∧
      (∀ᵐ w ∂P,∀ T : ℝ,0≤T →
        Integrable (fun t => H (w,t)*(r*S (w,t))) (volume.restrict (Ioc 0 T)) ∧
        Integrable (fun t => (H (w,t)*(σ*S (w,t)))^2) (volume.restrict (Ioc 0 T)) ∧
        Integrable (fun t => η (w,t)*(r*Real.exp (r*t))) (volume.restrict (Ioc 0 T))) := by
  intro S H η
  obtain ⟨Y,hY,hYI,hhold,hprice⟩ := scalar_stock_gains P B i x σ hx.ne' hσ φ.val φ.property.1 N hN hNI
  have hH : ItoCovarianceFormula P B.F Y H N := by
    apply hhold.congr_on_time_domain P B.F Y N _ H
    intro w t ht _
    dsimp only [H,S]
    rw [B.diagonal_clock i w t ht,geometric_discount_identity]
  have hS w t : 0<S (w,t) := by
    dsimp [S,geometricFlow]
    positivity
  have hφ w : Measurable (fun t => φ.val (w,t)) := φ.property.1.comp measurable_prodMk_left
  have hMc w : Continuous (fun t : ℝ => c+N (realTimeClamp t) w) :=
    continuous_const.add ((hN.path w).comp real_time_clamp_continuous)
  have hpath : ∀ᵐ w ∂P,Integrable (fun t => φ.val (w,t)^2) (volume.restrict (Ioi (0:ℝ))) :=
    φ.property.2.2.integrable_sq.prod_right_ae
  have hdomains w T (hT : 0≤T)
      (hi : Integrable (fun t => φ.val (w,t)^2) (volume.restrict (Ioc 0 T))) :=
    replication_strategy_path_integrability (fun t => φ.val (w,t))
      (fun t => c+N (realTimeClamp t) w) (fun t => S (w,t)) (hφ w) (hS w)
      T r r σ hT hσ hi (hMc w).continuousOn
  refine ⟨Y,hY,hH,?_,?_,?_⟩
  · filter_upwards [hprice] with w hw
    intro t ht
    dsimp only [S]
    rw [geometric_discount_identity]
    exact hw t ht
  · intro w t
    have hi : Integrable (fun t => φ.val (w,t)^2) (volume.restrict (Ioc 0 0)) := by simp
    exact (hdomains w 0 le_rfl hi).1 t
  · filter_upwards [hpath] with w hw
    intro T hT
    have hi := hw.mono_measure (Measure.restrict_mono (show Ioc (0:ℝ) T ⊆ Ioi 0 from fun _ h => h.1) le_rfl)
    exact ⟨(hdomains w T hT hi).2.1,(hdomains w T hT hi).2.2.1,(hdomains w T hT hi).2.2.2.1⟩

end Asakura.Chapter12
#print axioms Asakura.Chapter12.scalar_replication_domains
