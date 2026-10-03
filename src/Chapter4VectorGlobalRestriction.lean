import Chapter4VectorRealPath
import Chapter4ItoPrefixCongruence

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Restrict an arbitrary continuous solution to a finite interval and
construct the clipped coefficient integrals used by finite-path estimates. -/
theorem global_sde_finite_restriction
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hC : ∀ j,LocalCovarianceWitness P F (W j) (W j) (C j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → C j (realTimeClamp r) w=r)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hσ : ∀ i j,Continuous (σ i j))
    (ξ : Ω → Fin dim → ℝ) (X : ClosedTime T → Ω → Fin dim → ℝ)
    (ha : ∀ t,t<⊤ → Measurable[F t] (X t))
    (hc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (N : Fin dim → Fin noise → ClosedTime T → Ω → ℝ)
    (hn : ∀ i j,LocalMProcessWitness P F (N i j))
    (hI : ∀ i j,ItoCovarianceFormula P F (W j) (fun z => σ i j (X (realTimeClamp z.2) z.1)) (N i j))
    (he : ∀ᵐ w ∂P,∀ r : ℝ,0≤r → (r:EReal)<T → ∀ i,
      X (realTimeClamp r) w i=ξ w i+(∫ s in 0..r,μ i (X (realTimeClamp s) w))+∑ j,N i j (realTimeClamp r) w)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) :
    let Y := realVectorPath X hc R hRT
    ∃ J : Fin dim → Fin noise → ClosedTime T → Ω → ℝ,
      (∀ i j,LocalMProcessWitness P F (J i j)) ∧
      (∀ i j,ItoCovarianceFormula P F (W j)
        (fun z => σ i j (Y z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))) (J i j)) ∧
      ∀ᵐ w ∂P,∀ r i,Y w r i=ξ w i+
        (∫ s in 0..r.val,μ i (Y w (projIcc 0 R hR s)))+∑ j,J i j (realTimeClamp r.val) w := by
  classical
  let Y := realVectorPath X hc R hRT
  have hYa r : Measurable[F (realTimeClamp r.val)] (fun w => Y w r) :=
    ha _ (real_time_below r.val r.property.1 ((EReal.coe_le_coe r.property.2).trans_lt hRT))
  have hY := finite_path_lift_regular F hF R hR hRT.le Y hYa
  let H := fun i j t w => σ i j (Y w (finitePrefixTime (T := T) R hR t))
  have hHa i j t (_ht : t<⊤) := (hσ i j).measurable.comp (hY.1 t)
  have hHc i j w t (_ht : t<⊤) := ((hσ i j).comp (hY.2 w)).continuousAt (x := t)
  have hex i j := continuous_adapted_ito_exists P hT F hF hle hnull (W j) (hW j)
    (fun z => H i j (realTimeClamp z.2) z.1)
    (open_process_real_regularity F (H i j) (hHa i j) (hHc i j)).1
    (open_process_real_regularity F (H i j) (hHa i j) (hHc i j)).2
  let J := fun i j => (hex i j).choose
  have hsame i j := brownian_ito_prefix_congr P hT F hF hle hnull (W j) (C j) (hW j) (hC j) (hclock j)
    (fun t w => σ i j (X t w)) (H i j) (N i j) (J i j)
    (fun t ht => (hσ i j).measurable.comp (ha t ht)) (hHa i j)
    (fun w t ht => (hσ i j).continuousAt.comp (hc w t ht)) (hHc i j)
    (hn i j) (hex i j).choose_spec.1 (hI i j) (hex i j).choose_spec.2 R hR hRT
    (.of_forall (fun w r hr => by
      dsimp only [H]
      rw [finite_path_lift_real R hR hRT.le Y w r hr,projIcc_of_mem hR hr]
      rfl))
  refine ⟨J,fun i j => (hex i j).choose_spec.1,fun i j => (hex i j).choose_spec.2,?_⟩
  filter_upwards [he,ae_all_iff.mpr (fun i => ae_all_iff.mpr (hsame i))] with w hw hsw
  intro r i
  change X (realTimeClamp r.val) w i=_
  rw [hw r.val r.property.1 ((EReal.coe_le_coe r.property.2).trans_lt hRT) i]
  have hi : (∫ s in 0..r.val,μ i (X (realTimeClamp s) w))=
      ∫ s in 0..r.val,μ i (Y w (projIcc 0 R hR s)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s∈Icc 0 r.val := by simpa only [uIcc_of_le r.property.1] using hs
    dsimp only
    rw [projIcc_of_mem hR ⟨hs'.1,hs'.2.trans r.property.2⟩]
    rfl
  rw [hi]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => hsw i j r.val r.property)

end Asakura.Chapter4.Vector
