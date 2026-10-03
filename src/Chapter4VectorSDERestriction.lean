import Chapter4ItoPrefixCongruence
import Chapter4VectorFiniteExistence
import Chapter4VectorFiniteUniqueness

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- Restriction of an actual finite-horizon solution. The shorter-horizon
noise integral is constructed and identified up to the shorter endpoint. -/
theorem finite_sde_restriction
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hC : ∀ j,LocalCovarianceWitness P F (W j) (W j) (C j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → C j (realTimeClamp r) w=r)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hσ : ∀ i j,Continuous (σ i j)) (ξ : Ω → Fin dim → ℝ)
    (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ))
    (ha : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y w r))
    (N : Fin dim → Fin noise → ClosedTime T → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P F (W j)
      (fun z => σ i j (Y z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))) (N i j))
    (hrep : ∀ᵐ w ∂P,∀ r i,Y w r i=ξ w i+(∫ s in 0..r.val,μ i (Y w (projIcc 0 R hR s)))+∑ j,N i j (realTimeClamp r.val) w)
    (d : ℝ) (hd : 0≤d) (hdR : d≤R) :
    ∃ Z : Fin dim → Fin noise → ClosedTime T → Ω → ℝ,
      (∀ i j,LocalMProcessWitness P F (Z i j)) ∧
      (∀ i j,ItoCovarianceFormula P F (W j)
        (fun z => σ i j (restrictRealPath hdR (Y z.1) (finitePrefixTime (T := T) d hd (realTimeClamp z.2)))) (Z i j)) ∧
      ∀ᵐ w ∂P,∀ r i,restrictRealPath hdR (Y w) r i=ξ w i+
        (∫ s in 0..r.val,μ i (restrictRealPath hdR (Y w) (projIcc 0 d hd s)))+∑ j,Z i j (realTimeClamp r.val) w := by
  let U := fun i j t w => σ i j (Y w (finitePrefixTime (T := T) R hR t))
  let V := fun i j t w => σ i j (restrictRealPath hdR (Y w) (finitePrefixTime (T := T) d hd t))
  have hY := finite_path_lift_regular F hF R hR hRT.le Y ha
  have hdT : (d:EReal)<T := (EReal.coe_le_coe hdR).trans_lt hRT
  have hYa : ∀ r,Measurable[F (realTimeClamp (T := T) r.val)] (fun w => restrictRealPath hdR (Y w) r) :=
    fun r => ha ⟨r.val,r.property.1,r.property.2.trans hdR⟩
  have hZ := finite_path_lift_regular F hF d hd hdT.le (fun w => restrictRealPath hdR (Y w)) hYa
  have hVa i j t (_ht : t<⊤) := (hσ i j).measurable.comp (hZ.1 t)
  have hVc i j w t (_ht : t<⊤) := ((hσ i j).comp (hZ.2 w)).continuousAt (x := t)
  have hreg i j := open_process_real_regularity F (V i j) (hVa i j) (hVc i j)
  have hex i j := continuous_adapted_ito_exists P hT F hF hle hnull (W j) (hW j)
    (fun z => V i j (realTimeClamp z.2) z.1) (hreg i j).1 (hreg i j).2
  choose Z hZlocal hZI using hex
  have hUV i j : ∀ᵐ w ∂P,∀ r,r∈Icc 0 d → U i j (realTimeClamp r) w=V i j (realTimeClamp r) w := by
    apply Filter.Eventually.of_forall
    intro w r hr
    dsimp only [U,V,restrictRealPath,ContinuousMap.coe_mk]
    congr 2
    apply Subtype.ext
    rw [finite_prefix_time_of_real R r hR ⟨hr.1,hr.2.trans hdR⟩ hRT.le,
      finite_prefix_time_of_real d r hd hr hdT.le]
  have he i j := brownian_ito_prefix_congr P hT F hF hle hnull (W j) (C j) (hW j) (hC j) (hclock j)
    (U i j) (V i j) (N i j) (Z i j)
    (fun t _ => (hσ i j).measurable.comp (hY.1 t)) (hVa i j)
    (fun w t _ => ((hσ i j).comp (hY.2 w)).continuousAt) (hVc i j)
    (hN i j) (hZlocal i j) (hNI i j) (hZI i j) d hd hdT (hUV i j)
  refine ⟨Z,hZlocal,hZI,?_⟩
  filter_upwards [hrep,ae_all_iff.mpr (fun i => ae_all_iff.mpr (he i))] with w hw hew
  intro r i
  have hi : (∫ s in 0..r.val,μ i (Y w (projIcc 0 R hR s)))=
      ∫ s in 0..r.val,μ i (restrictRealPath hdR (Y w) (projIcc 0 d hd s)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s∈Icc 0 d := Icc_subset_Icc_right r.property.2 (by simpa [uIcc_of_le r.property.1] using hs)
    dsimp only
    rw [projIcc_of_mem hR ⟨hs'.1,hs'.2.trans hdR⟩,projIcc_of_mem hd hs']
    rfl
  have h := hw ⟨r.val,r.property.1,r.property.2.trans hdR⟩ i
  rw [hi] at h
  simp_rw [fun j => hew i j r.val r.property] at h
  exact h

end Asakura.Chapter4.Vector
