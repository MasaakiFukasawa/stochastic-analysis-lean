import Chapter4ItoPrefixCongruence
import Chapter4ScalarFiniteExistence
import Chapter4ScalarFiniteUniqueness

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- Restriction of an actual finite-horizon solution. The shorter-horizon
noise integral is constructed and identified up to the shorter endpoint. -/
theorem finite_sde_restriction
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hC : LocalCovarianceWitness P F W W C)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → C (realTimeClamp r) w=r)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (μ σ : ℝ → ℝ) (hσ : Continuous σ) (ξ : Ω → ℝ)
    (Y : Ω → C(Icc (0:ℝ) R,ℝ))
    (ha : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y w r))
    (N : ClosedTime T → Ω → ℝ) (hN : LocalMProcessWitness P F N)
    (hNI : ItoCovarianceFormula P F W
      (fun z => σ (Y z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))) N)
    (hrep : ∀ᵐ w ∂P,∀ r,Y w r=ξ w+(∫ s in 0..r.val,μ (Y w (projIcc 0 R hR s)))+N (realTimeClamp r.val) w)
    (d : ℝ) (hd : 0≤d) (hdR : d≤R) :
    ∃ Z : ClosedTime T → Ω → ℝ,LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F W
        (fun z => σ (restrictRealPath hdR (Y z.1) (finitePrefixTime (T := T) d hd (realTimeClamp z.2)))) Z ∧
      ∀ᵐ w ∂P,∀ r,restrictRealPath hdR (Y w) r=ξ w+
        (∫ s in 0..r.val,μ (restrictRealPath hdR (Y w) (projIcc 0 d hd s)))+Z (realTimeClamp r.val) w := by
  let U := fun t w => σ (Y w (finitePrefixTime (T := T) R hR t))
  let V := fun t w => σ (restrictRealPath hdR (Y w) (finitePrefixTime (T := T) d hd t))
  have hY := finite_path_lift_regular F hF R hR hRT.le Y ha
  have hdT : (d:EReal)<T := (EReal.coe_le_coe hdR).trans_lt hRT
  have hYa : ∀ r,Measurable[F (realTimeClamp (T := T) r.val)] (fun w => restrictRealPath hdR (Y w) r) :=
    fun r => ha ⟨r.val,r.property.1,r.property.2.trans hdR⟩
  have hZ := finite_path_lift_regular F hF d hd hdT.le (fun w => restrictRealPath hdR (Y w)) hYa
  have hVa t (_ht : t<⊤) := hσ.measurable.comp (hZ.1 t)
  have hVc w t (_ht : t<⊤) := (hσ.comp (hZ.2 w)).continuousAt (x := t)
  have hreg := open_process_real_regularity F V hVa hVc
  obtain ⟨Z,hZlocal,hZI⟩ := continuous_adapted_ito_exists P hT F hF hle hnull W hW
    (fun z => V (realTimeClamp z.2) z.1) hreg.1 hreg.2
  have hUV : ∀ᵐ w ∂P,∀ r,r∈Icc 0 d → U (realTimeClamp r) w=V (realTimeClamp r) w := by
    apply Filter.Eventually.of_forall
    intro w r hr
    dsimp only [U,V,restrictRealPath,ContinuousMap.coe_mk]
    congr 2
    apply Subtype.ext
    rw [finite_prefix_time_of_real R r hR ⟨hr.1,hr.2.trans hdR⟩ hRT.le,
      finite_prefix_time_of_real d r hd hr hdT.le]
  have he := brownian_ito_prefix_congr P hT F hF hle hnull W C hW hC hclock U V N Z
    (fun t _ => hσ.measurable.comp (hY.1 t)) hVa
    (fun w t _ => (hσ.comp (hY.2 w)).continuousAt) hVc hN hZlocal hNI hZI d hd hdT hUV
  refine ⟨Z,hZlocal,hZI,?_⟩
  filter_upwards [hrep,he] with w hw hew
  intro r
  have hi : (∫ s in 0..r.val,μ (Y w (projIcc 0 R hR s)))=
      ∫ s in 0..r.val,μ (restrictRealPath hdR (Y w) (projIcc 0 d hd s)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s∈Icc 0 d := Icc_subset_Icc_right r.property.2 (by simpa [uIcc_of_le r.property.1] using hs)
    dsimp only
    rw [projIcc_of_mem hR ⟨hs'.1,hs'.2.trans hdR⟩,projIcc_of_mem hd hs']
    rfl
  have h := hw ⟨r.val,r.property.1,r.property.2.trans hdR⟩
  rw [hi,hew r.val r.property] at h
  exact h

end Asakura.Chapter4
