import Chapter4VectorPowerEstimate
import Chapter4VectorPathRestriction
import Chapter4PathRestrictionLp

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

theorem vector_integral_prefix_power_estimate
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    {d dim : ℕ} (W A : Fin d → ClosedTime T → Ω → ℝ) (N : Fin dim → Fin d → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hA : ∀ j,LocalCovarianceWitness P F (W j) (W j) (A j))
    (hN : ∀ i j,LocalMProcessWitness P F (N i j))
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ j n w r, r ∈ Icc 0 (c n) → A j (realTimeClamp r) w = r)
    (G : Fin dim → Fin d → Ω × ℝ → ℝ)
    (hG : ∀ i j n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => G i j (z.1,z.2.val)))
    (hi : ∀ i j n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G i j (w,r)^2) volume 0 (c n))
    (hNI : ∀ i j,ItoCovarianceFormula P F (W j) (G i j) (N i j))
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) (p : ℝ) (hp : 2≤p)
    (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ)) (hYm : Measurable[m] Y) 
    (hYi : MemLp Y (ENNReal.ofReal p) P)
    (ξ : Fin dim → Ω → ℝ) (hξm : ∀ i,Measurable[m] (ξ i)) (hξi : ∀ i,MemLp (ξ i) (ENNReal.ofReal p) P)
    (U : Fin dim → Ω × ℝ → ℝ) (hUm : ∀ i,Measurable[m.prod inferInstance] (U i)) (hGm : ∀ i j,Measurable[m.prod inferInstance] (G i j))
    (K : ℝ) (hK : 0≤K)
    (hUg : ∀ i w r,r∈Icc 0 R → |U i (w,r)|^p≤K*(1+‖Y w (projIcc 0 R hR r)‖^p))
    (hGg : ∀ i j w r,r∈Icc 0 R → |G i j (w,r)|^p≤K*(1+‖Y w (projIcc 0 R hR r)‖^p))
    (hrep : ∀ᵐ w ∂P,∀ r i,Y w r i=ξ i w+(∫ s in 0..r.val,U i (w,s))+∑ j,N i j (realTimeClamp r.val) w)
    (t : ℝ) (ht : t∈Icc 0 R) :
    (∫ w,‖prefixPath hR (normEnvelope (Y w)) t‖^p ∂P)≤(dim:ℝ)^(p-1)*(3:ℝ)^(p-1)*
      ((∑ i,∫ w,|ξ i w|^p ∂P)+(dim:ℝ)*
      (t^(p-1)+((d:ℝ)^(p-1)*d)*bdgUpperMomentConstant p*t^(p/2-1))*K*
        (t+∫ r in 0..t,(∫ w,‖prefixPath hR (normEnvelope (Y w)) r‖^p ∂P))) := by
  letI : MeasurableSpace Ω := m
  have hm := Vector.restrict_real_path_measurable ht.2 Y hYm
  have hiY : MemLp (fun w => Vector.restrictRealPath ht.2 (Y w)) (ENNReal.ofReal p) P := by
    apply hYi.of_le_mul (c := 1) hm.aestronglyMeasurable
    exact .of_forall (fun w => by simpa only [one_mul] using Vector.restrict_real_path_norm_le ht.2 (Y w))
  have hpoint w r (hr : r∈Icc 0 t) : Vector.restrictRealPath ht.2 (Y w) (projIcc 0 t ht.1 r)=Y w (projIcc 0 R hR r) := by
    rw [projIcc_of_mem ht.1 hr,projIcc_of_mem hR ⟨hr.1,hr.2.trans ht.2⟩]
    rfl
  have hUg' i w r (hr : r∈Icc 0 t) : |U i (w,r)|^p≤K*(1+‖Vector.restrictRealPath ht.2 (Y w) (projIcc 0 t ht.1 r)‖^p) := by
    rw [hpoint w r hr]
    exact hUg i w r ⟨hr.1,hr.2.trans ht.2⟩
  have hGg' i j w r (hr : r∈Icc 0 t) : |G i j (w,r)|^p≤K*(1+‖Vector.restrictRealPath ht.2 (Y w) (projIcc 0 t ht.1 r)‖^p) := by
    rw [hpoint w r hr]
    exact hGg i j w r ⟨hr.1,hr.2.trans ht.2⟩
  have hrep' : ∀ᵐ w ∂P,∀ r i,Vector.restrictRealPath ht.2 (Y w) r i=ξ i w+
      (∫ s in 0..r.val,U i (w,s))+∑ j,N i j (realTimeClamp r.val) w := by
    filter_upwards [hrep] with w hw
    intro r i
    exact hw ⟨r.val,r.property.1,r.property.2.trans ht.2⟩ i
  have hb := vector_integral_power_estimate P hT F hF hle hnull W A N hW hA hN
    c hc hcm hcT hct hcut hcc hclock G hG hi hNI t ht.1 ((EReal.coe_le_coe ht.2).trans_lt hRT) p hp
    (fun w => Vector.restrictRealPath ht.2 (Y w)) hm hiY ξ hξm hξi U hUm hGm K hK hUg' hGg' hrep'
  have hnorm w : ‖Vector.restrictRealPath ht.2 (Y w)‖=‖prefixPath hR (normEnvelope (Y w)) t‖ := by
    rw [← norm_envelope_norm]
    exact restriction_eq_prefix_norm ht.1 ht.2 (normEnvelope (Y w))
  simp_rw [hnorm] at hb
  have he : (∫ r in 0..t,(∫ w,‖prefixPath ht.1 (normEnvelope (Vector.restrictRealPath ht.2 (Y w))) r‖^p ∂P))=
      ∫ r in 0..t,(∫ w,‖prefixPath hR (normEnvelope (Y w)) r‖^p ∂P) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r∈Icc 0 t := by simpa only [uIcc_of_le ht.1] using hr
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro w
    change ‖prefixPath ht.1 (restrictRealPath ht.2 (normEnvelope (Y w))) r‖^p=_
    rw [restricted_prefix_norm ht.1 ht.2 _ r hr']
  simpa only [he] using hb

end Asakura.Chapter4
