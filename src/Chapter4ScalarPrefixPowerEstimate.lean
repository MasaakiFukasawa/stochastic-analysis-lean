import Chapter4ScalarPowerEstimate
import Chapter4PathRestrictionLp

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- The actual integral moment estimate at every prefix time. -/
theorem scalar_integral_prefix_power_estimate
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (W A N : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A) (hN : LocalMProcessWitness P F N)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (G : Ω × ℝ → ℝ)
    (hG : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => G (z.1,z.2.val)))
    (hi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G (w,r)^2) volume 0 (c n))
    (hNI : ItoCovarianceFormula P F W G N)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) (p : ℝ) (hp : 2≤p)
    (Y : Ω → C(Icc (0:ℝ) R,ℝ)) (hYm : Measurable[m] Y) (hYi : MemLp Y (ENNReal.ofReal p) P)
    (ξ : Ω → ℝ) (hξm : Measurable[m] ξ) (hξi : MemLp ξ (ENNReal.ofReal p) P)
    (U : Ω × ℝ → ℝ) (hUm : Measurable[m.prod inferInstance] U) (hGm : Measurable[m.prod inferInstance] G)
    (K : ℝ) (hK : 0≤K)
    (hUg : ∀ w r,r∈Icc 0 R → |U (w,r)|^p≤K*(1+|Y w (projIcc 0 R hR r)|^p))
    (hGg : ∀ w r,r∈Icc 0 R → |G (w,r)|^p≤K*(1+|Y w (projIcc 0 R hR r)|^p))
    (hrep : ∀ᵐ w ∂P,∀ r,Y w r=ξ w+(∫ s in 0..r.val,U (w,s))+N (realTimeClamp r.val) w)
    (d : ℝ) (hd : d∈Icc 0 R) :
    (∫ w,‖prefixPath hR (Y w) d‖^p ∂P)≤(3:ℝ)^(p-1)*((∫ w,|ξ w|^p ∂P)+
      (d^(p-1)+bdgUpperMomentConstant p*d^(p/2-1))*K*
        (d+∫ r in 0..d,(∫ w,‖prefixPath hR (Y w) r‖^p ∂P))) := by
  change 0≤d ∧ d≤R at hd
  letI : MeasurableSpace Ω := m
  have hpoint w r (hr : r∈Icc 0 d) : restrictRealPath hd.2 (Y w) (projIcc 0 d hd.1 r)=Y w (projIcc 0 R hR r) := by
    rw [projIcc_of_mem hd.1 hr,projIcc_of_mem hR ⟨hr.1,hr.2.trans hd.2⟩]
    rfl
  have hUg' w r (hr : r∈Icc 0 d) : |U (w,r)|^p≤K*(1+|restrictRealPath hd.2 (Y w) (projIcc 0 d hd.1 r)|^p) := by
    rw [hpoint w r hr]
    exact hUg w r ⟨hr.1,hr.2.trans hd.2⟩
  have hGg' w r (hr : r∈Icc 0 d) : |G (w,r)|^p≤K*(1+|restrictRealPath hd.2 (Y w) (projIcc 0 d hd.1 r)|^p) := by
    rw [hpoint w r hr]
    exact hGg w r ⟨hr.1,hr.2.trans hd.2⟩
  have hrep' : ∀ᵐ w ∂P,∀ r,restrictRealPath hd.2 (Y w) r=ξ w+(∫ s in 0..r.val,U (w,s))+N (realTimeClamp r.val) w := by
    filter_upwards [hrep] with w hw
    intro r
    exact hw ⟨r.val,r.property.1,r.property.2.trans hd.2⟩
  have hb := scalar_integral_power_estimate P hT F hF hle hnull W A N hW hA hN
    c hc hcm hcT hct hcut hcc hclock G hG hi hNI d hd.1 ((EReal.coe_le_coe hd.2).trans_lt hRT) p hp
    (fun w => restrictRealPath hd.2 (Y w)) (restrict_real_path_measurable hd.2 Y hYm)
    (restrict_real_path_memLp_exponent P hd.2 Y hYm _ hYi) ξ hξm hξi U hUm hGm K hK hUg' hGg' hrep'
  simp_rw [restriction_eq_prefix_norm hd.1 hd.2] at hb
  have he : (∫ r in 0..d,(∫ w,‖prefixPath hd.1 (restrictRealPath hd.2 (Y w)) r‖^p ∂P))=
      ∫ r in 0..d,(∫ w,‖prefixPath hR (Y w) r‖^p ∂P) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r∈Icc 0 d := by simpa only [uIcc_of_le hd.1] using hr
    apply integral_congr_ae
    exact .of_forall (fun w => by dsimp only; rw [restricted_prefix_norm hd.1 hd.2 _ r hr'])
  simpa only [he] using hb

end Asakura.Chapter4
