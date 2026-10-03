import Chapter4MultipleNoisePowerEstimate
import Chapter4VectorPowerNorm
import Chapter4RunningNormPath

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

theorem vector_integral_running_power_estimate
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
    (hUg : ∀ i w r,r∈Icc 0 R → |U i (w,r)|^p≤K*(1+‖prefixPath hR (normEnvelope (Y w)) r‖^p))
    (hGg : ∀ i j w r,r∈Icc 0 R → |G i j (w,r)|^p≤K*(1+‖prefixPath hR (normEnvelope (Y w)) r‖^p))
    (hrep : ∀ᵐ w ∂P,∀ r i,Y w r i=ξ i w+(∫ s in 0..r.val,U i (w,s))+∑ j,N i j (realTimeClamp r.val) w) :
    (∫ w,‖Y w‖^p ∂P)≤(dim:ℝ)^(p-1)*(3:ℝ)^(p-1)*
      ((∑ i,∫ w,|ξ i w|^p ∂P)+(dim:ℝ)*
      (R^(p-1)+((d:ℝ)^(p-1)*d)*bdgUpperMomentConstant p*R^(p/2-1))*K*
        (R+∫ r in 0..R,(∫ w,‖prefixPath hR (normEnvelope (Y w)) r‖^p ∂P))) := by
  letI : MeasurableSpace Ω := m
  have hp1 : 1≤p := by linarith only [hp]
  let Q := fun w => runningNormPath hR (normEnvelope (Y w))
  have hQm := running_norm_path_measurable hR (fun w => normEnvelope (Y w)) (norm_envelope_measurable Y hYm)
  have hQi := running_norm_path_memLp P hR (fun w => normEnvelope (Y w))
    (norm_envelope_measurable Y hYm) (ENNReal.ofReal p) ((norm_envelope_memLp P Y hYm (ENNReal.ofReal p)).2 hYi)
  have hh i := multiple_noise_envelope_power_estimate P hT F hF hle hnull W A (N i) hW hA (hN i)
    c hc hcm hcT hct hcut hcc hclock (G i) (hG i) (hi i) (hNI i) R hR hRT p hp
    (fun w => coordinateRealPath (Y w) i) (coordinate_path_measurable Y hYm i) Q hQm hQi
    (ξ i) (hξm i) (hξi i) (U i) (hUm i) (hGm i) K hK
    (fun w r hr => by
      simpa only [Q,runningNormPath,ContinuousMap.coe_mk,projIcc_of_mem hR hr,abs_norm] using hUg i w r hr)
    (fun j w r hr => by
      simpa only [Q,runningNormPath,ContinuousMap.coe_mk,projIcc_of_mem hR hr,abs_norm] using hGg i j w r hr)
    (hrep.mono (fun w hw r => hw r i))
  have hint : (∫ r in 0..R,(∫ w,‖prefixPath hR (Q w) r‖^p ∂P))=
      ∫ r in 0..R,(∫ w,‖prefixPath hR (normEnvelope (Y w)) r‖^p ∂P) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r∈Icc 0 R := by simpa only [uIcc_of_le hR] using hr
    apply integral_congr_ae
    exact ae_of_all _ fun w => by
      dsimp only
      rw [show ‖prefixPath hR (Q w) r‖=‖prefixPath hR (normEnvelope (Y w)) r‖ from
        running_norm_path_prefix hR (normEnvelope (Y w)) r hr']
  have hb := bundle_path_power_moment P (fun i w => coordinateRealPath (Y w) i)
    (coordinate_path_measurable Y hYm) p hp1 (fun i => (hh i).1)
  have he : ∀ w,bundleRealPaths (fun i => coordinateRealPath (Y w) i)=Y w := by
    intro w
    apply ContinuousMap.ext
    intro r
    rfl
  simp_rw [he] at hb
  apply hb.trans
  have hs := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => (hh i).2))
    (Real.rpow_nonneg (Nat.cast_nonneg dim) (p-1))
  simp only [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,hint] at hs
  convert hs using 1 <;> ring

end Asakura.Chapter4
