import Chapter4ProgressiveFinitePowerMoment
import Chapter4CoefficientQuadraticPower
import Chapter4CoefficientDriftPower
import Chapter4ThreeTermPowerMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The moment inequality for the actual SDE integral representation.
Both integral moment estimates are derived here from the coefficients. -/
theorem multiple_noise_envelope_power_estimate
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    {d : ℕ} (W A N : Fin d → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hA : ∀ j,LocalCovarianceWitness P F (W j) (W j) (A j))
    (hN : ∀ j,LocalMProcessWitness P F (N j))
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ j n w r, r ∈ Icc 0 (c n) → A j (realTimeClamp r) w = r)
    (G : Fin d → Ω × ℝ → ℝ)
    (hG : ∀ j n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => G j (z.1,z.2.val)))
    (hi : ∀ j n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G j (w,r)^2) volume 0 (c n))
    (hNI : ∀ j,ItoCovarianceFormula P F (W j) (G j) (N j))
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) (p : ℝ) (hp : 2≤p)
    (Y : Ω → C(Icc (0:ℝ) R,ℝ)) (hYm : Measurable[m] Y) 
    (Q : Ω → C(Icc (0:ℝ) R,ℝ)) (hQm : Measurable[m] Q) (hQi : MemLp Q (ENNReal.ofReal p) P)
    (ξ : Ω → ℝ) (hξm : Measurable[m] ξ) (hξi : MemLp ξ (ENNReal.ofReal p) P)
    (U : Ω × ℝ → ℝ) (hUm : Measurable[m.prod inferInstance] U) (hGm : ∀ j,Measurable[m.prod inferInstance] (G j))
    (K : ℝ) (hK : 0≤K)
    (hUg : ∀ w r,r∈Icc 0 R → |U (w,r)|^p≤K*(1+|Q w (projIcc 0 R hR r)|^p))
    (hGg : ∀ j w r,r∈Icc 0 R → |G j (w,r)|^p≤K*(1+|Q w (projIcc 0 R hR r)|^p))
    (hrep : ∀ᵐ w ∂P,∀ r,Y w r=ξ w+(∫ s in 0..r.val,U (w,s))+∑ j,N j (realTimeClamp r.val) w) :
    MemLp Y (ENNReal.ofReal p) P ∧
    (∫ w,‖Y w‖^p ∂P)≤(3:ℝ)^(p-1)*((∫ w,|ξ w|^p ∂P)+
      (R^(p-1)+((d:ℝ)^(p-1)*d)*bdgUpperMomentConstant p*R^(p/2-1))*K*
        (R+∫ r in 0..R,(∫ w,‖prefixPath hR (Q w) r‖^p ∂P))) := by
  letI : MeasurableSpace Ω := m
  have hp0 : 0<p := by linarith only [hp]
  have hp1 : 1≤p := by linarith only [hp]
  have he j := coefficient_quadratic_power_moment P R hR p hp Q hQm hQi (G j) (hGm j) K hK (hGg j)
  have hn j := progressive_ito_finite_power_moment P hT F hF hle hnull (W j) (A j) (N j) (hW j) (hA j) (hN j)
    c hc hcm hcT hct hcut hcc (hclock j) (G j) (hG j) (hi j) (hNI j) R hR hRT p hp0 (he j).1
  let V := fun j => finiteRealPath (N j) R (hn j).choose
  have hVi j : MemLp (V j) (ENNReal.ofReal p) P := (hn j).choose_spec.1
  have hVm j : Measurable[m] (V j) := finite_real_path_measurable F hle (N j) R hRT (hn j).choose ((hN j).adapted P F)
  let Z := fun w => ∑ j,V j w
  have hZm : Measurable[m] Z := Finset.measurable_sum Finset.univ (fun j _ => hVm j)
  obtain ⟨hZi,hZb⟩ := finite_sum_power_moment P V p hp1 hVi
  have hNb : (∫ w,‖Z w‖^p ∂P)≤((d:ℝ)^(p-1)*d)*bdgUpperMomentConstant p*
      (R^(p/2-1)*K)*(R+∫ r in 0..R,(∫ w,‖prefixPath hR (Q w) r‖^p ∂P)) := by
    apply hZb.trans
    have hj j := (hn j).choose_spec.2.trans
      (mul_le_mul_of_nonneg_left (he j).2 (bdg_moment_constants_positive p hp0).1.le)
    have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hj j))
      (Real.rpow_nonneg (Nat.cast_nonneg d) (p-1))
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using hh
  let B := fun w => ContinuousMap.const (Icc (0:ℝ) R) (ξ w)
  let D := fun w => Y w-B w-Z w
  have hBm : Measurable[m] B := ContinuousMap.measurable_iff_eval.mpr (fun _ => hξm)
  have hDm : Measurable[m] D := (hYm.sub hBm).sub hZm
  have hDr : ∀ᵐ w ∂P,∀ r,D w r=∫ s in 0..r.val,U (w,s) := by
    filter_upwards [hrep] with w hw
    intro r
    change Y w r-ξ w-(∑ j,V j w) r=_
    simp only [ContinuousMap.sum_apply]
    change Y w r-ξ w-(∑ j,N j (realTimeClamp r.val) w)=_
    rw [hw r]
    ring
  obtain ⟨hDi,hDb⟩ := coefficient_drift_power_moment P R hR p hp1 Q hQm hQi U hUm K hK hUg D hDm.aestronglyMeasurable hDr
  letI : Nonempty (Icc (0:ℝ) R) := ⟨⟨0,le_rfl,hR⟩⟩
  have he : Y=ᵐ[P] fun w => B w+D w+Z w := .of_forall (fun w => by dsimp only [D]; abel)
  have hb := (three_term_path_power_moment P ξ hξm p hp1 hξi Y D Z hDi hZi he)
  refine ⟨hb.1,?_⟩
  apply hb.2.trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
  nlinarith only [hDb,hNb]

end Asakura.Chapter4
