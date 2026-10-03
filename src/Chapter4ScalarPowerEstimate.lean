import Chapter4ProgressiveFinitePowerMoment
import Chapter4CoefficientQuadraticPower
import Chapter4CoefficientDriftPower
import Chapter4ThreeTermPowerMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The moment inequality for the actual SDE integral representation.
Both integral moment estimates are derived here from the coefficients. -/
theorem scalar_integral_power_estimate
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
    (hrep : ∀ᵐ w ∂P,∀ r,Y w r=ξ w+(∫ s in 0..r.val,U (w,s))+N (realTimeClamp r.val) w) :
    (∫ w,‖Y w‖^p ∂P)≤(3:ℝ)^(p-1)*((∫ w,|ξ w|^p ∂P)+
      (R^(p-1)+bdgUpperMomentConstant p*R^(p/2-1))*K*
        (R+∫ r in 0..R,(∫ w,‖prefixPath hR (Y w) r‖^p ∂P))) := by
  letI : MeasurableSpace Ω := m
  have hp0 : 0<p := by linarith only [hp]
  have hp1 : 1≤p := by linarith only [hp]
  obtain ⟨henergy,hEb⟩ := coefficient_quadratic_power_moment P R hR p hp Y hYm hYi G hGm K hK hGg
  obtain ⟨hs,hZi,hZb⟩ := progressive_ito_finite_power_moment P hT F hF hle hnull W A N hW hA hN
    c hc hcm hcT hct hcut hcc hclock G hG hi hNI R hR hRT p hp0 henergy
  let Z := finiteRealPath N R hs
  let B := fun w => ContinuousMap.const (Icc (0:ℝ) R) (ξ w)
  let D := fun w => Y w-B w-Z w
  have hBm : Measurable[m] B := ContinuousMap.measurable_iff_eval.mpr (fun _ => hξm)
  have hZm : Measurable[m] Z := finite_real_path_measurable F hle N R hRT hs (hN.adapted P F)
  have hDm : Measurable[m] D := (hYm.sub hBm).sub hZm
  have hDr : ∀ᵐ w ∂P,∀ r,D w r=∫ s in 0..r.val,U (w,s) := by
    filter_upwards [hrep] with w hw
    intro r
    change Y w r-ξ w-N (realTimeClamp r.val) w=_
    rw [hw r]
    ring
  obtain ⟨hDi,hDb⟩ := coefficient_drift_power_moment P R hR p hp1 Y hYm hYi U hUm K hK hUg D hDm.aestronglyMeasurable hDr
  letI : Nonempty (Icc (0:ℝ) R) := ⟨⟨0,le_rfl,hR⟩⟩
  have he : Y=ᵐ[P] fun w => B w+D w+Z w := .of_forall (fun w => by dsimp only [D]; abel)
  have hb := (three_term_path_power_moment P ξ hξm p hp1 hξi Y D Z hDi hZi he).2
  have hNb := hZb.trans (mul_le_mul_of_nonneg_left hEb (bdg_moment_constants_positive p hp0).1.le)
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
  nlinarith only [hDb,hNb]

end Asakura.Chapter4
