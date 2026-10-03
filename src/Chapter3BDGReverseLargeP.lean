import Chapter3IncreasingItoWeightConstruction
import Chapter3PowerItoStoppedEnergy
import Chapter3MomentCancellation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The entire p>2 reverse BDG moment estimate at the bounded stage. -/
theorem bdg_reverse_large_p_bounded
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (hAm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hA0 : ∀ ω, A ⊥ ω = 0)
    (p : ℝ) (hp : 2 < p)
    (b : ClosedTime T) (hb : b < ⊤) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ᵐ ω ∂P, A b ω ≤ K)
    (L : ℝ) (hL : 0 ≤ L)
    (hXbound : ∀ᵐ ω ∂P, ∀ s, s ≤ b → |X s ω| ≤ L) :
    ∃ hx : ∀ ω, Continuous (fun t => X (min b t) ω),
      Integrable (fun ω => ‖continuousPath (fun t ω => X (min b t) ω) hx ω‖^p) P ∧
      Integrable (fun ω => A b ω^(p/2)) P ∧
      (∫ ω, A b ω^(p/2) ∂P) ≤
        (2*p)^(p/2)*(∫ ω, ‖continuousPath (fun t ω => X (min b t) ω) hx ω‖^p ∂P) := by
  have hp0 : 0 < p := by linarith
  have hAp ω t (ht : t < ⊤) : 0 ≤ A t ω := by
    rw [← hA0 ω]
    exact hAm ω hT ht bot_le
  let V := fun t ω => A t ω^((p-2)/4)
  have hr : 0 ≤ (p-2)/4 := by linarith
  have hVa t (ht : t < ⊤) : Measurable[F t] (V t) :=
    (Real.continuous_rpow_const hr).measurable.comp (hA.adapted P F hX hX t ht)
  have hVc ω t (ht : t < ⊤) : ContinuousAt (fun s => V s ω) t :=
    (hAc ω t ht).rpow_const (Or.inr hr)
  have hVm ω : MonotoneOn (fun t => V t ω) (Iio ⊤) := by
    intro s hs t ht hst
    exact Real.rpow_le_rpow (hAp ω s hs) (hAm ω hs ht hst) hr
  obtain ⟨Y,hY,hy,hYbound⟩ := increasing_ito_weight_constructed P hT F hF hle hnull X V hX
    hVa hVc hVm (fun ω t ht => Real.rpow_nonneg (hAp ω t ht) _)
  have henergy := power_ito_stopped_energy P hT F hF hle hnull X A Y hX hA hAm hAc hA0
    p hp hY hy b hb K hK hbound
  have hx ω : Continuous (fun t => X (min b t) ω) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hX.path P F ω _ ((min_le_left b t).trans_lt hb)).comp
      (continuous_const.min continuous_id).continuousAt
  let S := fun ω => ‖continuousPath (fun t ω => X (min b t) ω) hx ω‖
  have hSp ω : 0 ≤ S ω := norm_nonneg _
  have hSm : Measurable S := (continuous_path_measurable _ hx (by
    intro t
    exact (hX.adapted P F _ ((min_le_left b t).trans_lt hb)).mono (hle _) le_rfl)).norm
  have hSb : ∀ᵐ ω ∂P, S ω ≤ L := by
    filter_upwards [hXbound] with ω hω
    apply (ContinuousMap.norm_le _ hL).mpr
    intro t
    simpa only [continuousPath,ContinuousMap.coe_mk,Real.norm_eq_abs] using hω (min b t) (min_le_left b t)
  have hSi : Integrable (fun ω => S ω^p) P := by
    apply (integrable_const (L^p)).mono'
      ((Real.continuous_rpow_const hp0.le).measurable.comp hSm).aestronglyMeasurable
    filter_upwards [hSb] with ω hω
    change ‖S ω^p‖ ≤ L^p
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (hSp ω) p)]
    exact Real.rpow_le_rpow (hSp ω) hω hp0.le
  have hQi : Integrable (fun ω => A b ω^(p/2)) P := by
    apply (integrable_const (K^(p/2))).mono'
      ((Real.continuous_rpow_const (by positivity : 0 ≤ p/2)).measurable.comp
        ((hA.adapted P F hX hX b hb).mono (hle b) le_rfl)).aestronglyMeasurable
    filter_upwards [hbound] with ω hω
    change ‖A b ω^(p/2)‖ ≤ K^(p/2)
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (hAp ω b hb) _)]
    exact Real.rpow_le_rpow (hAp ω b hb) hω (by positivity)
  have ha : 0 < 2/p := by positivity
  have ha1 : 2/p < 1 := (div_lt_one hp0).mpr hp
  have hh := fractional_moment_holder P (fun ω => S ω^p) (fun ω => A b ω^(p/2)) hSi hQi
    (fun ω => Real.rpow_nonneg (hSp ω) _) (fun ω => Real.rpow_nonneg (hAp ω b hb) _) (2/p) ha ha1
  have hdom : ∀ᵐ ω ∂P, Y b ω^2 ≤ 4*((S ω^p)^(2/p)*(A b ω^(p/2))^(1-2/p)) := by
    filter_upwards [hYbound] with ω hω
    have hSbound s (hs : s ≤ b) : |X s ω| ≤ S ω := by
      have hn := (continuousPath (fun t ω => X (min b t) ω) hx ω).norm_coe_le_norm s
      simpa only [S,continuousPath,ContinuousMap.coe_mk,min_eq_right hs,Real.norm_eq_abs] using hn
    have hyb := hω b hb (S ω) (hSp ω) hSbound
    have hypos : 0 ≤ 2*S ω*V b ω :=
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hSp ω))
        (Real.rpow_nonneg (hAp ω b hb) ((p-2)/4))
    have hsq := sq_le_sq₀ (abs_nonneg (Y b ω)) hypos
    have hsq' := hsq.mpr hyb
    rw [sq_abs] at hsq'
    have he : (2*S ω*V b ω)^2 = 4*((S ω^p)^(2/p)*(A b ω^(p/2))^(1-2/p)) := by
      dsimp [V]
      rw [mul_pow,mul_pow,← Real.rpow_two (A b ω^((p-2)/4)),
        ← Real.rpow_mul (hAp ω b hb),← Real.rpow_mul (hSp ω),← Real.rpow_mul (hAp ω b hb)]
      have e1 : p*(2/p) = 2 := by field_simp
      have e2 : ((p-2)/4)*2 = (p/2)*(1-2/p) := by field_simp; ring
      rw [e1,e2,Real.rpow_two]
      norm_num
      ring
    exact hsq'.trans_eq he
  have hYi : Integrable (fun ω => Y b ω^2) P := by
    simpa only [min_top_right] using
      (memLp_two_iff_integrable_sq (henergy.1.moment ⊤).aestronglyMeasurable).mp (henergy.1.moment ⊤)
  have hineq : (2/p)*(∫ ω, A b ω^(p/2) ∂P) ≤
      4*((∫ ω, S ω^p ∂P)^(2/p)*(∫ ω, A b ω^(p/2) ∂P)^(1-2/p)) := by
    rw [← henergy.2]
    exact (integral_mono_ae hYi (hh.1.const_mul 4) hdom).trans
      (by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hh.2 (by norm_num))
  have hineq' : (∫ ω, A b ω^(p/2) ∂P) ≤
      (2*p)*(∫ ω, S ω^p ∂P)^(2/p)*(∫ ω, A b ω^(p/2) ∂P)^(1-2/p) := by
    have h := mul_le_mul_of_nonneg_left hineq (show 0 ≤ p/2 by positivity)
    have he : (p/2)*(2/p) = 1 := by field_simp
    rw [← mul_assoc,he,one_mul] at h
    nlinarith [h]
  have hc := fractional_moment_cancel
    (integral_nonneg (fun ω => Real.rpow_nonneg (hAp ω b hb) _))
    (integral_nonneg (fun ω => Real.rpow_nonneg (hSp ω) _)) (by positivity : 0 ≤ 2*p) ha ha1 hineq'
  have he : 1/(2/p) = p/2 := by field_simp
  rw [he] at hc
  exact ⟨hx,hSi,hQi,hc⟩

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.bdg_reverse_large_p_bounded
