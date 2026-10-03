import Chapter3BoundedItoExpectation
import Chapter3AbsolutePowerC2
import Chapter3MomentHolder

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Ito applied to |X|^p, followed by the actual mean-zero and Holder arguments. -/
theorem absolute_power_ito_moment_bound
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
      Integrable (fun ω => |X b ω|^p) P ∧
      (∫ ω, |X b ω|^p ∂P) ≤ (p*(p-1)/2)*
        (∫ ω, ‖continuousPath (fun t ω => X (min b t) ω) hx ω‖^p ∂P)^((p-2)/p)*
        (∫ ω, A b ω^(p/2) ∂P)^(2/p) := by
  have hp0 : 0 < p := by linarith
  have hpr : 0 ≤ p-2 := by linarith
  have hpp : 0 ≤ p*(p-1) := mul_nonneg hp0.le (by linarith)
  have hAp ω t (ht : t < ⊤) : 0 ≤ A t ω := by
    rw [← hA0 ω]
    exact hAm ω hT ht bot_le
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

  have hXm : Measurable (fun ω => |X b ω|) := by
    simpa only [Real.norm_eq_abs] using ((hX.adapted P F b hb).mono (hle b) le_rfl).norm
  have hfi : Integrable (fun ω => |X b ω|^p) P := by
    apply (integrable_const (L^p)).mono'
      ((Real.continuous_rpow_const hp0.le).measurable.comp
        hXm).aestronglyMeasurable
    filter_upwards [hXbound] with ω hω
    change ‖|X b ω|^p‖ ≤ L^p
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) p)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hω b le_rfl) hp0.le
  have hf := absolute_power_C2 p hp
  have hDb : ∀ᵐ ω ∂P, ∀ s, s ≤ b → |deriv (fun x : ℝ => |x|^p) (X s ω)| ≤ p*L^(p-2)*L := by
    filter_upwards [hXbound] with ω hω
    intro s hs
    rw [hf.2.1,abs_mul,abs_mul,abs_of_nonneg hp0.le,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) (hω s hs) hpr) hp0.le)
      (hω s hs) (abs_nonneg _) (mul_nonneg hp0.le (Real.rpow_nonneg hL _))
  have hDDb : ∀ᵐ ω ∂P, ∀ s, s ≤ b → |iteratedDeriv 2 (fun x : ℝ => |x|^p) (X s ω)| ≤ p*(p-1)*L^(p-2) := by
    filter_upwards [hXbound] with ω hω
    intro s hs
    rw [hf.2.2,abs_of_nonneg (mul_nonneg hpp (Real.rpow_nonneg (abs_nonneg _) _))]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) (hω s hs) hpr) hpp
  obtain ⟨J,hJi,hJe,hJbound⟩ := bounded_C2_ito_expectation P hT F hF hle hnull X A hX hA hAm hAc hA0
    (fun x : ℝ => |x|^p) hf.1 (by simp [hp0.ne']) b hb K (p*L^(p-2)*L) (p*(p-1)*L^(p-2))
    hK (by positivity) (by positivity) hbound hDb hDDb hfi
  have ha : 0 < (p-2)/p := div_pos (by linarith) hp0
  have ha1 : (p-2)/p < 1 := (div_lt_one hp0).mpr (by linarith)
  have hh := fractional_moment_holder P (fun ω => S ω^p) (fun ω => A b ω^(p/2)) hSi hQi
    (fun ω => Real.rpow_nonneg (hSp ω) _) (fun ω => Real.rpow_nonneg (hAp ω b hb) _)
    ((p-2)/p) ha ha1
  have hdom : ∀ᵐ ω ∂P, J b ω ≤ (p*(p-1))*((S ω^p)^((p-2)/p)*(A b ω^(p/2))^(1-(p-2)/p)) := by
    filter_upwards [hJbound] with ω hω
    have hSbound s (hs : s ≤ b) : |X s ω| ≤ S ω := by
      have hn := (continuousPath (fun t ω => X (min b t) ω) hx ω).norm_coe_le_norm s
      simpa only [S,continuousPath,ContinuousMap.coe_mk,min_eq_right hs,Real.norm_eq_abs] using hn
    have hj := hω (p*(p-1)*S ω^(p-2)) (mul_nonneg hpp (Real.rpow_nonneg (hSp ω) _)) (by
      intro s hs
      rw [hf.2.2,abs_of_nonneg (mul_nonneg hpp (Real.rpow_nonneg (abs_nonneg _) _))]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) (hSbound s hs) hpr) hpp)
    have he : p*(p-1)*S ω^(p-2)*A b ω =
        (p*(p-1))*((S ω^p)^((p-2)/p)*(A b ω^(p/2))^(1-(p-2)/p)) := by
      rw [← Real.rpow_mul (hSp ω),← Real.rpow_mul (hAp ω b hb)]
      have e1 : p*((p-2)/p) = p-2 := by field_simp
      have e2 : (p/2)*(1-(p-2)/p) = 1 := by field_simp; ring
      rw [e1,e2,Real.rpow_one]
      ring
    exact ((le_abs_self _).trans hj).trans_eq he
  have hineq : (∫ ω, J b ω ∂P) ≤
      (p*(p-1))*((∫ ω, S ω^p ∂P)^((p-2)/p)*(∫ ω, A b ω^(p/2) ∂P)^(1-(p-2)/p)) :=
    (integral_mono_ae hJi (hh.1.const_mul (p*(p-1))) hdom).trans
    (by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hh.2 hpp)
  refine ⟨hx,hSi,hfi,?_⟩
  rw [hJe]
  have he : 1-(p-2)/p = 2/p := by field_simp; ring
  rw [he] at hineq
  dsimp [S] at hineq
  linarith

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.absolute_power_ito_moment_bound
