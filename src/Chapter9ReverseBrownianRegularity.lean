import Chapter9ReverseBrownian

open MeasureTheory Set
open scoped ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem reverse_drift_path_continuous {Ω : Type*} {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (X : ℝ → Ω → Fin d → ℝ) (hXc : ∀ w,Continuous (fun r => X r w))
    (T b : ℝ) (hbT : b<T) (w : Ω) (i : Fin d) :
    ContinuousOn (fun r => ouReverseDrift μ (T-r,X (T-r) w) i) (Icc 0 b) :=
  (ou_reverse_drift_coordinate_continuous μ i).comp
    ((show Continuous (fun r : ℝ => T-r) by fun_prop).prodMk
      ((hXc w).comp (by fun_prop))).continuousOn
    (fun r hr => ⟨show 0<T-r from sub_pos.mpr (hr.2.trans_lt hbT),mem_univ _⟩)

theorem reverse_brownian_adapted {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (X : ℝ → Ω → Fin d → ℝ) (hXc : ∀ w,Continuous (fun r => X r w))
    (T s : ℝ) (hs : 0≤s) (hsT : s<T) :
    Measurable[reversedNaturalInformation P X T s] (reverseBrownian μ X T s) := by
  apply (@measurable_pi_iff Ω (Fin d) (fun _ => ℝ)
    (reversedNaturalInformation P X T s) (fun _ => inferInstance) (reverseBrownian μ X T s)).mpr
  intro i
  have hI : Measurable[reversedNaturalInformation P X T s]
      (fun w => ∫ r in 0..s,ouReverseDrift μ (T-r,X (T-r) w) i) := by
    apply measurable_past_integral (m := reversedNaturalInformation P X T s) _ s hs
    · intro r hr
      have hX := (reversed_state_adapted P X T r hr.1).mono
        (reversed_information_monotone P X T hr.2) le_rfl
      exact ((measurable_pi_apply i).comp (ou_reverse_drift_measurable μ)).comp
        (measurable_const.prodMk hX)
    · exact fun w => reverse_drift_path_continuous μ X hXc T s hsT w i
  have hzero : Measurable[reversedNaturalInformation P X T s] (fun w => X T w i) := by
    have hh := ((measurable_pi_apply i).comp (reversed_state_adapted P X T 0 le_rfl)).mono
      (reversed_information_monotone P X T hs) le_rfl
    simpa only [sub_zero,Function.comp_def] using! hh
  exact ((((measurable_pi_apply i).comp (reversed_state_adapted P X T s hs)).sub hzero).sub hI).div_const _

theorem reverse_brownian_continuous {Ω : Type*} {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (X : ℝ → Ω → Fin d → ℝ) (hXc : ∀ w,Continuous (fun r => X r w))
    (T b : ℝ) (hb : 0≤b) (hbT : b<T) (w : Ω) :
    ContinuousOn (fun r => reverseBrownian μ X T r w) (Icc 0 b) := by
  apply continuousOn_pi.mpr
  intro i
  have ha := reverse_drift_path_continuous μ X hXc T b hbT w i
  have hi : IntervalIntegrable (fun r => ouReverseDrift μ (T-r,X (T-r) w) i) volume 0 b :=
    ha.intervalIntegrable_of_Icc hb
  have hc : ContinuousOn (fun r => ∫ u in 0..r,ouReverseDrift μ (T-u,X (T-u) w) i) (Icc 0 b) := by
    simpa only [uIcc_of_le hb] using intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
  exact (((((continuous_apply i).comp ((hXc w).comp (by fun_prop))).continuousOn).sub
    continuousOn_const).sub hc).div_const _

theorem reverse_brownian_zero {Ω : Type*} {d : ℕ}
    (μ : Measure (Fin d → ℝ)) (X : ℝ → Ω → Fin d → ℝ) (T : ℝ) (w : Ω) :
    reverseBrownian μ X T 0 w=0 := by
  ext i
  simp [reverseBrownian]

theorem reverse_brownian_sde_identity {Ω : Type*} {d : ℕ}
    (μ : Measure (Fin d → ℝ)) (X : ℝ → Ω → Fin d → ℝ) (T s : ℝ) (w : Ω) (i : Fin d) :
    X (T-s) w i=X T w i+(∫ r in 0..s,ouReverseDrift μ (T-r,X (T-r) w) i)+
      Real.sqrt 2*reverseBrownian μ X T s w i := by
  have hne : Real.sqrt (2:ℝ)≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold reverseBrownian
  rw [mul_div_cancel₀ _ hne]
  ring
end Asakura.Chapter9
