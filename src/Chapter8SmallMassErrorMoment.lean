import Chapter8RandomPositionMoment

open MeasureTheory Set
namespace Asakura.Chapter8
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Bounded deterministic linear maps preserve the actual L2 random
vectors and multiply their second-moment bound by the squared operator norm. -/
theorem random_linear_second_moment {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : Measure Ω) (A : E →L[ℝ] F) (X : Ω → E) (hX : MemLp X 2 P) :
    MemLp (fun w => A (X w)) 2 P ∧
      (∫ w,‖A (X w)‖^2 ∂P)≤‖A‖^2*(∫ w,‖X w‖^2 ∂P) := by
  have hA : MemLp (fun w => A (X w)) 2 P := A.comp_memLp' hX
  refine ⟨hA,?_⟩
  rw [←integral_const_mul]
  apply integral_mono (hA.integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    ((hX.integrable_norm_pow (by norm_num : (2:ℕ)≠0)).const_mul _)
  intro w
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm (X w)) 2

/-- The initial-velocity correction has the O(m²) bound used in the text. -/
theorem initial_velocity_second_moment {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) (M E0 : E →L[ℝ] E) (hE : ‖E0‖≤1)
    (m : ℝ) (hm : 0≤m) (V : Ω → E) (hV : MemLp V 2 P) :
    MemLp (fun w => m • M (V w-E0 (V w))) 2 P ∧
      (∫ w,‖m • M (V w-E0 (V w))‖^2 ∂P)≤4*m^2*‖M‖^2*(∫ w,‖V w‖^2 ∂P) := by
  let A := m • M.comp (ContinuousLinearMap.id ℝ E-E0)
  have hA := random_linear_second_moment P A V hV
  have hb : ‖A‖≤2*m*‖M‖ := by
    dsimp only [A]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hm]
    have he : ‖ContinuousLinearMap.id ℝ E-E0‖≤2 :=
      (norm_sub_le _ _).trans (by linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)])
    have hh := (ContinuousLinearMap.opNorm_comp_le M _).trans (mul_le_mul_of_nonneg_left he (norm_nonneg _))
    convert mul_le_mul_of_nonneg_left hh hm using 1 <;> ring
  have hs := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg A) hb 2)
    (integral_nonneg (μ := P) (fun w => sq_nonneg ‖V w‖))
  refine ⟨hA.1,?_⟩
  have hh := hA.2.trans hs
  convert hh using 1
  · rfl
  · ring

/-- Combine the three actual remainder terms. The force and initial
velocity are O(m²), while the noise is O(m), for 0<m≤1. -/
theorem small_mass_remainder_moment {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) (A D N : Ω → E) (hA : MemLp A 2 P) (hD : MemLp D 2 P) (hN : MemLp N 2 P)
    (m CA CD CN : ℝ) (hm : 0≤m) (hm1 : m≤1) (hCA : 0≤CA) (hCD : 0≤CD)
    (ha : (∫ w,‖A w‖^2 ∂P)≤CA*m^2) (hd : (∫ w,‖D w‖^2 ∂P)≤CD*m^2)
    (hn : (∫ w,‖N w‖^2 ∂P)≤CN*m) :
    (∫ w,‖A w+D w+N w‖^2 ∂P)≤3*(CA+CD+CN)*m := by
  have hh := random_three_sum_square P A D N hA hD hN
  have hm2 : m^2≤m := by nlinarith
  have ha' := ha.trans (mul_le_mul_of_nonneg_left hm2 hCA)
  have hd' := hd.trans (mul_le_mul_of_nonneg_left hm2 hCD)
  nlinarith

/-- Subtracting the overdamped equation leaves a Lipschitz drift integral
and the remainder. This gives the second Gronwall inequality in mean square. -/
theorem small_mass_error_moment {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : E →L[ℝ] E)
    (t : ℝ) (ht : 0≤t) (H : Ω × ℝ → E) (hH : Measurable H)
    (h2 : MemLp H 2 (P.prod (volume.restrict (Ioc 0 t))))
    (D R : Ω → E) (hR : MemLp R 2 P)
    (he : ∀ᵐ w ∂P,D w=R w+(∫ s in 0..t,(-M) (H (w,s))))
    (u : ℝ → ℝ) (hu : ContinuousOn u (Icc 0 t)) (L : ℝ)
    (hb : ∀ s∈Icc 0 t,(∫ w,‖H (w,s)‖^2 ∂P)≤L^2*u s) :
    (∫ w,‖D w‖^2 ∂P)≤3*(∫ w,‖R w‖^2 ∂P)+3*t*‖M‖^2*L^2*(∫ s in 0..t,u s) := by
  obtain ⟨hDi,hDb⟩ := random_volterra_bound P t ht (fun _ => -M) continuous_const H hH h2 ‖M‖ (norm_nonneg _) (by intro s hs; simp)
  have hi : IntervalIntegrable (fun s => ∫ w,‖H (w,s)‖^2 ∂P) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
    exact (h2.integrable_norm_pow (by norm_num : (2:ℕ)≠0)).integral_prod_right
  have hui := hu.intervalIntegrable_of_Icc (μ := volume) ht
  have hbi := intervalIntegral.integral_mono_on ht hi (hui.const_mul (L^2)) hb
  rw [intervalIntegral.integral_const_mul] at hbi
  have hbd := hDb.trans (mul_le_mul_of_nonneg_left hbi (mul_nonneg ht (sq_nonneg _)))
  have hh := random_three_sum_square P R (fun w => ∫ s in 0..t,(-M) (H (w,s))) (fun _ => 0) hR hDi MemLp.zero
  simp only [add_zero,norm_zero,zero_pow (by decide : 2≠0),integral_zero] at hh
  calc
    _ = ∫ w,‖R w+(∫ s in 0..t,(-M) (H (w,s)))‖^2 ∂P := integral_congr_ae (he.mono (fun w hw => by rw [hw]))
    _ ≤ _ := by nlinarith [hh,hbd]
end Asakura.Chapter8
