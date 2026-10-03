import Chapter8RandomIntegralSquare
import Chapter8SmallMassBounds

open MeasureTheory Set
namespace Asakura.Chapter8
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Pointwise square estimates used for the three terms in the position
formula; valid in any real normed space. -/
theorem norm_three_sum_square {E : Type*} [NormedAddCommGroup E] (a b c : E) :
    ‖a+b+c‖^2≤3*(‖a‖^2+‖b‖^2+‖c‖^2) := by
  have h := (norm_add_le (a+b) c).trans (add_le_add (norm_add_le a b) le_rfl)
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖b‖-‖c‖),sq_nonneg (‖c‖-‖a‖)]

/-- Fubini and Cauchy--Schwarz bound the actual random Volterra integral.
The kernel may depend on the mass; only its uniform operator bound enters. -/
theorem random_volterra_bound {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (t : ℝ) (ht : 0≤t)
    (K : ℝ → E →L[ℝ] E) (hK : Continuous K)
    (H : Ω × ℝ → E) (hH : Measurable H)
    (h2 : MemLp H 2 (P.prod (volume.restrict (Ioc 0 t))))
    (L : ℝ) (hL : 0≤L) (hKb : ∀ s∈Icc 0 t,‖K s‖≤L) :
    MemLp (fun w => ∫ s in 0..t,K s (H (w,s))) 2 P ∧
      (∫ w,‖∫ s in 0..t,K s (H (w,s))‖^2 ∂P)≤
        t*L^2*(∫ s in 0..t,(∫ w,‖H (w,s)‖^2 ∂P)) := by
  let μ := volume.restrict (Ioc 0 t)
  let G := fun z : Ω × ℝ => K z.2 (H z)
  have hG : Measurable G := ((hK.comp continuous_fst).clm_apply continuous_snd).measurable.comp (measurable_snd.prodMk hH)
  have hG2 : MemLp G 2 (P.prod μ) := by
    apply h2.const_smul L |>.of_le hG.aestronglyMeasurable
    rw [Measure.ae_prod_iff_ae_ae] <;> try exact (measurableSet_le hG.norm ((hH.const_smul L).norm))
    apply ae_of_all
    intro w
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hb := (K s).le_opNorm (H (w,s))
    exact hb.trans (by simpa [norm_smul,Real.norm_eq_abs,abs_of_nonneg hL] using
      mul_le_mul_of_nonneg_right (hKb s ⟨hs.1.le,hs.2⟩) (norm_nonneg (H (w,s))))
  obtain ⟨hGi,hGb⟩ := random_integral_square_estimate P μ G hG hG2
  have hHi := h2.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hGi2 := hG2.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hb : (∫ s,(∫ w,‖G (w,s)‖^2 ∂P) ∂μ)≤L^2*(∫ s,(∫ w,‖H (w,s)‖^2 ∂P) ∂μ) := by
    rw [←integral_const_mul]
    apply integral_mono_ae hGi2.integral_prod_right (hHi.integral_prod_right.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioc,hHi.prod_left_ae,hGi2.prod_left_ae] with s hs hi gi
    rw [←integral_const_mul]
    apply integral_mono gi (hi.const_mul _)
    intro w
    have hh := ((K s).le_opNorm (H (w,s))).trans
      (mul_le_mul_of_nonneg_right (hKb s ⟨hs.1.le,hs.2⟩) (norm_nonneg _))
    simpa only [G,mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hh 2
  have hmass : μ.real univ=t := by simp [μ,Measure.real,ht]
  rw [hmass] at hGb
  refine ⟨by simpa only [intervalIntegral.integral_of_le ht,G,μ] using hGi,?_⟩
  have hh := hGb.trans (mul_le_mul_of_nonneg_left hb ht)
  simpa only [intervalIntegral.integral_of_le ht,G,μ,mul_assoc] using hh
end Asakura.Chapter8
