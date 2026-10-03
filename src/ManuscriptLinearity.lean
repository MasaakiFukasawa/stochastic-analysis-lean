import ManuscriptConvergence
import ManuscriptENNApproximation
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- app0:489: the exact dyadic simple approximations followed by MCT. -/
theorem manuscript_lintegral_add (f g : Ω → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, f x + g x ∂μ) = (∫⁻ x, f x ∂μ) + ∫⁻ x, g x ∂μ := by
  choose s hs using fun n => manuscript_ennphi_simple f hf n
  choose t ht using fun n => manuscript_ennphi_simple g hg n
  have hsf : ∀ x, (⨆ n, s n x) = f x := by intro x; simp_rw [hs]; exact manuscript_ennphi_iSup _
  have htg : ∀ x, (⨆ n, t n x) = g x := by intro x; simp_rw [ht]; exact manuscript_ennphi_iSup _
  have hsm : Monotone (fun n x => s n x) := by
    intro n m hnm x; simp_rw [hs]; exact manuscript_ennphi_increasing _ hnm
  have htm : Monotone (fun n x => t n x) := by
    intro n m hnm x; simp_rw [ht]; exact manuscript_ennphi_increasing _ hnm
  have hsum : ∀ x, f x + g x = ⨆ n, (s n + t n) x := by
    intro x
    rw [← hsf x, ← htg x, ENNReal.iSup_add_iSup_of_monotone (fun n m h => hsm h x) (fun n m h => htm h x)]
    rfl
  simp_rw [hsum]
  rw [manuscript_monotone_convergence (fun n => (s n + t n).measurable)
    (by intro n m h x; exact add_le_add (hsm h x) (htm h x))]
  simp_rw [(s _ + t _).lintegral_eq_lintegral, manuscript_simple_integral_add]
  rw [← ENNReal.iSup_add_iSup_of_monotone
    (fun n m h => manuscript_simple_integral_mono μ _ _ (hsm h))
    (fun n m h => manuscript_simple_integral_mono μ _ _ (htm h))]
  congr 1
  · simp_rw [← (s _).lintegral_eq_lintegral]
    rw [← manuscript_monotone_convergence (fun n => (s n).measurable) hsm]
    simp_rw [hsf]
  · simp_rw [← (t _).lintegral_eq_lintegral]
    rw [← manuscript_monotone_convergence (fun n => (t n).measurable) htm]
    simp_rw [htg]

/-- Constant multiples: same approximations and the finite-sum formula. -/
theorem manuscript_lintegral_const_mul (c : ℝ≥0∞) (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, c * f x ∂μ) = c * ∫⁻ x, f x ∂μ := by
  choose s hs using fun n => manuscript_ennphi_simple f hf n
  have hsf : ∀ x, (⨆ n, s n x) = f x := by intro x; simp_rw [hs]; exact manuscript_ennphi_iSup _
  have hsm : Monotone (fun n x => s n x) := by
    intro n m hnm x; simp_rw [hs]; exact manuscript_ennphi_increasing _ hnm
  conv_lhs => arg 2; ext x; rw [← hsf x, ENNReal.mul_iSup]
  rw [manuscript_monotone_convergence (f := fun n x => c * s n x)
    (fun n => measurable_const.mul (s n).measurable)
    (by intro n m h x; exact mul_le_mul_right (hsm h x) c)]
  have heq : ∀ n, (∫⁻ x, c * s n x ∂μ) = c * (s n).lintegral μ := by
    intro n
    change (∫⁻ x, (SimpleFunc.const Ω c * s n) x ∂μ) = _
    rw [(SimpleFunc.const Ω c * s n).lintegral_eq_lintegral, SimpleFunc.const_mul_lintegral]
  simp_rw [heq]
  rw [← ENNReal.mul_iSup]
  congr 1
  simp_rw [← (s _).lintegral_eq_lintegral]
  rw [← manuscript_monotone_convergence (fun n => (s n).measurable) hsm]
  simp_rw [hsf]

/-- Finite positive-part integrals; only domination by the norm is used. -/
theorem manuscript_positive_integral_finite (f : Ω → ℝ) (hf : Integrable f μ) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≠ ⊤ :=
  ne_top_of_le_ne_top hf.hasFiniteIntegral.ne (lintegral_ofReal_le_lintegral_enorm f)

/-- Nonnegative real-valued additivity obtained from the dyadic proof above. -/
theorem manuscript_nonneg_integral_add (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    (∫ x, f x + g x ∂μ) = (∫ x, f x ∂μ) + ∫ x, g x ∂μ := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun x => add_nonneg (hf0 x) (hg0 x)))
      (hf.add hg).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hf.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg0) hg.aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_add (hf0 _) (hg0 _)]
  rw [manuscript_lintegral_add μ _ _ hf.ennreal_ofReal hg.ennreal_ofReal,
    ENNReal.toReal_add (manuscript_positive_integral_finite μ f hfi)
      (manuscript_positive_integral_finite μ g hgi)]

/-- The manuscript's positive/negative-parts identity, before subtraction. -/
theorem manuscript_signed_parts_identity (x y : ℝ) :
    max (x+y) 0 + max (-x) 0 + max (-y) 0 =
      max (-(x+y)) 0 + max x 0 + max y 0 := by
  simp only [max_def]
  split_ifs <;> linarith

/-- Definition bridge from Bochner's integral to the manuscript's signed integral. -/
theorem manuscript_integral_parts (f : Ω → ℝ) (hf : Measurable f) (hi : Integrable f μ) :
    (∫ x, f x ∂μ) = (∫ x, max (f x) 0 ∂μ) - ∫ x, max (-f x) 0 ∂μ := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun x => le_max_right (f x) 0))
      (hf.max measurable_const).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun x => le_max_right (-f x) 0))
      (hf.neg.max measurable_const).aestronglyMeasurable]
  simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_zero]

/-- app0:510--531: integrate that identity and subtract only finite integrals. -/
theorem manuscript_real_integral_add (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hfi : Integrable f μ) (hgi : Integrable g μ) :
    (∫ x, f x + g x ∂μ) = (∫ x, f x ∂μ) + ∫ x, g x ∂μ := by
  let P := fun h : Ω → ℝ => fun x => max (h x) 0
  let N := fun h : Ω → ℝ => fun x => max (-h x) 0
  have hPm : ∀ h, Measurable h → Measurable (P h) := fun h hh => hh.max measurable_const
  have hNm : ∀ h, Measurable h → Measurable (N h) := fun h hh => hh.neg.max measurable_const
  have hPi : ∀ h, Integrable h μ → Integrable (P h) μ := fun h hh => by simpa [P, Real.coe_toNNReal'] using hh.real_toNNReal
  have hNi : ∀ h, Integrable h μ → Integrable (N h) μ := fun h hh => by simpa [N, Real.coe_toNNReal'] using hh.neg.real_toNNReal
  have hP0 : ∀ h x, 0 ≤ P h x := fun h x => le_max_right _ _
  have hN0 : ∀ h x, 0 ≤ N h x := fun h x => le_max_right _ _
  have heq : (∫ x, (P (f+g) x + N f x) + N g x ∂μ) =
      ∫ x, (N (f+g) x + P f x) + P g x ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => manuscript_signed_parts_identity (f x) (g x))
  rw [manuscript_nonneg_integral_add μ (fun x => P (f+g) x + N f x) (N g) ((hPm _ (hf.add hg)).add (hNm _ hf)) (hNm _ hg)
      ((hPi _ (hfi.add hgi)).add (hNi _ hfi)) (hNi _ hgi)
      (fun x => add_nonneg (hP0 _ x) (hN0 _ x)) (hN0 _),
    manuscript_nonneg_integral_add μ _ _ (hPm _ (hf.add hg)) (hNm _ hf)
      (hPi _ (hfi.add hgi)) (hNi _ hfi) (hP0 _) (hN0 _),
    manuscript_nonneg_integral_add μ (fun x => N (f+g) x + P f x) (P g) ((hNm _ (hf.add hg)).add (hPm _ hf)) (hPm _ hg)
      ((hNi _ (hfi.add hgi)).add (hPi _ hfi)) (hPi _ hgi)
      (fun x => add_nonneg (hN0 _ x) (hP0 _ x)) (hP0 _),
    manuscript_nonneg_integral_add μ _ _ (hNm _ (hf.add hg)) (hPm _ hf)
      (hNi _ (hfi.add hgi)) (hPi _ hfi) (hN0 _) (hP0 _)] at heq
  have hparts := manuscript_integral_parts μ _ (hf.add hg) (hfi.add hgi)
  have hpartf := manuscript_integral_parts μ _ hf hfi
  have hpartg := manuscript_integral_parts μ _ hg hgi
  change (∫ x, f x + g x ∂μ) = _
  dsimp [P,N] at heq
  simp only [Pi.add_apply, Real.coe_toNNReal'] at hparts hpartf hpartg
  linarith

/-- Negative signs swap positive and negative parts in the defining formula. -/
theorem manuscript_real_integral_neg (f : Ω → ℝ) (hf : Integrable f μ) :
    (∫ x, -f x ∂μ) = -(∫ x, f x ∂μ) := by
  change (∫ x, (-f) x ∂μ) = _
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf.neg,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  simp only [Pi.neg_apply, neg_neg]
  ring

theorem manuscript_real_integral_nonneg_mul (c : ℝ) (hc : 0 ≤ c) (f : Ω → ℝ)
    (hf : Measurable f) (hfi : Integrable f μ) :
    (∫ x, c*f x ∂μ) = c * ∫ x, f x ∂μ := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hfi.const_mul c),
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi]
  simp_rw [show ∀ x, -(c*f x) = c*(-f x) from fun x => by ring,
    ENNReal.ofReal_mul hc]
  rw [manuscript_lintegral_const_mul μ _ _ hf.ennreal_ofReal,
    manuscript_lintegral_const_mul μ _ (fun x => ENNReal.ofReal (-f x)) hf.neg.ennreal_ofReal]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]
  ring

theorem manuscript_real_integral_mul (c : ℝ) (f : Ω → ℝ)
    (hf : Measurable f) (hfi : Integrable f μ) :
    (∫ x, c*f x ∂μ) = c * ∫ x, f x ∂μ := by
  by_cases hc : 0 ≤ c
  · exact manuscript_real_integral_nonneg_mul μ c hc f hf hfi
  · have heq : (fun x => c*f x) = fun x => -((-c)*f x) := by funext x; ring
    rw [heq, manuscript_real_integral_neg μ _ (hfi.const_mul (-c)),
      manuscript_real_integral_nonneg_mul μ (-c) (by linarith) f hf hfi]
    ring

theorem manuscript_real_integral_linear (c d : ℝ) (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hfi : Integrable f μ) (hgi : Integrable g μ) :
    (∫ x, c*f x+d*g x ∂μ) = c*(∫ x, f x ∂μ) + d*(∫ x, g x ∂μ) := by
  rw [manuscript_real_integral_add μ _ _ (hf.const_mul c) (hg.const_mul d)
      (hfi.const_mul c) (hgi.const_mul d),
    manuscript_real_integral_mul μ c f hf hfi, manuscript_real_integral_mul μ d g hg hgi]

theorem manuscript_real_integral_sub (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hfi : Integrable f μ) (hgi : Integrable g μ) :
    (∫ x, f x-g x ∂μ) = (∫ x, f x ∂μ) - ∫ x, g x ∂μ := by
  simp only [sub_eq_add_neg]
  rw [manuscript_real_integral_add μ f (fun x => -g x) hf hg.neg hfi hgi.neg,
    manuscript_real_integral_neg μ g hgi]

end Asakura
