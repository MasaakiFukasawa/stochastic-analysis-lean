import ManuscriptInequalities
import ManuscriptZeroNorm
import ManuscriptLinearity
open MeasureTheory Filter
open scoped ENNReal Topology
namespace Asakura

/-- Pointwise norm triangle inequality followed by the manuscript's scalar Minkowski proof. -/
theorem manuscript_minkowski_finite {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) (f g : Ω → E)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (p : ℝ≥0∞) (hp : p ≠ ⊤) (hp1 : 1 ≤ p) :
    eLpNorm (fun x => f x+g x) p μ ≤ eLpNorm f p μ + eLpNorm g p μ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp1)
  have hpr : 1 ≤ p.toReal := by exact_mod_cast (ENNReal.toReal_mono hp hp1)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (f := fun x => f x+g x) (hf.add hg),
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hg]
  apply le_trans _ (manuscript_lintegral_Lp_add_le hf.enorm hg.enorm hpr)
  apply ENNReal.rpow_le_rpow _ (by positivity)
  exact lintegral_mono (fun x => ENNReal.rpow_le_rpow (enorm_add_le _ _) (by positivity))

/-- Young normalization applied to the norms, for 1 < p,q < infinity. -/
theorem manuscript_holder_finite {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (p q : ℝ) (hpq : p.HolderConjugate q) :
    eLpNorm (fun x => f x*g x) 1 μ ≤
      eLpNorm f (ENNReal.ofReal p) μ * eLpNorm g (ENNReal.ofReal q) μ := by
  rw [eLpNorm_one_eq_lintegral_enorm (f := fun x => f x*g x) (hf.mul hg),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hpq.pos) ENNReal.ofReal_ne_top hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos) ENNReal.ofReal_ne_top hg]
  simp only [enorm_mul,ENNReal.toReal_ofReal hpq.pos.le,ENNReal.toReal_ofReal hpq.symm.pos.le]
  exact manuscript_lintegral_mul_le_Lp_mul_Lq μ hpq hf.enorm hg.enorm

/-- The endpoint uses the a.e. essential-supremum bound directly. -/
theorem manuscript_holder_one_infty {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x => f x*g x) 1 μ ≤ eLpNorm f 1 μ * eLpNorm g ⊤ μ := by
  rw [eLpNorm_one_eq_lintegral_enorm (f := fun x => f x*g x) (hf.mul hg),eLpNorm_one_eq_lintegral_enorm hf,
    eLpNorm_exponent_top hg]
  calc
    (∫⁻ x, ‖f x*g x‖ₑ ∂μ) ≤ ∫⁻ x, ‖f x‖ₑ * eLpNormEssSup g μ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_le_eLpNormEssSup (μ := μ) (f := g)] with x hx
      rw [enorm_mul]
      exact mul_le_mul_right hx _
    _ = (∫⁻ x, ‖f x‖ₑ ∂μ) * eLpNormEssSup g μ := lintegral_mul_const'' _ hf.enorm

/-- The infinite-p triangle inequality is an a.e. bound, without a limiting p argument. -/
theorem manuscript_minkowski_infty {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) (f g : Ω → E)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x => f x+g x) ⊤ μ ≤ eLpNorm f ⊤ μ + eLpNorm g ⊤ μ := by
  rw [eLpNorm_exponent_top (f := fun x => f x+g x) (hf.add hg),eLpNorm_exponent_top hf,eLpNorm_exponent_top hg]
  refine essSup_le_of_ae_le _ ?_
  filter_upwards [ae_le_eLpNormEssSup (μ := μ) (f := f),ae_le_eLpNormEssSup (μ := μ) (f := g)] with x hx hy
  exact (enorm_add_le _ _).trans (add_le_add hx hy)

/-- Bridge from the actual Lp seminorm to the threshold-set proof in app1. -/
theorem manuscript_lp_zero_finite {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) (f g : Ω → E) (hf : Measurable f) (hg : Measurable g)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (hz : eLpNorm (fun x => f x-g x) p μ = 0) : f =ᵐ[μ] g := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (f := fun x => f x-g x) (hf.sub hg).aestronglyMeasurable] at hz
  have hi : (∫⁻ x, ‖f x-g x‖ₑ ^ p.toReal ∂μ) = 0 := by
    rcases ENNReal.rpow_eq_zero_iff.mp hz with h | h
    · exact h.1
    · have : 0 < 1/p.toReal := by positivity
      linarith [h.2]
  apply manuscript_zero_norm_finite μ f g hf hg p.toReal hpr
  simpa only [← ofReal_norm,ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpr.le] using hi

/-- Zero essential supremum forces the norm to vanish off a null set. -/
theorem manuscript_lp_zero_infty {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) (f g : Ω → E)
    (hm : AEStronglyMeasurable (fun x => f x-g x) μ)
    (hz : eLpNorm (fun x => f x-g x) ⊤ μ = 0) : f =ᵐ[μ] g := by
  rw [eLpNorm_exponent_top hm] at hz
  filter_upwards [ae_le_eLpNormEssSup (μ := μ) (f := fun x => f x-g x)] with x hx
  rw [hz] at hx
  exact sub_eq_zero.mp (enorm_eq_zero.mp (le_antisymm hx zero_le))

/-- All p >= 1, using the separate endpoint proofs above. -/
theorem manuscript_minkowski {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) (f g : Ω → E) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    eLpNorm (f+g) p μ ≤ eLpNorm f p μ+eLpNorm g p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · by_cases hg : AEStronglyMeasurable g μ
    · by_cases ht : p = ⊤
      · subst p; exact manuscript_minkowski_infty μ f g hf hg
      · exact manuscript_minkowski_finite μ f g hf hg p ht hp
    · simp [eLpNorm_of_not_aestronglyMeasurable hg]
  · simp [eLpNorm_of_not_aestronglyMeasurable hf]

/-- Finite sums used before Fatou in the completeness proof. -/
theorem manuscript_eLpNorm'_sum {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) (s : Finset ι) (f : ι → Ω → E)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm' (∑ i ∈ s, f i) p μ ≤ ∑ i ∈ s, eLpNorm' (f i) p μ := by
  classical
  have hadd : ∀ u v : Ω → E, AEStronglyMeasurable u μ → AEStronglyMeasurable v μ →
      eLpNorm' (u+v) p μ ≤ eLpNorm' u p μ+eLpNorm' v p μ := by
    intro u v hu hv
    simp only [eLpNorm'_eq_lintegral_enorm]
    apply le_trans _ (manuscript_lintegral_Lp_add_le hu.enorm hv.enorm hp)
    apply ENNReal.rpow_le_rpow _ (by positivity)
    exact lintegral_mono (fun x => ENNReal.rpow_le_rpow (enorm_add_le _ _) (by linarith))
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact le_of_eq (eLpNorm'_zero (by linarith : 0 < p))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    apply (hadd _ _ (hf i (Finset.mem_insert_self _ _))
      (Finset.aestronglyMeasurable_sum s (fun j hj => hf j (Finset.mem_insert_of_mem hj)))).trans
    exact add_le_add le_rfl (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

end Asakura
