import Chapter12FiniteHolderMoment

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000

theorem finite_holder_moment_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (m : ℕ) (hm : 0<m) (f : Fin m → Ω → ℝ)
    (hf : ∀ j,Measurable (f j)) (hn : ∀ j x,0≤f j x)
    (hi : ∀ j,Integrable (fun x => f j x^m) P)
    (hprod : Integrable (fun x => ∏ j,f j x) P) :
    (∫ x,∏ j,f j x ∂P)≤∏ j,(∫ x,f j x^m ∂P)^((m:ℝ)⁻¹) := by
  have hh := finite_holder_moment_lintegral P m hm f hf hn
  have hp : (∫⁻ x,ENNReal.ofReal (∏ j,f j x) ∂P)=ENNReal.ofReal (∫ x,∏ j,f j x ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hprod (ae_of_all P (fun x => Finset.prod_nonneg (fun j _ => hn j x)))).symm
  have hj (j : Fin m) : (∫⁻ x,ENNReal.ofReal (f j x)^m ∂P)=ENNReal.ofReal (∫ x,f j x^m ∂P) := by
    simp_rw [← ENNReal.ofReal_pow (hn j _) ]
    exact (ofReal_integral_eq_lintegral_ofReal (hi j) (ae_of_all P (fun x => pow_nonneg (hn j x) m))).symm
  rw [hp] at hh
  simp_rw [hj] at hh
  have hfin : (∏ j,ENNReal.ofReal (∫ x,f j x^m ∂P)^((m:ℝ)⁻¹))≠⊤ := by
    apply ENNReal.prod_ne_top
    intro j _
    exact ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono hfin hh
  simpa only [ENNReal.toReal_prod,← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (integral_nonneg (fun x => pow_nonneg (hn _ x) m)),
    ENNReal.toReal_ofReal (integral_nonneg (fun x => Finset.prod_nonneg (fun j _ => hn j x)))] using hreal

/-- Hölder's exact step for the norms of the actual Gaussian coordinate
arrays appearing in a terminal contraction. -/
theorem gaussian_array_holder {n m : ℕ} (hm : 0<m)
    {I : Fin m → Type*} [∀ j,Fintype (I j)]
    (f : ∀ j,I j → GaussianJet n) :
    (∫ x,∏ j,gaussianArrayNorm (f j) x ∂Measure.pi fun _ => gaussianReal 0 1)≤
      ∏ j,(∫ x,gaussianArrayNorm (f j) x^m ∂Measure.pi fun _ => gaussianReal 0 1)^((m:ℝ)⁻¹) := by
  apply finite_holder_moment_integral _ m hm
    (fun j => gaussianArrayNorm (f j))
    (fun j => (gaussianArrayNorm_continuous _).measurable)
    (fun j => gaussianArrayNorm_nonneg _)
  · intro j
    exact memLp_one_iff_integrable.mp (polynomial_growth_gaussian_memLp
      ((gaussianArrayNorm_continuous _).pow m).measurable
      (polynomial_growth_pow (gaussianArrayNorm_growth _) m) 1 (by simp))
  · have hm' : Measurable (fun x => ∏ j,gaussianArrayNorm (f j) x) :=
      Finset.measurable_prod _ (fun j _ => (gaussianArrayNorm_continuous _).measurable)
    have hg := polynomial_growth_finset_prod Finset.univ (fun j => gaussianArrayNorm (f j))
      (fun j _ => gaussianArrayNorm_growth _)
    exact memLp_one_iff_integrable.mp (polynomial_growth_gaussian_memLp hm' hg 1 (by simp))

end Asakura.Chapter12
