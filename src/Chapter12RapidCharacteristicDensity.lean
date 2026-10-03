import Chapter12CharacteristicContinuity
import Chapter12CharacteristicInverseSmooth
import Chapter12GaussianMixtureWeakLimit
import Chapter12GaussianDampedFourierLimit

open MeasureTheory Filter Real
open scoped Topology ContDiff RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

/-- The final analytic part of the smooth-density proof, including the
identification with the original law by Gaussian convolution. -/
theorem rapid_characteristic_density {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (hd : ∀ k : ℕ,∃ A : ℝ,0≤A ∧ ∀ ξ : E,
      ‖∫ y,Complex.exp (Complex.I*(inner ℝ ξ y:ℂ)) ∂μ‖≤A/(1+‖ξ‖)^k) :
    ∃ p : E → ℝ,ContDiff ℝ ∞ p ∧ (∀ x,0≤p x) ∧
      μ=volume.withDensity (fun x => ENNReal.ofReal (p x)) ∧
      ∀ x,p x=(((2*π)^Module.finrank ℝ E:ℂ)⁻¹*
        ∫ ξ,Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*
          (∫ y,Complex.exp (Complex.I*(inner ℝ ξ y:ℂ)) ∂μ)).re := by
  let φ : E → ℂ := fun ξ => ∫ y,Complex.exp (Complex.I*(inner ℝ ξ y:ℂ)) ∂μ
  have hm : AEStronglyMeasurable φ volume := (characteristic_integral_continuous μ).aestronglyMeasurable
  have hi : Integrable φ volume := (integrable_norm_iff hm).mp (by
    simpa using rapid_decay_polynomial_integrable volume φ hm hd 0)
  let Z : ℂ := ((2*π)^Module.finrank ℝ E:ℂ)⁻¹
  let p : E → ℝ := fun x => (Z*(∫ ξ,Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*φ ξ)).re
  have hp : ContDiff ℝ ∞ p :=
    Complex.reCLM.contDiff.comp (contDiff_const.mul (characteristic_inverse_smooth φ hm hd))
  let r : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hr (n) : 0<r n := by dsimp [r]; positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let ε : ℕ → ℝ := fun n => 2*(r n)^2
  have hε (n) : 0≤ε n := by dsimp [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    simpa using (hr0.pow 2).const_mul 2
  let pn : ℕ → E → ℝ := fun n x => ∫ y,normalizedGaussianKernel (1/(4*(r n)^2)) (x-y) ∂μ
  have hpn (n) := normalized_gaussian_kernel_properties (E := E) (1/(4*(r n)^2))
    (by have := hr n; positivity)
  have hmix (n) := real_mixture_density μ volume _ (hpn n).1
    (fun x => ((hpn n).2.1 x).le) _ (hpn n).2.2.1
  have hpf (n) (x : E) : (pn n x:ℂ)=Z*
      ∫ ξ,Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*φ ξ*
        (Real.exp (-ε n*‖ξ‖^2/2):ℂ) := by
    have hh := gaussian_mixture_fourier μ ((r n)^2) (sq_pos_of_pos (hr n)) x
    change (pn n x:ℂ)=Z*∫ ξ,Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*φ ξ*
      (Real.exp (-(r n)^2*‖ξ‖^2):ℂ) at hh
    rw [hh]
    congr 1
    apply integral_congr_ae
    apply ae_of_all
    intro ξ
    have he : -(r n)^2*‖ξ‖^2= -ε n*‖ξ‖^2/2 := by dsimp [ε]; ring
    dsimp only
    rw [he]
  let C : ℝ := ‖Z‖*(∫ ξ,‖φ ξ‖)
  have hC : 0≤C := mul_nonneg (norm_nonneg _) (integral_nonneg (fun ξ => norm_nonneg _))
  have hbound (n) (x : E) : pn n x≤C := by
    have hh := (gaussian_damped_fourier_limit volume φ hi ε hε hε0 x).1 n
    have he : ‖(pn n x:ℂ)‖=pn n x := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ((hmix n).2.2.1 x)]
    rw [← he,hpf,norm_mul]
    exact mul_le_mul_of_nonneg_left hh (norm_nonneg Z)
  have hlim (x : E) : Tendsto (fun n => pn n x) atTop (𝓝 (p x)) := by
    have hh := (gaussian_damped_fourier_limit volume φ hi ε hε hε0 x).2
    have hc := Complex.continuous_re.continuousAt.tendsto.comp (hh.const_mul Z)
    have he (n) : (Z*∫ ξ,Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*φ ξ*
      (Real.exp (-ε n*‖ξ‖^2/2):ℂ)).re=pn n x := by rw [← hpf]; rfl
    simpa only [Function.comp_def,he] using hc
  have hfinal := density_of_bounded_approximations volume μ p pn hp.continuous
    (fun n => (hmix n).2.1.measurable) (fun n => (hmix n).2.2.1)
    C hC hbound hlim (fun f => gaussian_mixture_weak_limit μ r hr hr0 f)
  exact ⟨p,hp,hfinal.1,hfinal.2,fun x => rfl⟩

end Asakura.Chapter12
