import Chapter9ReverseGaussianChangeVariables
import Chapter9ReverseApproximation
import Chapter9GaussianMixture

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace Asakura.Chapter9
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

 theorem reverse_gaussian_change_variables_coordinates {d : ℕ} (h : ℝ) (hh : 0<h)
    (x : Fin d → ℝ) (q : (Fin d → ℝ) → ℝ) (hq : Continuous q) :
    (∫ y,q y*gaussianKernel (Real.exp (-h)) (1-Real.exp (-2*h)) y x)=
      Real.exp ((d:ℝ)*h)*∫ ξ : Fin d → ℝ,
        q (Real.exp h • (x-Real.sqrt (1-Real.exp (-2*h)) • ξ))
        ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  have he := reverse_gaussian_change_variables h hh x q hq
  rw [←map_pi_eq_stdGaussian,integral_map (WithLp.measurable_toLp 2 _).aemeasurable
    (by apply Continuous.aestronglyMeasurable; fun_prop)] at he
  exact he

/-- The actual reverse transition tends to the identity at its lower time
endpoint. The density is the actual OU mixture and the test is compactly
supported; the required bound is derived on a compact time-space set. -/
theorem reverse_kernel_lower_endpoint {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0<τ) (x : Fin d → ℝ)
    (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    let p := fun z => ∫ z0,Real.exp (ouExponent z0 z) ∂μ
    Tendsto (fun h => (∫ y,f y*p (τ-h,y)*
      gaussianKernel (Real.exp (-h)) (1-Real.exp (-2*h)) y x)/p (τ,x))
      (𝓝[>] (0:ℝ)) (𝓝 (f x)) := by
  let p := fun z => ∫ z0,Real.exp (ouExponent z0 z) ∂μ
  let q := fun h y => f y*p (τ-h,y)
  let U : Set (ℝ × (Fin d → ℝ)) := {z | z.1<τ}
  have hqc : ContinuousOn q.uncurry U :=
    (hf.comp continuous_snd).continuousOn.mul
      ((ou_gaussian_mixture_smooth μ).continuousOn.comp
        (show ContinuousOn (fun z : ℝ × (Fin d → ℝ) => (τ-z.1,z.2)) U from by fun_prop)
        (fun z hz => by change 0<τ-z.1; exact sub_pos.mpr hz))
  have hqch h (hh : h<τ) : Continuous (q h) :=
    hqc.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => hh)
  let S : Set (ℝ × (Fin d → ℝ)) := Icc 0 (τ/2) ×ˢ tsupport f
  have hS : IsCompact S := isCompact_Icc.prod hfc.isCompact
  have hSU : S⊆U := by intro z hz; change z.1<τ; linarith [hz.1.2]
  obtain ⟨M,hM⟩ := hS.bddAbove_image (hqc.norm.mono hSU)
  have hbound h (hh : h∈Ioo 0 (τ/2)) y : ‖q h y‖≤max M 0 := by
    by_cases hy : y∈tsupport f
    · exact (hM (mem_image_of_mem _ (show (h,y)∈S from ⟨⟨hh.1.le,hh.2.le⟩,hy⟩))).trans (le_max_left _ _)
    · have hz := image_eq_zero_of_notMem_tsupport hy
      simpa only [q,hz,zero_mul,norm_zero] using le_max_right M (0:ℝ)
  have hq0 : ContinuousAt q.uncurry (0,x) := hqc.continuousAt
    ((isOpen_lt continuous_fst continuous_const).mem_nhds hτ)
  have hlim := reverse_gaussian_approximation
    (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) q x d (τ/2) (by linarith) hq0
    (fun h hh => ((hqch h (by linarith [hh.2])).comp (by fun_prop)).aestronglyMeasurable)
    (max M 0) hbound
  have hsmall : ∀ᶠ h in 𝓝[>] (0:ℝ),h∈Ioo 0 (τ/2) := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds (show 0<τ/2 by linarith))] with h hh hδ
    exact ⟨hh,hδ⟩
  have he : (fun h => ∫ y,q h y*gaussianKernel (Real.exp (-h)) (1-Real.exp (-2*h)) y x) =ᶠ[𝓝[>] (0:ℝ)]
      (fun h => Real.exp ((d:ℝ)*h)*∫ ξ : Fin d → ℝ,q h (Real.exp h • (x-Real.sqrt (1-Real.exp (-2*h)) • ξ))
        ∂Measure.pi (fun _ => gaussianReal 0 1)) := by
    filter_upwards [hsmall] with h hh
    exact reverse_gaussian_change_variables_coordinates h hh.1 x (q h) (hqch h (by linarith [hh.2]))
  have hp : 0<p (τ,x) := (gaussian_mixture_positive μ (Real.exp (-τ))
    ⟨1-Real.exp (-2*τ),(ou_variance_positive τ hτ).le⟩ (by
      apply ne_of_gt; exact_mod_cast ou_variance_positive τ hτ) x).2
  have hh := (hlim.congr' he.symm).div_const (p (τ,x))
  simpa only [q,sub_zero,mul_div_cancel_right₀ _ hp.ne'] using hh
end Asakura.Chapter9
