import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import FourierCovariance

/-! The conditionally convergent sine series printed in app2:145--155.
Partial sums, rather than HasSum, are required for this non-absolute series. -/
open Filter Finset Set Complex
open scoped Topology
namespace Asakura

/-- Dirichlet convergence and Abel's limit determine the boundary log series. -/
theorem manuscript_log_boundary (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1)
    (hslit : 1-z ∈ Complex.slitPlane) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, z^n / (n : ℂ)) atTop (𝓝 (-Complex.log (1-z))) := by
  have hb : ∀ N, ‖∑ n ∈ Finset.range N, z^(n+1)‖ ≤ 2 / ‖z-1‖ := by
    intro N
    have heq : (∑ n ∈ Finset.range N, z^(n+1)) = z * ∑ n ∈ Finset.range N, z^n := by
      simp_rw [pow_succ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn; ring
    rw [heq, norm_mul, hz, one_mul, geom_sum_eq hz1, norm_div]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    have hn := norm_sub_le (z^N) 1
    simpa only [norm_pow,hz,one_pow,norm_one,one_add_one_eq_two] using hn
  have hanti : Antitone (fun n : ℕ => 1 / ((n:ℝ)+1)) := by
    intro n m hnm
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hc := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded
    tendsto_one_div_add_atTop_nhds_zero_nat hb
  obtain ⟨L,hL⟩ := cauchySeq_tendsto_of_complete hc
  have hshift : Tendsto (fun N => ∑ n ∈ Finset.range N, z^(n+1) / ((n:ℂ)+1)) atTop (𝓝 L) := by
    convert hL using 1
    funext N
    apply Finset.sum_congr rfl
    intro n hn
    simp [Complex.real_smul, div_eq_mul_inv, mul_comm]
  have hL0 : Tendsto (fun N => ∑ n ∈ Finset.range N, z^n / (n:ℂ)) atTop (𝓝 L) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have heq : ∀ N, (∑ n ∈ Finset.range (N+1), z^n / (n:ℂ)) =
        ∑ n ∈ Finset.range N, z^(n+1) / ((n:ℂ)+1) := by
      intro N
      rw [Finset.sum_range_succ']
      simp
    simpa only [heq] using hshift
  have hAbel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hL0
  rw [tendsto_map'_iff] at hAbel
  have harg : Tendsto (fun r : ℝ => 1-(r:ℂ)*z) (𝓝[<] 1) (𝓝 (1-z)) := by
    have hr : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[<] 1) (𝓝 (1 : ℂ)) := by
      simpa using (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds (x := (1:ℂ))).sub (hr.mul_const z)
  have hlog := ((continuousAt_clog hslit).tendsto.comp harg).neg
  have hevent : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r ∧ r < 1 := by
    have hpos : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r :=
      nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))
    exact Filter.Eventually.and hpos self_mem_nhdsWithin
  have heq : ∀ᶠ r : ℝ in 𝓝[<] 1,
      (∑' n : ℕ, z^n / (n:ℂ) * (r:ℂ)^n) = -Complex.log (1-(r:ℂ)*z) := by
    filter_upwards [hevent] with r hr
    have hnorm : ‖(r:ℂ)*z‖ < 1 := by simp [norm_mul,hz,Complex.norm_real,abs_of_pos hr.1,hr.2]
    have ht := (Complex.hasSum_taylorSeries_neg_log hnorm).tsum_eq
    convert ht using 1
    apply tsum_congr
    intro n
    rw [mul_pow]
    ring
  have hlog' := hlog.congr' (Filter.EventuallyEq.symm heq)
  have hsame : L = -Complex.log (1-z) := tendsto_nhds_unique hAbel hlog'
  rwa [hsame] at hL0

/-- Argument computation for the boundary logarithm; the endpoint pi is excluded. -/
theorem manuscript_arg_one_add_exp (θ : ℝ) (h0 : 0 ≤ θ) (hπ : θ < Real.pi) :
    (1 + Complex.exp ((θ:ℂ)*I)).arg = θ/2 ∧
      1 + Complex.exp ((θ:ℂ)*I) ∈ Complex.slitPlane := by
  have hc : 0 < Real.cos (θ/2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],by linarith⟩
  have heq : 1 + Complex.exp ((θ:ℂ)*I) =
      ((2*Real.cos (θ/2):ℝ):ℂ) * (Complex.cos ((θ/2:ℝ):ℂ) + Complex.sin ((θ/2:ℝ):ℂ)*I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    apply Complex.ext <;> simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re,
      Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.add_im,
      Complex.one_im,Complex.mul_im, mul_zero,zero_mul,add_zero,zero_add,sub_zero,mul_one]
    · have h := Real.cos_two_mul (θ/2)
      rw [show 2*(θ/2)=θ by ring] at h
      nlinarith
    · have h := Real.sin_two_mul (θ/2)
      rw [show 2*(θ/2)=θ by ring] at h
      nlinarith
  constructor
  · rw [heq]
    exact Complex.arg_mul_cos_add_sin_mul_I (by positivity) ⟨by linarith [Real.pi_pos],by linarith⟩
  · apply Complex.mem_slitPlane_iff.mpr
    left
    rw [heq, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.add_re,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
    positivity

/-- app2:151: the ramp sine expansion as convergence of ordered partial sums. -/
theorem manuscript_ramp_sine (t : ℝ) (ht : t ∈ Set.Ico 0 1) :
    Tendsto (fun N => -2 * ∑ n ∈ Finset.range N,
      (-1:ℝ)^n * Real.sin (Real.pi*n*t) / (Real.pi*n)) atTop (𝓝 t) := by
  let θ := Real.pi*t
  let z := -Complex.exp ((θ:ℂ)*I)
  have hθ0 : 0 ≤ θ := mul_nonneg Real.pi_pos.le ht.1
  have hθπ : θ < Real.pi := by dsimp [θ]; nlinarith [Real.pi_pos,ht.2]
  have ha := manuscript_arg_one_add_exp θ hθ0 hθπ
  have hz : ‖z‖ = 1 := by simp [z,Complex.norm_exp]
  have hslit : 1-z ∈ Complex.slitPlane := by simpa [z] using ha.2
  have hz1 : z ≠ 1 := by
    intro he
    have := Complex.slitPlane_ne_zero hslit
    exact this (by rw [he]; ring)
  have h := (Complex.continuous_im.tendsto _).comp (manuscript_log_boundary z hz hz1 hslit)
  have him : ∀ n : ℕ, (z^n/(n:ℂ)).im = (-1:ℝ)^n * Real.sin (Real.pi*n*t) / n := by
    intro n
    have hp : z^n = ((-1:ℂ)^n) * Complex.exp (((Real.pi*n*t:ℝ):ℂ)*I) := by
      dsimp [z,θ]
      rw [neg_eq_neg_one_mul,mul_pow,← Complex.exp_nat_mul]
      congr 2
      push_cast
      ring
    rw [hp]
    have hn : (n:ℂ) = ((n:ℝ):ℂ) := by simp
    rw [hn,Complex.div_ofReal_im,Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]
    have hn' : (-1:ℂ)^n = (((-1:ℝ)^n:ℝ):ℂ) := by simp
    rw [hn']
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.add_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,mul_one,add_zero,zero_add]
  have hs : Tendsto (fun N => ∑ n ∈ Finset.range N,
      (-1:ℝ)^n * Real.sin (Real.pi*n*t) / n) atTop (𝓝 (-θ/2)) := by
    convert h using 1
    · funext N
      simp only [Function.comp_apply]
      induction N with
      | zero => simp
      | succ N ih => rw [Finset.sum_range_succ,Finset.sum_range_succ,Complex.add_im,← ih,him]
    · simp only [Complex.neg_im,Complex.log_im]
      congr 1
      dsimp [z]
      rw [sub_neg_eq_add]
      rw [ha.1]; ring
  convert hs.const_mul (-2/Real.pi) using 1
  · funext N
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  · dsimp [θ]
    field_simp

/-- Verification of the first displayed expansion. The manuscript leaves the
Fourier convergence calculation implicit; here cosine Fourier sums and the
conditional ramp sum supply that calculation. -/
theorem manuscript_min_sine (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Ico 0 1) :
    Tendsto (fun N => 2 * ∑ n ∈ Finset.range N,
      (Real.sin (Real.pi*n*s)/(Real.pi^2*(n:ℝ)^2) - s*(-1:ℝ)^n/(Real.pi*n)) *
        Real.sin (Real.pi*n*t)) atTop (𝓝 (min s t)) := by
  have habs : |t-s|/2 ∈ Set.Icc 0 1 := by
    constructor
    · positivity
    · have hb : |t-s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.2,ht.1],by linarith [hs.1,ht.2]⟩
      linarith
  have h₁ := cosine_series (|t-s|/2) habs
  have h₂ := cosine_series ((t+s)/2) (by constructor <;> linarith [hs.1,hs.2,ht.1,ht.2])
  have h := ((h₁.sub h₂).div_const (Real.pi^2)).tendsto_sum_nat.add
    ((manuscript_ramp_sine t ht).const_mul s)
  convert h using 1
  · funext N
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hcos : Real.cos (2*Real.pi*n*(|t-s|/2)) =
        Real.cos (Real.pi*n*s-Real.pi*n*t) := by
      by_cases hst : s ≤ t
      · rw [abs_of_nonneg (sub_nonneg.mpr hst),show 2*Real.pi*(n:ℝ)*((t-s)/2) =
          -(Real.pi*n*s-Real.pi*n*t) by ring,Real.cos_neg]
      · rw [abs_of_neg (by linarith),show 2*Real.pi*(n:ℝ)*(-(t-s)/2) =
          Real.pi*n*s-Real.pi*n*t by ring]
    rw [hcos,show 2*Real.pi*(n:ℝ)*((t+s)/2)=Real.pi*n*s+Real.pi*n*t by ring,
      ← mul_sub, ← Real.two_mul_sin_mul_sin]
    ring
  · congr 1
    field_simp [Real.pi_ne_zero]
    by_cases hst : s ≤ t
    · rw [min_eq_left hst,abs_of_nonneg (sub_nonneg.mpr hst)]; ring
    · rw [min_eq_right (le_of_not_ge hst),abs_of_neg (by linarith)]; ring

/-- app2:153--157: subtract s times the ramp expansion at each finite N,
then pass to the limit. This is the manuscript's cancellation step. -/
theorem manuscript_sine_cancellation (s t : ℝ) (hs : s ∈ Set.Icc 0 1)
    (ht : t ∈ Set.Ico 0 1) :
    Tendsto (fun N => 2 * ∑ n ∈ Finset.range N,
      Real.sin (Real.pi*n*s)*Real.sin (Real.pi*n*t)/(Real.pi^2*(n:ℝ)^2))
      atTop (𝓝 (min s t-s*t)) := by
  have h := (manuscript_min_sine s t hs ht).sub ((manuscript_ramp_sine t ht).const_mul s)
  convert h using 1
  funext N
  simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Absolute convergence of the remaining 1/n^2 series, including t=1. -/
theorem manuscript_sine_covariance (s t : ℝ) (hs : s ∈ Set.Icc 0 1)
    (ht : t ∈ Set.Icc 0 1) :
    HasSum (fun n : ℕ => 2*Real.sin (Real.pi*n*s)*Real.sin (Real.pi*n*t) /
      (Real.pi^2*(n:ℝ)^2)) (min s t-s*t) := by
  let a : ℕ → ℝ := fun n => 2*Real.sin (Real.pi*n*s)*Real.sin (Real.pi*n*t) /
    (Real.pi^2*(n:ℝ)^2)
  have ha : Summable a := by
    apply (hasSum_zeta_two.summable.mul_left (2/Real.pi^2)).of_norm_bounded
    intro n
    dsimp [a]
    rw [abs_div,abs_mul,abs_mul,abs_of_nonneg (by positivity : (0:ℝ) ≤ 2),
      abs_of_nonneg (by positivity : 0 ≤ Real.pi^2*(n:ℝ)^2)]
    calc
      _ ≤ 2*1*1/(Real.pi^2*(n:ℝ)^2) := by
        gcongr <;> exact Real.abs_sin_le_one _
      _ = _ := by ring
  apply ha.hasSum_iff_tendsto_nat.mpr
  rcases lt_or_eq_of_le ht.2 with ht1 | rfl
  · simpa only [a,Finset.mul_sum,mul_div_assoc,mul_assoc] using
      manuscript_sine_cancellation s t hs ⟨ht.1,ht1⟩
  · have hz : a = 0 := by
      funext n
      simp [a,mul_comm Real.pi (n:ℝ),Real.sin_nat_mul_pi]
    rw [hz]
    simpa [min_eq_left hs.2] using (tendsto_const_nhds (x := (0:ℝ)) (f := atTop))

end Asakura
