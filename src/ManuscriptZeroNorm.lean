import ManuscriptMeasure
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace Asakura

/-- app1:43--59: the sets {h >= 1/(n+1)}, an integral lower bound, and their union. -/
theorem manuscript_nonnegative_zero_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → ℝ) (hm : Measurable h) (hpos : ∀ x, 0 ≤ h x)
    (hzero : (∫⁻ x, ENNReal.ofReal (h x) ∂μ) = 0) : h =ᵐ[μ] 0 := by
  let A : ℕ → Set Ω := fun n => {x | 1 / ((n:ℝ)+1) ≤ h x}
  have hAm : ∀ n, MeasurableSet (A n) := fun n => measurableSet_le measurable_const hm
  have hAz : ∀ n, μ (A n) = 0 := by
    intro n
    let c : ℝ≥0∞ := ENNReal.ofReal (1 / ((n:ℝ)+1))
    have hc : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
    have hb : c * μ (A n) ≤ ∫⁻ x, ENNReal.ofReal (h x) ∂μ := by
      have heq : (∫⁻ x, (A n).indicator (fun _ => c) x ∂μ) = c * μ (A n) := by
        rw [lintegral_indicator (hAm n)]
        simp
      rw [← heq]
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ A n
      · simp only [Set.indicator_of_mem hx]
        exact ENNReal.ofReal_le_ofReal hx
      · simp [Set.indicator_of_notMem hx]
    rw [hzero] at hb
    exact (mul_eq_zero.mp (le_antisymm hb zero_le)).resolve_left hc
  have hcover : {x | h x ≠ 0} ⊆ ⋃ n, A n := by
    intro x hx
    have hxp : 0 < h x := lt_of_le_of_ne (hpos x) (Ne.symm hx)
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt hxp
    exact Set.mem_iUnion.mpr ⟨n,hn.le⟩
  have hz : μ {x | h x ≠ 0} = 0 := measure_mono_null hcover (measure_iUnion_null hAz)
  exact ae_iff.mpr hz

/-- Its application to |f-g|^p, the finite-p zero-norm argument. -/
theorem manuscript_zero_norm_finite {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) (f g : Ω → E) (hf : Measurable f) (hg : Measurable g)
    (p : ℝ) (hp : 0 < p)
    (hzero : (∫⁻ x, ENNReal.ofReal (‖f x-g x‖ ^ p) ∂μ) = 0) : f =ᵐ[μ] g := by
  have hz := manuscript_nonnegative_zero_integral μ (fun x => ‖f x-g x‖^p)
    (((hf.sub hg).norm).pow_const p) (fun x => Real.rpow_nonneg (norm_nonneg _) _) hzero
  filter_upwards [hz] with x hx
  have hn : ‖f x-g x‖ = 0 := by
    by_contra hn
    have ht := Real.rpow_pos_of_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)) p
    change ‖f x-g x‖^p = 0 at hx
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end Asakura
