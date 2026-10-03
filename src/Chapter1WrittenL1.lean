import Chapter1WrittenJensen
import Chapter1WrittenReverse

/- thm:l1conv: precisely X_m = X 1_{|X|≤m}, then the three-term estimate.
The forward/reverse L2 inputs below are the original convex-tail proofs. -/
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter1Written
variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

theorem abs_convex_written : ConvexOn ℝ univ (fun x : ℝ => |x|) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  change |a*x+b*y| ≤ a*|x|+b*|y|
  calc
    _ ≤ |a*x|+|b*y| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

/-- The Jensen-based L1 contraction used at the start of thm:l1conv. -/
theorem written_L1_contraction {G : MeasurableSpace Ω} (hG : G ≤ m)
    {X : Ω → ℝ} (hX : Integrable X P) :
    eLpNorm P[X | G] 1 P ≤ eLpNorm X 1 P := by
  have hJ := conditional_jensen_written hG abs_convex_written hX hX.abs
  have hI : ∫ ω, |P[X | G] ω| ∂P ≤ ∫ ω, |X ω| ∂P := by
    calc
      _ ≤ ∫ ω, P[fun ω => |X ω| | G] ω ∂P :=
        integral_mono_ae integrable_condExp.abs integrable_condExp hJ
      _ = _ := integral_condExp hG
  have hnorm (Z : Ω → ℝ) (hZ : Integrable Z P) :
      ENNReal.ofReal (∫ ω, |Z ω| ∂P) = eLpNorm Z 1 P := by
    rw [eLpNorm_one_eq_lintegral_enorm hZ.aestronglyMeasurable]
    simpa only [Real.norm_eq_abs] using ofReal_integral_norm_eq_lintegral_enorm hZ
  rw [← hnorm _ integrable_condExp, ← hnorm _ hX]
  exact ENNReal.ofReal_le_ofReal hI

/-- The cutoff error has exactly the tail integral appearing in the manuscript. -/
theorem written_cutoff_eLpNorm_one {X : Ω → ℝ} (hmX : Measurable[m] X) (hX : Integrable X P) :
    Tendsto (fun n : ℕ => eLpNorm (X - {ω | |X ω| ≤ (n : ℝ)}.indicator X) 1 P)
      atTop (𝓝 0) := by
  have hmabs : Measurable (fun ω => |X ω|) := by simpa only [Real.norm_eq_abs] using hmX.norm
  have he (n : ℕ) : eLpNorm (X - {ω | |X ω| ≤ (n : ℝ)}.indicator X) 1 P =
      ENNReal.ofReal (∫ ω, {ω | (n : ℝ) < |X ω|}.indicator (fun ω => |X ω|) ω ∂P) := by
    have hi : Integrable (X - {ω | |X ω| ≤ (n : ℝ)}.indicator X) P :=
      hX.sub (hX.indicator (measurableSet_le hmabs measurable_const))
    rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm hi]
    congr 1
    apply integral_congr_ae (Eventually.of_forall _)
    intro ω
    by_cases h : |X ω| ≤ (n : ℝ)
    · simp [Set.indicator, h, not_lt.mpr h]
    · simp [Set.indicator, h, lt_of_not_ge h, Real.norm_eq_abs]
  simp_rw [he]
  simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp (cutoff_tail_L1 hmX hX)

/-- The cutoff transfer step is generic; the next theorem supplies its L2 premise
from both original convex-tail proofs, so it is not left as an unproved assumption. -/
theorem written_cutoff_transfer (G : ℕ → MeasurableSpace Ω) (H : MeasurableSpace Ω)
    (hG : ∀ n, G n ≤ m) (hH : H ≤ m)
    (hL2 : ∀ (Z : Ω → ℝ), MemLp Z 2 P →
      Tendsto (fun n => eLpNorm (P[Z | G n]-P[Z | H]) 2 P) atTop (𝓝 0))
    {X : Ω → ℝ} (hmX : Measurable[m] X) (hX : Integrable X P) :
    Tendsto (fun n => eLpNorm (P[X | G n]-P[X | H]) 1 P) atTop (𝓝 0) := by
  letI : MeasurableSpace Ω := m
  have hdist {A B : Ω → ℝ} (hA : Integrable A P) (hB : Integrable B P)
      {K : MeasurableSpace Ω} (hK : K ≤ m) :
      eLpNorm (P[A | K]-P[B | K]) 1 P ≤ eLpNorm (A-B) 1 P := by
    rw [← eLpNorm_congr_ae (condExp_sub hA hB K)]
    exact written_L1_contraction hK (hA.sub hB)
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  let δ := (ε/2)/2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact ENNReal.div_pos (ENNReal.div_pos hε.ne' (by norm_num)).ne' (by norm_num)
  obtain ⟨k, hk⟩ := ((ENNReal.tendsto_nhds_zero.mp (written_cutoff_eLpNorm_one (P := P) hmX hX)) δ hδ).exists
  let Z := {ω | |X ω| ≤ (k : ℝ)}.indicator X
  have hZ2 : MemLp Z 2 P := cutoff_L2 (P := P) hmX k
  have hZ : Integrable Z P := hZ2.integrable (by norm_num)
  have hb := (ENNReal.tendsto_nhds_zero.mp (hL2 Z hZ2)) δ hδ
  filter_upwards [hb] with n hn
  have he : P[X | G n]-P[X | H] =
      ((P[X | G n]-P[Z | G n])+(P[Z | G n]-P[Z | H]))+(P[Z | H]-P[X | H]) := by abel
  calc
    _ ≤ eLpNorm (P[X | G n]-P[Z | G n]) 1 P +
        eLpNorm (P[Z | G n]-P[Z | H]) 1 P + eLpNorm (P[Z | H]-P[X | H]) 1 P := by
      rw [he]
      exact (eLpNorm_add_le le_rfl).trans (add_le_add (eLpNorm_add_le le_rfl) le_rfl)
    _ ≤ δ+δ+δ := by
      apply add_le_add
      · exact add_le_add ((hdist hX hZ (hG n)).trans hk)
          ((eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans hn)
      · rw [eLpNorm_sub_comm]
        exact (hdist hX hZ hH).trans hk
    _ ≤ (δ+δ)+(δ+δ) := add_le_add le_rfl (le_add_right le_rfl)
    _ = ε := by dsimp [δ]; rw [ENNReal.add_halves, ENNReal.add_halves]

/-- Both directions of the manuscript L1 theorem, with its cutoff proof and
both previously checked original L2 arguments. Natural n indexes G_n or G_{-n}. -/
theorem conditional_L1_written (G : ℕ → MeasurableSpace Ω) (hle : ∀ n, G n ≤ m)
    {X : Ω → ℝ} (hmX : Measurable[m] X) (hX : Integrable X P) :
    (Monotone G → Tendsto (fun n => eLpNorm (P[X | G n]-P[X | ⨆ n, G n]) 1 P) atTop (𝓝 0)) ∧
    (Antitone G → Tendsto (fun n => eLpNorm (P[X | G n]-P[X | ⨅ n, G n]) 1 P) atTop (𝓝 0)) := by
  constructor
  · intro hG
    apply written_cutoff_transfer (P := P) G (⨆ n, G n) hle (iSup_le hle) _ hmX hX
    intro Z hZ
    have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp
      (conditional_upward_L2_written G hG hle hZ.toLp)
    apply ht.congr
    intro n
    exact eLpNorm_congr_ae ((hZ.condExpL2_ae_eq_condExp (𝕜 := ℝ) (hle n)).sub
      (hZ.condExpL2_ae_eq_condExp (𝕜 := ℝ) (iSup_le hle)))
  · intro hG
    apply written_cutoff_transfer (P := P) G (⨅ n, G n) hle ((iInf_le G 0).trans (hle 0)) _ hmX hX
    intro Z hZ
    have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp
      (conditional_downward_L2_written G hG hle hZ.toLp)
    apply ht.congr
    intro n
    exact eLpNorm_congr_ae ((hZ.condExpL2_ae_eq_condExp (𝕜 := ℝ) (hle n)).sub
      (hZ.condExpL2_ae_eq_condExp (𝕜 := ℝ) ((iInf_le G 0).trans (hle 0))))

end Asakura.Chapter1Written
