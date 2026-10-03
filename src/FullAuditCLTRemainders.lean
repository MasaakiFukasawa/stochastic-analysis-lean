import FullAuditCLTVariances

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- Integrating and summing the displayed remainder estimate. The random
increments, their actual moments, and the Lindeberg tail integrals are retained. -/
theorem clt_remainder_sum_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X R : ι → Ω → ℝ)
    (hmX : ∀ i, Measurable (X i)) (hX : ∀ i, Integrable (fun ω => X i ω ^ 2) P)
    (hR : ∀ i, Integrable (R i) P) (C₂ C₃ ε : ℝ) (hC₂ : 0 ≤ C₂)
    (hb : ∀ i ω, |R i ω| ≤ C₂ * ((∫ x, X i x ^ 2 ∂P)^2 +
      (∫ x, X i x ^ 2 ∂P) * |X i ω| +
      {ω | ε ≤ |X i ω|}.indicator (fun ω => X i ω ^ 2) ω) + ε*C₃*X i ω ^ 2) :
    ∑ i, ∫ ω, |R i ω| ∂P ≤
      C₂ * (rowMaximum (fun i => ∫ ω, X i ω ^ 2 ∂P) * (∑ i, ∫ ω, X i ω ^ 2 ∂P) +
        rowMaximum (fun i => ∫ ω, |X i ω| ∂P) * (∑ i, ∫ ω, X i ω ^ 2 ∂P) +
        ∑ i, ∫ ω in {ω | ε ≤ |X i ω|}, X i ω ^ 2 ∂P) +
      ε*C₃*(∑ i, ∫ ω, X i ω ^ 2 ∂P) := by
  let v : ι → ℝ := fun i => ∫ ω, X i ω ^ 2 ∂P
  let a : ι → ℝ := fun i => ∫ ω, |X i ω| ∂P
  let t : ι → ℝ := fun i => ∫ ω in {ω | ε ≤ |X i ω|}, X i ω ^ 2 ∂P
  have hv : ∀ i, 0 ≤ v i := fun i => integral_nonneg fun ω => sq_nonneg _
  have ha : ∀ i, Integrable (fun ω => |X i ω|) P := by
    intro i
    have h2 := (memLp_two_iff_integrable_sq (hmX i).aestronglyMeasurable).mpr (hX i)
    exact (h2.integrable (by norm_num)).abs
  have hi : ∀ i, ∫ ω, |R i ω| ∂P ≤ C₂*(v i ^2 + v i*a i+t i)+ε*C₃*v i := by
    intro i
    have hA : MeasurableSet {ω | ε ≤ |X i ω|} := measurableSet_le measurable_const
      (by simpa only [Real.norm_eq_abs] using (hmX i).norm)
    have hconst : Integrable (fun _ : Ω => v i ^ 2) P := integrable_const _
    have hva : Integrable (fun ω => v i * |X i ω|) P := (ha i).const_mul _
    have hind : Integrable ({ω | ε ≤ |X i ω|}.indicator (fun ω => X i ω ^ 2)) P := (hX i).indicator hA
    have hbase : Integrable (fun ω => v i ^ 2 + v i * |X i ω|) P := hconst.add hva
    have hsum : Integrable (fun ω => v i ^ 2 + v i * |X i ω| + {ω | ε ≤ |X i ω|}.indicator (fun ω => X i ω ^ 2) ω) P := hbase.add hind
    have hInt : Integrable (fun ω => C₂*(v i ^ 2 + v i * |X i ω| + {ω | ε ≤ |X i ω|}.indicator (fun ω => X i ω ^ 2) ω)) P := hsum.const_mul _
    have hlast : Integrable (fun ω => ε*C₃*X i ω ^ 2) P := (hX i).const_mul _
    have h := integral_mono (hR i).abs (hInt.add hlast) (hb i)
    simp only [Pi.add_apply] at h
    rw [integral_add hInt hlast,integral_const_mul,integral_const_mul,
      integral_add hbase hind, integral_add hconst hva, integral_const_mul,
      integral_const,probReal_univ,one_smul,integral_indicator hA] at h
    exact h
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  have hsquare : ∑ i, v i ^ 2 ≤ rowMaximum v * ∑ i, v i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right (le_rowMaximum v i) (hv i)
  have hfirst : ∑ i, v i*a i ≤ rowMaximum a * ∑ i, v i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (le_rowMaximum a i) (hv i)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  change ∑ i, ∫ ω, |R i ω| ∂P ≤ C₂*(rowMaximum v*(∑ i, v i)+rowMaximum a*(∑ i, v i)+(∑ i, t i))+ε*C₃*(∑ i,v i)
  exact hsum.trans (add_le_add (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hsquare hfirst) le_rfl) hC₂) le_rfl)

/-- The epsilon-then-n limit in the manuscript. This result is conditional only
on its explicitly displayed pointwise remainder estimate, which is a separate
Taylor-calculus obligation, not hidden in the theorem's conclusion. -/
theorem clt_remainder_sum_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X R : (n : ℕ) → Fin n → Ω → ℝ)
    (hmX : ∀ n i, Measurable (X n i)) (hX : ∀ n i, Integrable (fun ω => X n i ω ^ 2) P)
    (hR : ∀ n i, Integrable (R n i) P) (C₂ C₃ : ℝ) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hvsum : Tendsto (fun n => ∑ i : Fin n, ∫ ω, X n i ω ^ 2 ∂P) atTop (𝓝 1))
    (hL : ∀ ε > 0, Tendsto (fun n => ∑ i : Fin n, ∫ ω in {ω | ε ≤ |X n i ω|}, X n i ω ^ 2 ∂P)
      atTop (𝓝 0))
    (hb : ∀ ε > 0, ∀ᶠ n in atTop, ∀ i ω, |R n i ω| ≤ C₂ * ((∫ x, X n i x ^ 2 ∂P)^2 +
      (∫ x, X n i x ^ 2 ∂P) * |X n i ω| +
      {ω | ε ≤ |X n i ω|}.indicator (fun ω => X n i ω ^ 2) ω) + ε*C₃*X n i ω ^ 2) :
    Tendsto (fun n => ∑ i : Fin n, ∫ ω, |R n i ω| ∂P) atTop (𝓝 0) := by
  have hv := clt_max_second_moment_tendsto_zero P X hmX hX hL
  have ha := clt_max_first_moment_tendsto_zero P X hmX hX hL
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact Eventually.of_forall fun n => hc.trans_le (Finset.sum_nonneg fun i _ => integral_nonneg fun ω => abs_nonneg _)
  · intro δ hδ
    let ε := δ/(2*(C₃+1))
    have hε : 0 < ε := div_pos hδ (by positivity)
    have hsmall : ε*C₃ < δ := by
      dsimp [ε]
      have hden : 0 < 2*(C₃+1) := by positivity
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ hden).mpr
      nlinarith
    have ht := ((hv.mul hvsum).add (ha.mul hvsum) |>.add (hL ε hε)).const_mul C₂
    have hu := ht.add (hvsum.const_mul (ε*C₃))
    simp only [zero_mul,zero_add,mul_zero,mul_one] at hu
    filter_upwards [hb ε hε,(tendsto_order.mp hu).2 δ hsmall] with n hbn hn
    exact (clt_remainder_sum_bound P (X n) (R n) (hmX n) (hX n) (hR n) C₂ C₃ ε hC₂ hbn).trans_lt hn

end Asakura.FullAudit
