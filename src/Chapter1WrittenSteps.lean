import ManuscriptDominated
import ConvexTail

/- Checks of inferences actually printed in chap1.tex.
Each premise below is an explicitly identified preceding step of the manuscript.
This file does not certify the entire chapter or supply a replacement CLT proof. -/
open MeasureTheory Set Filter
open scoped Topology
set_option linter.unusedSectionVars false
namespace Asakura.Chapter1Written
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- lem:l1conti: the two sign sets are disjoint, so the last inequality has constant 1. -/
theorem sign_split (x y : ℝ) :
    (if 0 < y then x else 0) - (if y < 0 then x else 0) ≤ |x| := by
  split_ifs <;> linarith [le_abs_self x, neg_le_abs x, abs_nonneg x]

/-- lem:l1conti: the preceding equality, before applying C2. -/
theorem abs_sign_split (y : ℝ) :
    |y| = (if 0 < y then y else 0) - (if y < 0 then y else 0) := by
  split_ifs <;> simp_all [abs_of_pos, abs_of_neg, abs_of_nonneg] <;> linarith

/-- lem:l1conti: C2 on the two sign sets implies precisely the printed L1 estimate.
Only the two C2 identities are inputs; no conditional-expectation contraction is used. -/
theorem l1_bound_from_C2 {X Y : Ω → ℝ} (hX : Integrable X P) (hY : Integrable Y P)
    (hmY : Measurable Y)
    (hpos : ∫ ω, ({ω | 0 < Y ω}.indicator Y) ω ∂P =
      ∫ ω, ({ω | 0 < Y ω}.indicator X) ω ∂P)
    (hneg : ∫ ω, ({ω | Y ω < 0}.indicator Y) ω ∂P =
      ∫ ω, ({ω | Y ω < 0}.indicator X) ω ∂P) :
    ∫ ω, |Y ω| ∂P ≤ ∫ ω, |X ω| ∂P := by
  have hp : MeasurableSet {ω | 0 < Y ω} := measurableSet_lt measurable_const hmY
  have hn : MeasurableSet {ω | Y ω < 0} := measurableSet_lt hmY measurable_const
  have he : (fun ω => |Y ω|) =
      {ω | 0 < Y ω}.indicator Y - {ω | Y ω < 0}.indicator Y := by
    funext ω
    simpa [Set.indicator, Pi.sub_apply] using abs_sign_split (Y ω)
  rw [he]
  change (∫ ω, {ω | 0 < Y ω}.indicator Y ω - {ω | Y ω < 0}.indicator Y ω ∂P) ≤ _
  rw [integral_sub (hY.indicator hp) (hY.indicator hn), hpos, hneg,
    ← integral_sub (hX.indicator hp) (hX.indicator hn)]
  apply integral_mono ((hX.indicator hp).sub (hX.indicator hn)) hX.abs
  intro ω
  simpa [Set.indicator, Pi.sub_apply] using sign_split (X ω) (Y ω)

/-- prop:ce and thm:l1conv use this particular cutoff, not simple-function density. -/
theorem cutoff_L2 [IsFiniteMeasure P] {X : Ω → ℝ} (hX : Measurable X) (n : ℕ) :
    MemLp ({ω | |X ω| ≤ (n : ℝ)}.indicator X) 2 P := by
  have hmabs : Measurable (fun ω => |X ω|) := by simpa only [Real.norm_eq_abs] using hX.norm
  apply MemLp.of_bound ((hX.indicator (measurableSet_le hmabs measurable_const)).aestronglyMeasurable) (n : ℝ)
  exact Eventually.of_forall (by
    intro ω
    by_cases h : |X ω| ≤ (n : ℝ)
    · simp [Set.indicator, h, Real.norm_eq_abs]
    · simp [Set.indicator, h])

/-- The exact cutoff tail integral tends to zero by the appendix's DCT proof. -/
theorem cutoff_tail_L1 {X : Ω → ℝ} (hmX : Measurable X) (hX : Integrable X P) :
    Tendsto (fun n : ℕ => ∫ ω, {ω | (n : ℝ) < |X ω|}.indicator (fun ω => |X ω|) ω ∂P)
      atTop (𝓝 0) := by
  have hmabs : Measurable (fun ω => |X ω|) := by simpa only [Real.norm_eq_abs] using hmX.norm
  have ht := Asakura.manuscript_dominated_convergence P
    (fun n : ℕ => {ω | (n : ℝ) < |X ω|}.indicator (fun ω => |X ω|))
    (fun _ => 0) (fun ω => |X ω|)
    (fun n => hmabs.indicator (measurableSet_lt measurable_const hmabs))
    measurable_const hmabs hX.abs
    (fun n => Eventually.of_forall (by
      intro ω
      by_cases h : (n : ℝ) < |X ω| <;> simp [Set.indicator, h]))
    (Eventually.of_forall (by
      intro ω
      obtain ⟨N, hN⟩ := exists_nat_gt |X ω|
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hb : ¬ (n : ℝ) < |X ω| := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      simp [Set.indicator, hb]))
  simpa using ht

/-- Jensen: the countable common full-measure set and supremum step, exactly as printed.
The supporting-line representation must be proved separately, and is not hidden here. -/
theorem countable_support_step (φ : ℝ → ℝ) (a b : ℚ → ℝ) (Y Z : Ω → ℝ)
    (hrep : ∀ x, φ x = ⨆ q : ℚ, a q + b q * x)
    (hline : ∀ q, ∀ᵐ ω ∂P, a q + b q * Y ω ≤ Z ω) :
    ∀ᵐ ω ∂P, φ (Y ω) ≤ Z ω := by
  filter_upwards [ae_all_iff.mpr hline] with ω hω
  rw [hrep]
  exact ciSup_le hω

/-- CLT: expanding the Hessian quadratic form with increment (x,-v). -/
theorem hessian_expansion (x v hxx hxt htt hxx₀ : ℝ) :
    (x * (hxx * x + hxt * (-v)) + (-v) * (hxt * x + htt * (-v))) - hxx₀*x^2 =
      (hxx-hxx₀)*x^2 - 2*hxt*x*v + htt*v^2 := by ring

/-- CLT: the small-increment Hessian-difference contribution after integrating s(1-s).
The manuscript's Euclidean bound |(x,-v)| < 2ε implies both coordinate bounds. -/
theorem small_increment_constant (x v ε C : ℝ) (_hv : 0 ≤ v) (hε : 0 ≤ ε)
    (hC : 0 ≤ C) (hx : |x| ≤ 2*ε) (hvt : v ≤ 2*ε) :
    C * (|x|+v) / 6 * x^2 ≤ ε*C*x^2 := by
  have hs : (|x|+v)/6 ≤ ε := by linarith
  nlinarith [mul_nonneg hC (sq_nonneg x),
    mul_le_mul_of_nonneg_right hs (mul_nonneg hC (sq_nonneg x))]

/-- CLT: all three Hessian terms give exactly the displayed remainder bound.
A is the xx-difference integral; B and D are the integrated xt and tt terms. -/
theorem remainder_assembly (x v ε C₂ C₃ A B D : ℝ) (I : ℝ)
    (hC₂ : 0 ≤ C₂) (_hv : 0 ≤ v)
    (hA : |A| ≤ C₂*x^2*I + ε*C₃*x^2)
    (hB : |B| ≤ C₂*v*|x|) (hD : |D| ≤ C₂*v^2/2) :
    |A+B+D| ≤ C₂*(v^2+v*|x|+x^2*I)+ε*C₃*x^2 := by
  have htri := (abs_add_le (A+B) D).trans (add_le_add (abs_add_le A B) le_rfl)
  nlinarith [mul_nonneg hC₂ (sq_nonneg v)]

/-- CLT: max variance bound comes from splitting at ε, uniformly in k. -/
theorem variance_tail_bound {ι : Type*} [Fintype ι] (v tail : ι → ℝ) (ε : ℝ)
    (ht : ∀ i, 0 ≤ tail i) (hsplit : ∀ i, v i ≤ ε^2 + tail i) (k : ι) :
    v k ≤ ε^2 + ∑ i, tail i := by
  exact (hsplit k).trans (add_le_add le_rfl (Finset.single_le_sum (fun i _ => ht i) (Finset.mem_univ k)))

/-- CLT: large space-time increments imply large space increments once v ≤ ε. -/
theorem large_increment (x v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hvt : v ≤ ε) (hlarge : (2*ε)^2 ≤ x^2+v^2) : ε ≤ |x| := by
  by_contra h
  have hx := lt_of_not_ge h
  have hx2 : x^2 < ε^2 := by nlinarith [sq_abs x, abs_nonneg x]
  nlinarith [sq_nonneg (ε-v)]

/-- thm:l1conv: the printed two-limit argument for 2*cutoff_error + L2_error.
The order of the limits is respected: fix m before choosing n. -/
theorem cutoff_two_limits (a : ℕ → ℝ) (b : ℕ → ℕ → ℝ) (d : ℕ → ℝ)
    (hd : ∀ n, 0 ≤ d n) (ha : Tendsto a atTop (𝓝 0))
    (hb : ∀ m, Tendsto (b m) atTop (𝓝 0))
    (hbound : ∀ m n, d n ≤ 2*a m+b m n) : Tendsto d atTop (𝓝 0) := by
  apply (tendsto_order.2 ⟨?_, ?_⟩)
  · intro c hc
    exact Eventually.of_forall (fun n => hc.trans_le (hd n))
  · intro ε hε
    obtain ⟨m, hm⟩ := ((tendsto_order.1 ha).2 (ε/4) (by linarith)).exists
    filter_upwards [(tendsto_order.1 (hb m)).2 (ε/2) (by linarith)] with n hn
    have := hbound m n
    linarith

/-- prop:st3: the nonzero level-set identity in the simple-function proof. -/
theorem indicator_nonzero_level (X : Ω → ℝ) (E : Set Ω) (a : ℝ) (ha : a ≠ 0) :
    {ω | E.indicator X ω = a} = {ω | X ω = a} ∩ E := by
  classical
  ext ω
  by_cases h : ω ∈ E <;> simp [Set.indicator, h, ha.symm]

/-- martconv: for a FIXED event (represented by L), every sufficiently late convex
combination has the same integral. Its limit therefore has that integral. -/
theorem convex_tail_fixed_test {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f g : ℕ → H) (Y : H) (L : H →L[ℝ] ℝ) (c : ℝ) (N : ℕ)
    (hg : ∀ n, g n ∈ convexHull ℝ (f '' Ici n))
    (ht : Tendsto g atTop (𝓝 Y)) (hf : ∀ n, N ≤ n → L (f n) = c) : L Y = c := by
  have he : (fun n => L (g n)) =ᶠ[atTop] (fun _ => c) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hs : convexHull ℝ (f '' Ici n) ⊆ L ⁻¹' {c} := by
      apply convexHull_min _ ((convex_singleton c).linear_preimage L.toLinearMap)
      rintro x ⟨k, hk, rfl⟩
      exact hf k (hn.trans hk)
    exact hs (hg n)
  exact tendsto_nhds_unique (L.continuous.tendsto Y |>.comp ht)
    (tendsto_const_nhds.congr' he.symm)

/-- martconv/martconv2: the printed bounded-sequence convex-tail construction,
using the separately checked appendix proof, followed by completeness. -/
theorem convergent_convex_tails {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : ℕ → H) (R : ℝ) (hf : ∀ n, ‖f n‖ ≤ R) :
    ∃ (g : ℕ → H) (Y : H), (∀ n, g n ∈ convexHull ℝ (f '' Ici n)) ∧
      Tendsto g atTop (𝓝 Y) := by
  obtain ⟨g, hg, hc⟩ := Asakura.convex_tail_selection f R hf
  obtain ⟨Y, hY⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨g, Y, hg, hY⟩

end Asakura.Chapter1Written
