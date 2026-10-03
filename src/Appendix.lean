import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Selected formal checks for asakura2e, Appendices A--C.
Library-backed results certify the explicitly stated propositions, NOT the
manuscript's individual proof steps. Section C below checks deterministic
steps only; it does not claim to formalize the stochastic continuity theorem.
-/
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Asakura

section AppendixA
variable {Ω S : Type*}

/-- A.1: π--λ theorem (Mathlib's equivalent Dynkin-system convention). -/
theorem pi_lambda (P : Set (Set Ω)) (hP : IsPiSystem P)
    (L : MeasurableSpace.DynkinSystem Ω) (hPL : ∀ s ∈ P, L.Has s)
    (s : Set Ω) (hs : MeasurableSet[MeasurableSpace.generateFrom P] s) : L.Has s := by
  rw [MeasurableSpace.DynkinSystem.generateFrom_eq hP] at hs
  exact L.generate_le hPL s hs

/-- A.2: measurability checked on a generating family. -/
theorem measurable_on_generators [MeasurableSpace Ω] (P : Set (Set S)) (f : Ω → S)
    (h : ∀ s ∈ P, MeasurableSet (f ⁻¹' s)) :
    @Measurable Ω S _ (MeasurableSpace.generateFrom P) f := measurable_generateFrom h

/-- A.2: pairing of measurable maps into the product measurable space. -/
theorem measurable_pair [MeasurableSpace Ω] [MeasurableSpace S] {T : Type*}
    [MeasurableSpace T] {f : Ω → S} {g : Ω → T}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => (f x, g x) := hf.prodMk hg

/-- A.2: countable suprema, with extended nonnegative values. -/
theorem measurable_sup [MeasurableSpace Ω] (f : ℕ → Ω → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) : Measurable fun x => ⨆ n, f n x := .iSup hf

theorem measurable_inf [MeasurableSpace Ω] (f : ℕ → Ω → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) : Measurable fun x => ⨅ n, f n x := .iInf hf

/-- A.3: continuity from below, including infinite measures. -/
theorem measure_continuity_below [MeasurableSpace Ω] (μ : Measure Ω)
    (s : ℕ → Set Ω) (hs : Monotone s) :
    Tendsto (fun n => μ (s n)) atTop (𝓝 (μ (⋃ n, s n))) :=
  tendsto_measure_iUnion_atTop hs

/-- A.4: monotone convergence, in its limit formulation. -/
theorem monotone_convergence [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ℕ → Ω → ℝ≥0∞) (F : Ω → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) (hm : ∀ x, Monotone fun n => f n x)
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 (∫⁻ x, F x ∂μ)) := by
  exact lintegral_tendsto_of_tendsto_of_monotone (fun n => (hf n).aemeasurable)
    (Filter.Eventually.of_forall hm) (Filter.Eventually.of_forall hlim)

/-- A.4: Fatou's lemma. -/
theorem fatou [MeasurableSpace Ω] (μ : Measure Ω) (f : ℕ → Ω → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) :
    ∫⁻ x, liminf (fun n => f n x) atTop ∂μ ≤
      liminf (fun n => ∫⁻ x, f n x ∂μ) atTop := lintegral_liminf_le hf

/-- A.4: dominated convergence for real-valued measurable functions. -/
theorem dominated_convergence [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ℕ → Ω → ℝ) (F g : Ω → ℝ) (hf : ∀ n, Measurable (f n))
    (hg : Integrable g μ) (hb : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ g x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
  exact tendsto_integral_of_dominated_convergence g
    (fun n => (hf n).aestronglyMeasurable) hg hb hlim

/-- A.4: linearity with arbitrary real coefficients. -/
theorem integral_linear [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (a b : ℝ) :
    ∫ x, a * f x + b * g x ∂μ = a * ∫ x, f x ∂μ + b * ∫ x, g x ∂μ := by
  rw [integral_add (hf.const_mul a) (hg.const_mul b), integral_const_mul, integral_const_mul]
end AppendixA

section AppendixB
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]

/-- B.1: completeness of the Bochner Lp space, including p = infinity. -/
theorem lp_complete (μ : Measure Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    CompleteSpace (Lp E p μ) := inferInstance

/-- B.1: Minkowski in the normed quotient Lp space, including the endpoints. -/
theorem minkowski (μ : Measure Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)] (f g : Lp E p μ) :
    ‖f + g‖ ≤ ‖f‖ + ‖g‖ := norm_add_le f g

/-- B.1: finite conjugate exponents; nonnegative extended-valued formulation. -/
theorem holder_finite (μ : Measure Ω) (p q : ℝ) (hpq : p.HolderConjugate q)
    (f g : Ω → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, f x * g x ∂μ) ≤
      (∫⁻ x, f x ^ p ∂μ) ^ (1 / p) * (∫⁻ x, g x ^ q ∂μ) ^ (1 / q) := by
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf.aemeasurable hg.aemeasurable
end AppendixB

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- B.2.1: the corrected positive-part estimate, following the manuscript algebra. -/
theorem convex_tail_estimate (x y : H) (A δ e : ℝ)
    (hx : ‖x‖ ≤ A + e) (hy : ‖y‖ ≤ A + e)
    (hs : 2 * max (A - δ) 0 ≤ ‖x + y‖) :
    ‖x - y‖ ^ 2 ≤ 4 * (A + e) ^ 2 - 4 * (max (A - δ) 0) ^ 2 := by
  have ha : 0 ≤ A + e := le_trans (norm_nonneg x) hx
  have hp : 0 ≤ max (A - δ) 0 := le_max_right _ _
  have hx2 : ‖x‖ ^ 2 ≤ (A + e) ^ 2 := by nlinarith [norm_nonneg x]
  have hy2 : ‖y‖ ^ 2 ≤ (A + e) ^ 2 := by nlinarith [norm_nonneg y]
  have hs2 : 4 * (max (A - δ) 0) ^ 2 ≤ ‖x + y‖ ^ 2 := by nlinarith
  have hpar := parallelogram_law_with_norm ℝ x y
  nlinarith

/-- B.2.2: existence of a minimizer on a nonempty closed convex set. -/
theorem projection_exists [CompleteSpace H] (C : Set H) (hne : C.Nonempty)
    (hc : IsClosed C) (hconv : Convex ℝ C) (u : H) :
    ∃ v ∈ C, ‖u - v‖ = ⨅ w : C, ‖u - w‖ :=
  exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hconv u

/-- B.2.2: uniqueness, checked directly with the parallelogram identity. -/
theorem projection_unique (C : Set H) (hc : Convex ℝ C) (u v w : H)
    (hv : v ∈ C) (hw : w ∈ C)
    (hminv : ∀ z ∈ C, ‖u - v‖ ≤ ‖u - z‖)
    (hminw : ∀ z ∈ C, ‖u - w‖ ≤ ‖u - z‖) : v = w := by
  have heq : ‖u - v‖ = ‖u - w‖ := le_antisymm (hminv w hw) (hminw v hv)
  have hmid := hc hv hw (a := (1/2 : ℝ)) (b := (1/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hm := hminv _ hmid
  have hpar := parallelogram_law_with_norm ℝ (u-v) (u-w)
  have hsum : (u-v) + (u-w) = (2:ℝ) • (u - ((1/2:ℝ) • v + (1/2:ℝ) • w)) := by module
  have hdiff : (u-v) - (u-w) = w-v := by abel
  rw [hsum, hdiff, norm_smul] at hpar
  norm_num at hpar
  have hz : ‖w-v‖ = 0 := by nlinarith [norm_nonneg (w-v), norm_nonneg (u-v)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

/-- B.2.2: characterization of projection onto a real linear subspace. -/
theorem projection_orthogonal (K : Submodule ℝ H) (u v : H) (hv : v ∈ K) :
    (‖u-v‖ = ⨅ w : (K : Set H), ‖u-w‖) ↔ ∀ w ∈ K, inner ℝ (u-v) w = 0 :=
  K.norm_eq_iInf_iff_real_inner_eq_zero hv
end Hilbert

/-- B.3.1: existence AND uniqueness of the uniformly continuous extension. -/
theorem uniform_extension {S T : Type*} [MetricSpace S] [MetricSpace T] [CompleteSpace T]
    (D : Set S) (hd : Dense D) (f : D → T) (hf : UniformContinuous f) :
    ∃! g : S → T, UniformContinuous g ∧ ∀ x : D, g x = f x := by
  refine ⟨hd.extend f, ⟨hd.uniformContinuous_extend hf, hd.extend_of_ind hf⟩, ?_⟩
  intro g hg
  apply Continuous.ext_on hd hg.1.continuous (hd.uniformContinuous_extend hf).continuous
  intro x hx
  exact (hg.2 ⟨x,hx⟩).trans (hd.extend_of_ind hf ⟨x,hx⟩).symm

section AppendixC
/-- The manuscript's maximum norm is Lean's norm on a finite Pi type. -/
theorem cube_diameter (d : ℕ) (s t : Fin d → ℝ)
    (hs : ∀ i, s i ∈ Set.Icc (0:ℝ) 1) (ht : ∀ i, t i ∈ Set.Icc (0:ℝ) 1) :
    ‖s-t‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).2
  intro i
  change ‖s i - t i‖ ≤ 1
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [(hs i).1,(hs i).2,(ht i).1,(ht i).2]

/-- All pairs of distinct cube points admit a nonnegative dyadic scale. -/
theorem cube_dyadic_scale (d : ℕ) (s t : Fin d → ℝ) (hne : s ≠ t)
    (hs : ∀ i, s i ∈ Set.Icc (0:ℝ) 1) (ht : ∀ i, t i ∈ Set.Icc (0:ℝ) 1) :
    ∃ m : ℕ, (1/2:ℝ)^(m+1) < ‖s-t‖ ∧ ‖s-t‖ ≤ (1/2:ℝ)^m := by
  apply exists_nat_pow_near_of_lt_one _ (cube_diameter d s t hs ht) (by norm_num) (by norm_num)
  exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)

/-- Delta_0 contains every ordered pair of cube vertices. -/
theorem delta_zero (d : ℕ) (s t : Fin d → ℝ)
    (hs : ∀ i, s i = 0 ∨ s i = 1) (ht : ∀ i, t i = 0 ∨ t i = 1) :
    ∀ i, |s i - t i| ≤ 1 := by
  intro i
  rcases hs i with h | h <;> rcases ht i with k | k <;> rw [h,k] <;> norm_num

noncomputable def roundDown (m : ℕ) (x : ℝ) : ℝ := (⌊(2:ℝ)^m*x⌋ : ℝ) / (2:ℝ)^m

/-- Explicit grid approximation lies below its target. -/
theorem roundDown_le (m : ℕ) (x : ℝ) : roundDown m x ≤ x := by
  unfold roundDown
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2^m)).2
  simpa [mul_comm] using Int.floor_le ((2:ℝ)^m*x)

/-- The approximation error is strictly smaller than one grid step. -/
theorem roundDown_error (m : ℕ) (x : ℝ) : x < roundDown m x + 1/(2:ℝ)^m := by
  unfold roundDown
  rw [← add_div]
  apply (lt_div_iff₀ (by positivity : (0:ℝ)<2^m)).2
  simpa [mul_comm] using Int.lt_floor_add_one ((2:ℝ)^m*x)

/-- A dyadic point is fixed at every finer grid level. -/
theorem roundDown_eventual (k l : ℕ) (z : ℤ) :
    roundDown (k+l) ((z:ℝ)/(2:ℝ)^k) = (z:ℝ)/(2:ℝ)^k := by
  have hz : (2:ℝ)^(k+l)*((z:ℝ)/(2:ℝ)^k) = ((z * 2^l : ℤ):ℝ) := by
    push_cast
    rw [pow_add]
    field_simp
  unfold roundDown
  rw [hz, Int.floor_intCast]
  push_cast
  rw [pow_add]
  field_simp

/-- Floor values of points within distance one differ by at most one. -/
theorem floor_adjacent (a b : ℝ) (h : |a-b| ≤ 1) :
    |(⌊a⌋:ℝ) - (⌊b⌋:ℝ)| ≤ 1 := by
  have h1 : a ≤ b+1 := by have := (abs_le.mp h).2; linarith
  have h2 : b ≤ a+1 := by have := (abs_le.mp h).1; linarith
  have hf1 : ⌊a⌋ ≤ ⌊b⌋+1 := by simpa using Int.floor_mono h1
  have hf2 : ⌊b⌋ ≤ ⌊a⌋+1 := by simpa using Int.floor_mono h2
  have hc1 : (⌊a⌋:ℝ) ≤ (⌊b⌋:ℝ)+1 := by exact_mod_cast hf1
  have hc2 : (⌊b⌋:ℝ) ≤ (⌊a⌋:ℝ)+1 := by exact_mod_cast hf2
  rw [abs_le]
  constructor <;> linarith

/-- Pairwise proximity is preserved by the chosen grid approximation. -/
theorem roundDown_adjacent (m : ℕ) (s t : ℝ) (h : |s-t| ≤ 1/(2:ℝ)^m) :
    |roundDown m s - roundDown m t| ≤ 1/(2:ℝ)^m := by
  have hp : (0:ℝ) < 2^m := by positivity
  have hscaled : |(2:ℝ)^m*s - (2:ℝ)^m*t| ≤ 1 := by
    rw [← mul_sub, abs_mul, abs_of_pos hp]
    have h' := (le_div_iff₀ hp).mp h
    nlinarith
  have hf := floor_adjacent ((2:ℝ)^m*s) ((2:ℝ)^m*t) hscaled
  unfold roundDown
  rw [← sub_div, abs_div, abs_of_pos hp]
  exact (div_le_div_iff_of_pos_right hp).2 hf
/- C.2.1: the positive exponent is essential for this uniform continuity step. -/
theorem positive_holder_uniformContinuous {S T : Type*} [MetricSpace S] [MetricSpace T]
    (f : S → T) (M α : ℝ) (ha : 0 < α)
    (h : ∀ s t, dist (f s) (f t) ≤ M * (dist s t) ^ α) : UniformContinuous f := by
  have hc : ContinuousAt (fun r : ℝ => M * r ^ α) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 α (Or.inr ha.le))
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := (Metric.continuousAt_iff.mp hc) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro s t hst
  have hdist : dist (dist s t) (0:ℝ) < δ := by simpa using hst
  have he := hd hdist
  rw [Real.zero_rpow ha.ne', mul_zero, Real.dist_eq, sub_zero] at he
  exact lt_of_le_of_lt (h s t) (lt_of_le_of_lt (le_abs_self _) he)

/-- Consecutive rounded approximations are monotone and adjacent on the finer grid. -/
theorem roundDown_refinement (m : ℕ) (x : ℝ) :
    roundDown m x ≤ roundDown (m+1) x ∧
    |roundDown (m+1) x - roundDown m x| ≤ 1/(2:ℝ)^(m+1) := by
  let a : ℝ := (2:ℝ)^m*x
  have hflo : 2 * ⌊a⌋ ≤ ⌊2*a⌋ := by
    apply Int.le_floor.mpr
    push_cast
    nlinarith [Int.floor_le a]
  have hfhi : ⌊2*a⌋ < 2*⌊a⌋+2 := by
    apply Int.floor_lt.mpr
    push_cast
    nlinarith [Int.lt_floor_add_one a]
  have hlo : 2*(⌊a⌋:ℝ) ≤ (⌊2*a⌋:ℝ) := by exact_mod_cast hflo
  have hhi : (⌊2*a⌋:ℝ) ≤ 2*(⌊a⌋:ℝ)+1 := by
    have hi : ⌊2*a⌋ ≤ 2*⌊a⌋+1 := by omega
    exact_mod_cast hi
  have hp : (0:ℝ) < 2^m := by positivity
  have heq : (2:ℝ)^(m+1)*x = 2*a := by dsimp [a]; rw [pow_succ]; ring
  have hr : roundDown (m+1) x - roundDown m x =
      ((⌊2*a⌋:ℝ) - 2*(⌊a⌋:ℝ)) / ((2:ℝ)^m*2) := by
    unfold roundDown
    rw [heq, pow_succ]
    change (⌊2*a⌋:ℝ) / (2^m*2) - (⌊a⌋:ℝ) / 2^m = _
    field_simp
  have hn : 0 ≤ roundDown (m+1) x - roundDown m x := by
    rw [hr]
    exact div_nonneg (by linarith) (by positivity)
  refine ⟨by linarith, ?_⟩
  rw [abs_of_nonneg hn, hr, pow_succ]
  apply (div_le_div_iff_of_pos_right (by positivity : (0:ℝ)<2^m*2)).2
  linarith
end AppendixC

/-- B.3.2: continuity and boundedness of a real linear map are equivalent. -/
theorem linear_continuous_iff_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →ₗ[ℝ] F) :
    Continuous A ↔ ∃ C : ℝ, 0 < C ∧ ∀ x, ‖A x‖ ≤ C * ‖x‖ := by
  constructor
  · exact SemilinearMapClass.bound_of_continuous A
  · rintro ⟨C, _, hC⟩
    exact (A.mkContinuous C hC).continuous

/-- B.3.2: continuity implies uniform continuity for a linear map. -/
theorem linear_uniform_of_continuous {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →ₗ[ℝ] F) (h : Continuous A) :
    UniformContinuous A := by
  obtain ⟨C, _, hC⟩ := (linear_continuous_iff_bound A).mp h
  exact (A.mkContinuous C hC).uniformContinuous

/-- C.2: continuous modifications agree simultaneously, using a countable dense set. -/
theorem continuous_modifications_agree {T Ω : Type*} [MetricSpace T] [MeasurableSpace Ω]
    (μ : Measure Ω) (D : Set T) (hd : Dense D) (hcount : D.Countable)
    (X Y : T → Ω → ℝ)
    (hX : ∀ᵐ ω ∂μ, Continuous (fun t => X t ω))
    (hY : ∀ᵐ ω ∂μ, Continuous (fun t => Y t ω))
    (heq : ∀ t, X t =ᵐ[μ] Y t) :
    ∀ᵐ ω ∂μ, (fun t => X t ω) = (fun t => Y t ω) := by
  let : Countable D := hcount.to_subtype
  have hD : ∀ᵐ ω ∂μ, ∀ t : D, X t ω = Y t ω := by
    exact (ae_all_iff).2 (fun t => heq t)
  filter_upwards [hX,hY,hD] with ω hx hy he
  exact Continuous.ext_on hd hx hy (fun t ht => he ⟨t,ht⟩)
end Asakura
