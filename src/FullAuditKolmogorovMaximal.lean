import FullAuditIndependentSums
import FullAuditDoob
import FullAuditJensenContraction
import Mathlib.Probability.Independence.Integration

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- Expanding the square and canceling the independent centered cross term
 gives the finite variance sum used in the exercise. -/
theorem independent_sum_square_energy {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → Ω → ℝ)
    (hm : ∀ i, Measurable[m] (Z i)) (hi : iIndepFun Z P)
    (h2 : ∀ i, MemLp (Z i) 2 P) (hz : ∀ i, ∫ ω, Z i ω ∂P = 0) (n : ℕ) :
    (∫ ω, (partialSum Z n ω)^2 ∂P) = ∑ i ∈ Finset.range n, ∫ ω, (Z i ω)^2 ∂P := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    have hS := partial_sum_memLp P Z 2 h2 n
    have hSS := (memLp_two_iff_integrable_sq hS.aestronglyMeasurable).mp hS
    have hZZ := (memLp_two_iff_integrable_sq (h2 n).aestronglyMeasurable).mp (h2 n)
    have hSZ : Integrable (fun ω => partialSum Z n ω * Z n ω) P := hS.integrable_mul (h2 n)
    have hind := hi.indepFun_finsetSum_of_notMem hm (show n ∉ Finset.range n by simp)
    have hfun : (∑ j ∈ Finset.range n, Z j) = partialSum Z n := by
      funext ω
      exact Finset.sum_apply ω (Finset.range n) Z
    rw [hfun] at hind
    have hcross : (∫ ω, partialSum Z n ω * Z n ω ∂P) = 0 := by
      have he := hind.integral_mul_eq_mul_integral
        hS.aestronglyMeasurable (h2 n).aestronglyMeasurable
      simpa only [partialSum,Finset.sum_apply,Pi.mul_apply,hz,mul_zero] using he
    have he : (fun ω => (partialSum Z (n+1) ω)^2) =
        (fun ω => (partialSum Z n ω)^2 + 2*(partialSum Z n ω*Z n ω)+(Z n ω)^2) := by
      funext ω
      simp only [partialSum,Finset.sum_range_succ]
      ring
    have hsum : Integrable (fun ω => (partialSum Z n ω)^2 + 2*(partialSum Z n ω*Z n ω)) P := hSS.add (hSZ.const_mul 2)
    rw [he,integral_add hsum hZZ,
      integral_add hSS (hSZ.const_mul 2),integral_const_mul,hcross,mul_zero,add_zero,ih,
      Finset.sum_range_succ]

/-- Corrected maximal inequality: x must be strictly positive. The proof
 applies the manuscript's Doob inequality to the squared partial-sum process. -/
theorem kolmogorov_maximal_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → Ω → ℝ)
    (hm : ∀ i, Measurable[m] (Z i)) (hi : iIndepFun Z P)
    (h2 : ∀ i, MemLp (Z i) 2 P) (hz : ∀ i, ∫ ω, Z i ω ∂P = 0)
    (n : ℕ) (x : ℝ) (hx : 0 < x) :
    P.real {ω | ∃ k ≤ n, x ≤ |partialSum Z k ω|} ≤
      (∫ ω, (partialSum Z n ω)^2 ∂P) / x^2 := by
  let F : Fin (n+1) → MeasurableSpace Ω := fun k => prefixSigma Z k.val
  let X : Fin (n+1) → Ω → ℝ := fun k ω => (partialSum Z k.val ω)^2
  have hF : Monotone F := fun i j hij => prefix_sigma_mono Z hij
  have hle : ∀ k, F k ≤ m := fun k => prefix_sigma_le Z hm k.val
  have hmX : ∀ k, Measurable[F k] (X k) := fun k => (partial_sum_adapted Z k.val).pow_const 2
  have hSn := partial_sum_memLp P Z 2 h2 n
  have hSq : Integrable (fun ω => (partialSum Z n ω)^2) P :=
    (memLp_two_iff_integrable_sq hSn.aestronglyMeasurable).mp hSn
  have hY : Integrable (X ⊤) P := hSq
  have hpos : ∀ k, 0 ≤ᵐ[P] X k := fun k => ae_of_all _ fun ω => sq_nonneg _
  have hdom : ∀ k, X k ≤ᵐ[P] P[X ⊤ | F k] := by
    intro k
    have hj := Asakura.Chapter1Written.conditional_jensen_written
      (G := F k) (hle k) (show ConvexOn ℝ univ (fun y : ℝ => y^2) from by
        simpa only [Real.rpow_two,Real.norm_eq_abs,sq_abs] using norm_rpow_convex 2 (by norm_num)) (hSn.integrable (by norm_num)) hSq
    have hmart := independent_partial_sum_martingale P Z hm hi
      (fun i => (h2 i).integrable (by norm_num)) hz k.val n (Nat.le_of_lt_succ k.isLt)
    filter_upwards [hj,hmart] with ω hj hmart
    change P[partialSum Z n | F k] ω = partialSum Z k.val ω at hmart
    change P[partialSum Z n | F k] ω ^ 2 ≤ P[fun ω => (partialSum Z n ω)^2 | F k] ω at hj
    rw [hmart] at hj
    exact hj
  have hw := doob_weak_written P F hF hle X hmX hY hpos hdom (x^2) (sq_pos_of_pos hx)
  have hB : MeasurableSet[m] {ω | ∃ k : Fin (n+1), x^2 ≤ X k ω} := by
    simpa only [setOf_exists] using MeasurableSet.iUnion (fun k => measurableSet_le measurable_const ((hmX k).mono (hle k) le_rfl))
  have ht := doob_weak_terminal_bound P hY _ hB (x^2) (sq_pos_of_pos hx)
  have habs : (fun ω => |X ⊤ ω|) = (fun ω => (partialSum Z n ω)^2) := by
    funext ω
    exact abs_of_nonneg (sq_nonneg _)
  rw [habs] at ht
  have he : {ω | ∃ k : Fin (n+1), x^2 ≤ X k ω} = {ω | ∃ k ≤ n, x ≤ |partialSum Z k ω|} := by
    ext ω
    simp only [mem_setOf_eq,X]
    constructor
    · rintro ⟨k,hk⟩
      exact ⟨k.val,Nat.le_of_lt_succ k.isLt,(sq_le_sq₀ hx.le (abs_nonneg _)).mp (by simpa only [sq_abs] using hk)⟩
    · rintro ⟨k,hkn,hk⟩
      refine ⟨⟨k,Nat.lt_succ_of_le hkn⟩,?_⟩
      simpa only [sq_abs] using (sq_le_sq₀ hx.le (abs_nonneg _)).mpr hk
  rw [← he]
  simpa only [div_eq_mul_inv,mul_comm] using hw.trans ht
end Asakura.FullAudit
