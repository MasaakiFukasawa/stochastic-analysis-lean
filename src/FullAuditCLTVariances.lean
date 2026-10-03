import FullAuditDoob

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- The actual second-moment split at epsilon, prior to taking a row maximum. -/
theorem clt_second_moment_split {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hmX : Measurable X) (hX : Integrable (fun ω => X ω ^ 2) P)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ∫ ω, X ω ^ 2 ∂P ≤ ε^2 + ∫ ω in {ω | ε ≤ |X ω|}, X ω ^ 2 ∂P := by
  have hA : MeasurableSet {ω | ε ≤ |X ω|} := measurableSet_le measurable_const (show Measurable (fun ω => |X ω|) from by simpa only [Real.norm_eq_abs] using hmX.norm)
  have hb : ∀ ω, X ω ^ 2 ≤ ε^2 + ({ω | ε ≤ |X ω|}.indicator (fun ω => X ω ^ 2)) ω := by
    intro ω
    by_cases h : ε ≤ |X ω|
    · simp [Set.indicator,h,sq_nonneg ε]
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | ε ≤ |X ω|} from h),add_zero]
      have hh := le_of_lt (lt_of_not_ge h)
      nlinarith [sq_abs (X ω),abs_nonneg (X ω)]
  have h := integral_mono hX ((integrable_const (ε^2)).add (hX.indicator hA)) hb
  simp only [Pi.add_apply] at h
  rwa [integral_add (integrable_const _) (hX.indicator hA),integral_const,
    probReal_univ,one_smul,integral_indicator hA] at h

/-- A finite maximum of nonnegative numbers, with value zero for the empty row. -/
noncomputable def rowMaximum {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  (↑(Finset.univ.sup fun i => (v i).toNNReal) : ℝ)

theorem rowMaximum_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ rowMaximum v :=
  NNReal.coe_nonneg _

theorem le_rowMaximum {ι : Type*} [Fintype ι] (v : ι → ℝ) (i : ι) : v i ≤ rowMaximum v := by
  exact (Real.le_coe_toNNReal _).trans (NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun j => (v j).toNNReal) (Finset.mem_univ i)))

theorem rowMaximum_le {ι : Type*} [Fintype ι] (v : ι → ℝ) (b : ℝ)
    (hb : 0 ≤ b) (h : ∀ i, v i ≤ b) : rowMaximum v ≤ b := by
  have ht : Finset.univ.sup (fun i => (v i).toNNReal) ≤ b.toNNReal :=
    Finset.sup_le (fun i _ => Real.toNNReal_le_toNNReal (h i))
  have hh := NNReal.coe_le_coe.mpr ht
  simpa only [rowMaximum,Real.coe_toNNReal b hb] using hh

/-- The Lindeberg condition forces the maximum actual variance to vanish.
The epsilon cutoff is chosen before n, as in the manuscript. -/
theorem clt_max_second_moment_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : (n : ℕ) → Fin n → Ω → ℝ)
    (hmX : ∀ n i, Measurable (X n i))
    (hX : ∀ n i, Integrable (fun ω => X n i ω ^ 2) P)
    (hL : ∀ ε > 0, Tendsto (fun n => ∑ i : Fin n, ∫ ω in {ω | ε ≤ |X n i ω|}, X n i ω ^ 2 ∂P)
      atTop (𝓝 0)) :
    Tendsto (fun n => rowMaximum (fun i : Fin n => ∫ ω, X n i ω ^ 2 ∂P)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (rowMaximum_nonneg _)
  · intro δ hδ
    let ε := Real.sqrt (δ/2)
    have hε : 0 < ε := Real.sqrt_pos.mpr (by linarith)
    have hεsq : ε^2 = δ/2 := Real.sq_sqrt (by linarith)
    filter_upwards [(tendsto_order.mp (hL ε hε)).2 (δ/2) (by linarith)] with n hn
    have htpos : 0 ≤ ∑ i : Fin n, ∫ ω in {ω | ε ≤ |X n i ω|}, X n i ω ^ 2 ∂P :=
      Finset.sum_nonneg fun i _ => integral_nonneg fun ω => sq_nonneg _
    have hb := rowMaximum_le (fun i : Fin n => ∫ ω, X n i ω ^ 2 ∂P)
      (ε^2 + ∑ i : Fin n, ∫ ω in {ω | ε ≤ |X n i ω|}, X n i ω ^ 2 ∂P)
      (add_nonneg (sq_nonneg _) htpos) (fun i => (clt_second_moment_split P (hmX n i) (hX n i) ε hε.le).trans
        (add_le_add le_rfl (Finset.single_le_sum (f := fun j : Fin n => ∫ ω in {ω | ε ≤ |X n j ω|}, X n j ω ^ 2 ∂P) (fun j _ => integral_nonneg fun ω => sq_nonneg _) (Finset.mem_univ i))))
    linarith

/-- Cauchy--Schwarz with the constant function 1, exactly the moment bound
used before the Lindeberg remainder sum. -/
theorem clt_first_moment_le_sqrt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hmX : Measurable X) (hX : Integrable (fun ω => X ω ^ 2) P) :
    ∫ ω, |X ω| ∂P ≤ Real.sqrt (∫ ω, X ω ^ 2 ∂P) := by
  have h2 : MemLp X 2 P := (memLp_two_iff_integrable_sq hmX.aestronglyMeasurable).mpr hX
  have ha : MemLp (fun ω => |X ω|) (ENNReal.ofReal 2) P := by
    simpa only [ENNReal.ofReal_ofNat,Real.norm_eq_abs] using h2.norm
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun ω => abs_nonneg (X ω))
    (Eventually.of_forall fun _ : Ω => (show (0:ℝ) ≤ 1 from zero_le_one)) ha
    (memLp_const (1:ℝ))
  simpa only [mul_one,Real.rpow_two,sq_abs,one_pow,integral_const,probReal_univ,
    one_smul,Real.one_rpow,mul_one,← Real.sqrt_eq_rpow,Real.sqrt_one,mul_one] using h

/-- The maximum absolute first moment also vanishes; the square-root bound
is uniform over every row, including the empty initial row. -/
theorem clt_max_first_moment_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : (n : ℕ) → Fin n → Ω → ℝ)
    (hmX : ∀ n i, Measurable (X n i))
    (hX : ∀ n i, Integrable (fun ω => X n i ω ^ 2) P)
    (hL : ∀ ε > 0, Tendsto (fun n => ∑ i : Fin n, ∫ ω in {ω | ε ≤ |X n i ω|}, X n i ω ^ 2 ∂P)
      atTop (𝓝 0)) :
    Tendsto (fun n => rowMaximum (fun i : Fin n => ∫ ω, |X n i ω| ∂P)) atTop (𝓝 0) := by
  have hb : ∀ n, rowMaximum (fun i : Fin n => ∫ ω, |X n i ω| ∂P) ≤
      Real.sqrt (rowMaximum (fun i : Fin n => ∫ ω, X n i ω ^ 2 ∂P)) := by
    intro n
    apply rowMaximum_le _ _ (Real.sqrt_nonneg _)
    intro i
    exact (clt_first_moment_le_sqrt P (hmX n i) (hX n i)).trans
      (Real.sqrt_le_sqrt (le_rowMaximum (fun j : Fin n => ∫ ω, X n j ω ^ 2 ∂P) i))
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp
    (clt_max_second_moment_tendsto_zero P X hmX hX hL)
  simp only [Real.sqrt_zero] at hs
  exact squeeze_zero (fun n => rowMaximum_nonneg _) hb hs

end Asakura.FullAudit
