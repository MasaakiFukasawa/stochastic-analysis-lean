import FullAuditHeatIncrement

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.FullAudit

/-- The complete written heat/Taylor/Lindeberg argument for smooth test
functions. The independent array and its actual moments are the only
probabilistic inputs; no CLT or distributional convergence is assumed. -/
theorem clt_smooth_written {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : (n : ℕ) → Fin n → Ω → ℝ)
    (hmX : ∀ n i, Measurable (X n i))
    (hX : ∀ n i, Integrable (fun ω => X n i ω ^ 2) P)
    (hmean : ∀ n i, ∫ ω, X n i ω ∂P = 0)
    (hind : ∀ n, iIndepFun (X n) P)
    (hvsum : Tendsto (fun n => ∑ i : Fin n, ∫ ω, X n i ω ^ 2 ∂P) atTop (𝓝 1))
    (hL : ∀ ε > 0, Tendsto (fun n => ∑ i : Fin n, ∫ ω in {ω | ε ≤ |X n i ω|}, X n i ω ^ 2 ∂P)
      atTop (𝓝 0)) (f : HeatTest) :
    Tendsto (fun n => ∫ ω, f.F 0 (∑ i : Fin n, X n i ω) ∂P) atTop
      (𝓝 (∫ z, f.F 0 z ∂gaussianReal 0 1)) := by
  let v := fun n (i : Fin n) => ∫ ω, X n i ω ^ 2 ∂P
  let q := fun n (k : Fin (n+1)) ω => heatAverage (f.F 0) (rowSum (X n) k ω) (rowTime (v n) k)
  let R := fun n (i : Fin n) => heatIncrementR f (rowSum (X n) i.castSucc) (X n i)
    (rowTime (v n) i.castSucc) (v n i)
  have hv : ∀ n i, 0 ≤ v n i := fun n i => integral_nonneg fun ω => sq_nonneg _
  have hvt : ∀ n (i : Fin n), v n i ≤ rowTime (v n) i.castSucc := by
    intro n i
    rw [rowTime_succ]
    exact le_add_of_nonneg_right (rowTime_nonneg (v n) (hv n) i.succ)
  have h2 : ∀ n i, MemLp (X n i) 2 P := fun n i =>
    (memLp_two_iff_integrable_sq (hmX n i).aestronglyMeasurable).mpr (hX n i)
  have hq : ∀ n k, Integrable (q n k) P := fun n k =>
    f.average_integrable P 0 (rowSum (X n) k) (rowSum_measurable (X n) (hmX n) k) _
  have hR : ∀ n i, Integrable (R n i) P := fun n i => f.increment_integrable P _ _
    (rowSum_measurable (X n) (hmX n) i.castSucc) (hmX n i) (h2 n i) _ _
  have hinc : ∀ n i, ∫ ω, q n i.succ ω-q n i.castSucc ω ∂P = ∫ ω, R n i ω ∂P := by
    intro n i
    have ht : rowTime (v n) i.succ = rowTime (v n) i.castSucc-v n i := by rw [rowTime_succ]; ring
    dsimp [q,R]
    simp_rw [rowSum_succ,ht]
    exact f.increment_expectation P _ _ (rowSum_measurable (X n) (hmX n) i.castSucc)
      (hmX n i) (h2 n i) (hmean n i) (rowSum_independent P (X n) (hmX n) (hind n) i) _
  have hmax := clt_max_second_moment_tendsto_zero P X hmX hX hL
  have hRzero := clt_remainder_sum_tendsto_zero P X R hmX hX hR
    (f.C 2+f.C 3+f.C 4) (f.C 3+f.C 4)
    (by linarith [f.bound_nonneg 2,f.bound_nonneg 3,f.bound_nonneg 4])
    (by linarith [f.bound_nonneg 3,f.bound_nonneg 4]) hvsum hL (by
      intro ε hε
      filter_upwards [(tendsto_order.mp hmax).2 ε hε] with n hn
      intro i ω
      have hvε : v n i ≤ ε := (le_rowMaximum (v n) i).trans hn.le
      have he := f.increment_remainder_eq (rowSum (X n) i.castSucc) (X n i)
        (rowTime (v n) i.castSucc) (v n i) (hv n i) (hvt n i) ω
      dsimp [R]
      rw [he]
      simpa only [Set.indicator_apply,mem_setOf_eq] using
        f.hessian_remainder_estimate (rowSum (X n) i.castSucc ω) (rowTime (v n) i.castSucc)
          (X n i ω) (v n i) ε (hv n i) (hvt n i) hε hvε)
  have hinit : Tendsto (fun n => ∫ ω, q n 0 ω ∂P) atTop (𝓝 (heatAverage (f.F 0) 0 1)) := by
    have ht := (heatAverage_continuous (f.continuous 0) (f.C 0) (f.bound 0)).continuousAt.tendsto.comp
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0)).prodMk_nhds hvsum)
    convert ht using 1
    ext n
    simp only [q,(row_endpoints (X n) (v n)).1,(row_endpoints (X n) (v n)).2.2.1,
      integral_const,probReal_univ,one_smul]
    rfl
  have hlim := clt_smooth_test_limit P q R hq hinc _ hinit hRzero
  have hend : ∀ n, q n (Fin.last n) = fun ω => f.F 0 (∑ i, X n i ω) := by
    intro n
    ext ω
    dsimp [q]
    rw [(row_endpoints (X n) (v n)).2.1 ω,(row_endpoints (X n) (v n)).2.2.2,heatAverage_zero]
  simp_rw [hend] at hlim
  simpa only [heatAverage,Real.sqrt_one,one_mul,zero_add] using hlim

end Asakura.FullAudit
