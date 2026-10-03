import Chapter3WrittenBDG

open MeasureTheory Filter Set
open scoped Topology
namespace Asakura.Chapter3Written

/-- Pointwise energy convergence, including Q=0. -/
theorem regularized_energy_limit {p q : ℝ} (hp : 0 < p)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => (2/p)*((ε n+q)^(p/2)-(ε n)^(p/2)))
      atTop (𝓝 ((2/p)*q^(p/2))) := by
  have hr : 0 < p/2 := by linarith
  have h1 := (hε.add_const q).rpow_const (Or.inr hr.le)
  have h2 := hε.rpow_const_nhds_zero hr
  simpa using (h1.sub h2).const_mul (2/p)

/-- Dominated convergence for the shifted bracket moment. The deterministic
bound K is exactly the localization used at the beginning of the BDG proof. -/
theorem shifted_bracket_moment_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Ω → ℝ)
    (hQ : Measurable Q) {K p : ℝ} (hp : 0 < p)
    (hbound : ∀ ω, 0 ≤ Q ω ∧ Q ω ≤ K)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (he : ∀ n, 0 ≤ ε n ∧ ε n ≤ 1) :
    Tendsto (fun n => ∫ ω, (ε n+Q ω)^(p/2) ∂P) atTop
      (𝓝 (∫ ω, (Q ω)^(p/2) ∂P)) := by
  have hr : 0 ≤ p/2 := by linarith
  have hm : ∀ n, Measurable (fun ω => (ε n+Q ω)^(p/2)) := fun n =>
    (Real.continuous_rpow_const hr).measurable.comp (measurable_const.add hQ)
  apply Asakura.manuscript_dominated_convergence P _ _ (fun _ => (1+K)^(p/2)) hm
    ((Real.continuous_rpow_const hr).measurable.comp hQ) measurable_const (integrable_const _)
  · intro n
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [(he n).1, (hbound ω).1]) _)]
    exact Real.rpow_le_rpow (by linarith [(he n).1, (hbound ω).1])
      (by linarith [(he n).2, (hbound ω).2]) hr
  · filter_upwards [] with ω
    simpa using (hε.add_const (Q ω)).rpow_const (Or.inr hr)

/-- The subtracted initial power also converges inside the energy expectation. -/
theorem regularized_energy_expectation_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Ω → ℝ)
    (hQ : Measurable Q) {K p : ℝ} (hp : 0 < p)
    (hbound : ∀ ω, 0 ≤ Q ω ∧ Q ω ≤ K)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (he : ∀ n, 0 ≤ ε n ∧ ε n ≤ 1) :
    Tendsto (fun n => ∫ ω, ((ε n+Q ω)^(p/2)-(ε n)^(p/2)) ∂P)
      atTop (𝓝 (∫ ω, (Q ω)^(p/2) ∂P)) := by
  have hr : 0 < p/2 := by linarith
  have hb n : Integrable (fun ω => (ε n+Q ω)^(p/2)) P := by
    apply (integrable_const ((1+K)^(p/2))).mono'
      ((Real.continuous_rpow_const hr.le).measurable.comp (measurable_const.add hQ)).aestronglyMeasurable
    filter_upwards [] with ω
    change ‖(ε n+Q ω)^(p/2)‖ ≤ (1+K)^(p/2)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [(he n).1, (hbound ω).1]) _)]
    exact Real.rpow_le_rpow (by linarith [(he n).1, (hbound ω).1])
      (by linarith [(he n).2, (hbound ω).2]) hr.le
  simp_rw [integral_sub (hb _) (integrable_const _), integral_const, probReal_univ, one_smul]
  simpa using (shifted_bracket_moment_limit P Q hQ hp hbound ε hε he).sub
    (hε.rpow_const_nhds_zero hr)

/-- Passing the regularized Holder/Doob inequality to the limit. The input
inequality is explicit; this theorem does not assert an unproved BDG inequality. -/
theorem bdg_regularized_bound_limit {a b : ℕ → ℝ} {L M C p : ℝ}
    (hp : 0 < p) (hp2 : p < 2)
    (ha : Tendsto a atTop (𝓝 M)) (hb : Tendsto b atTop (𝓝 M))
    (hineq : ∀ n, L ≤ C * (a n)^(p/2) * (b n)^((2-p)/2))
    (hM : 0 ≤ M) : L ≤ C*M := by
  have h1 := ha.rpow_const (Or.inr (by linarith : 0 ≤ p/2))
  have h2 := hb.rpow_const (Or.inr (by linarith : 0 ≤ (2-p)/2))
  have hlim := ge_of_tendsto' ((h1.const_mul C).mul h2) hineq
  have he : M^(p/2) * M^((2-p)/2) = M := by
    rw [← Real.rpow_add_of_nonneg hM (by linarith : 0 ≤ p/2) (by linarith : 0 ≤ (2-p)/2)]
    have hh : p/2+(2-p)/2 = 1 := by ring
    rw [hh, Real.rpow_one]
  simpa only [mul_assoc, he] using hlim

end Asakura.Chapter3Written
