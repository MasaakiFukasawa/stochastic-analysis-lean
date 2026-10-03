import Chapter3WrittenRegularization

open MeasureTheory Filter Set
open scoped Topology
namespace Asakura.Chapter3Complete
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Dominated convergence for shifted positive moments under an a.e. bound,
as supplied by stopping a local martingale. -/
theorem shifted_moment_limit_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Ω → ℝ) (hQ : Measurable Q) (hQp : ∀ ω, 0 ≤ Q ω)
    (K r : ℝ) (hr : 0 < r) (hbound : ∀ᵐ ω ∂P, Q ω ≤ K)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (he : ∀ n, 0 ≤ ε n ∧ ε n ≤ 1) :
    Tendsto (fun n => ∫ ω, (ε n+Q ω)^r ∂P) atTop (𝓝 (∫ ω, Q ω^r ∂P)) := by
  have hm n : Measurable (fun ω => (ε n+Q ω)^r) :=
    (Real.continuous_rpow_const hr.le).measurable.comp (measurable_const.add hQ)
  apply Asakura.manuscript_dominated_convergence P _ _ (fun _ => (1+K)^r) hm
    ((Real.continuous_rpow_const hr.le).measurable.comp hQ) measurable_const (integrable_const _)
  · intro n
    filter_upwards [hbound] with ω hω
    change ‖(ε n+Q ω)^r‖ ≤ (1+K)^r
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (by linarith [(he n).1,hQp ω]) _)]
    exact Real.rpow_le_rpow (by linarith [(he n).1,hQp ω]) (by linarith [(he n).2]) hr.le
  · exact Filter.Eventually.of_forall (fun ω => by
      simpa using (hε.add_const (Q ω)).rpow_const (Or.inr hr.le))

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.shifted_moment_limit_ae
