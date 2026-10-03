import IntegralConstruction

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura

/-- app0:286: differences of increasing sets, countable additivity, partial sums. -/
theorem manuscript_measure_iUnion {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n))
    (hmono : Monotone A) : μ (⋃ n, A n) = ⨆ n, μ (A n) := by
  classical
  have hd : ∀ n, MeasurableSet (disjointed A n) := MeasurableSet.disjointed hA
  have hpartial : ∀ n, (⋃ i ∈ Finset.range (n+1), disjointed A i) = A n := by
    intro n
    rw [biUnion_range_succ_disjointed]
    exact congrFun hmono.partialSups_eq n
  calc
    μ (⋃ n, A n) = μ (⋃ n, disjointed A n) := by rw [iUnion_disjointed]
    _ = ∑' n, μ (disjointed A n) := measure_iUnion (disjoint_disjointed A) hd
    _ = ⨆ n, ∑ i ∈ Finset.range (n+1), μ (disjointed A i) :=
      ENNReal.tsum_eq_iSup_nat' (tendsto_add_atTop_nat 1)
    _ = ⨆ n, μ (A n) := by
      apply iSup_congr
      intro n
      rw [← measure_biUnion_finset ((disjoint_disjointed A).set_pairwise _) (fun i _ => hd i),
        hpartial]

/-- app0:320: the finite sum of weighted restricted measures, not withDensity. -/
noncomputable def manuscriptSimpleMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : SimpleFunc Ω ℝ≥0∞) : Measure Ω :=
  ∑ a ∈ s.range, a • μ.restrict (s ⁻¹' {a})

theorem manuscript_simple_measure_formula {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : SimpleFunc Ω ℝ≥0∞) (A : Set Ω) (hA : MeasurableSet A) :
    manuscriptSimpleMeasure μ s A = ∑ a ∈ s.range, a * μ (s ⁻¹' {a} ∩ A) := by
  simp [manuscriptSimpleMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.restrict_apply hA, Set.inter_comm]

/-- app0:345: common finite partition by the pair of simple functions. -/
theorem manuscript_simple_integral_add {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : SimpleFunc Ω ℝ≥0∞) :
    (f + g).lintegral μ = f.lintegral μ + g.lintegral μ := by
  calc
    (f + g).lintegral μ = ∑ x ∈ (SimpleFunc.pair f g).range,
        (x.1 * μ (SimpleFunc.pair f g ⁻¹' {x}) + x.2 * μ (SimpleFunc.pair f g ⁻¹' {x})) := by
      rw [SimpleFunc.add_eq_map₂, SimpleFunc.map_lintegral]
      exact Finset.sum_congr rfl (fun x _ => add_mul _ _ _)
    _ = (∑ x ∈ (SimpleFunc.pair f g).range, x.1 * μ (SimpleFunc.pair f g ⁻¹' {x})) +
        (∑ x ∈ (SimpleFunc.pair f g).range, x.2 * μ (SimpleFunc.pair f g ⁻¹' {x})) :=
      Finset.sum_add_distrib
    _ = f.lintegral μ + g.lintegral μ := by
      rw [← SimpleFunc.map_lintegral, ← SimpleFunc.map_lintegral]
      rfl

/-- Monotonicity on the same common partition. -/
theorem manuscript_simple_integral_mono {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : SimpleFunc Ω ℝ≥0∞) (h : ∀ x, f x ≤ g x) :
    f.lintegral μ ≤ g.lintegral μ := by
  change ((SimpleFunc.pair f g).map Prod.fst).lintegral μ ≤
    ((SimpleFunc.pair f g).map Prod.snd).lintegral μ
  rw [SimpleFunc.map_lintegral, SimpleFunc.map_lintegral]
  apply Finset.sum_le_sum
  intro a ha
  obtain ⟨x, rfl⟩ := SimpleFunc.mem_range.mp ha
  exact mul_le_mul_left (h x) _

end Asakura
