import AllHolderExponents

open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace Asakura

/-- Arbitrarily high moment estimates yield every Holder exponent below H. -/
theorem power_moment_holder {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (X : UnitCube 1 → Ω → ℝ)
    (hX : ∀ t, Measurable (X t)) (hcont : ∀ ω, Continuous (fun t => X t ω))
    (H : ℝ)
    (hbound : ∀ p : ℝ≥0, 1 ≤ p → ∃ c : ℝ, 0 ≤ c ∧ ∀ s t,
      eLpNorm (X s - X t) p P ≤ ENNReal.ofReal (c * (dist s t)^H)) :
    ∀ᵐ ω ∂P, ∀ α : ℝ, 0 ≤ α → α < H →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s t,
        dist (X s ω) (X t ω) ≤ C * (dist s t)^α := by
  apply holder_all_exponents_common_event P X H
    (fun s t => cube_diameter 1 s.val t.val s.property t.property)
  intro α hα hαH
  obtain ⟨n,hn⟩ := exists_nat_gt (max 1 (1 / (H - α)))
  have hn1 : (1 : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hn0 : (0 : ℝ) < n := by linarith
  have he : α < H - 1 / (n : ℝ) := by
    have hn' : 1 / (H - α) < (n : ℝ) := (le_max_right _ _).trans_lt hn
    have hh := (div_lt_iff₀ (by linarith : (0 : ℝ) < H - α)).mp hn'
    have hi : 1 / (n : ℝ) < H - α := (div_lt_iff₀ hn0).mpr (by nlinarith)
    linarith
  have hp : (1 : ℝ≥0) ≤ n := by exact_mod_cast hn1.le
  obtain ⟨c,hc,hb⟩ := hbound n hp
  obtain ⟨Y,M,hYm,hYc,hYX,hMm,hM0,hYH,_⟩ :=
    kolmogorov_cube_holder P X hX (n : ℝ≥0) hp c (H - 1/(n:ℝ)) α hc hα he
      (by simpa only [NNReal.coe_natCast, Nat.cast_one, sub_add_cancel] using hb)
  have heq : ∀ᵐ ω ∂P, (fun t => Y t ω) = (fun t => X t ω) :=
    continuous_modifications_agree P (DyadicSet 1) (dyadicSet_dense 1)
      (dyadicSet_countable 1) Y X (Eventually.of_forall hYc) (Eventually.of_forall hcont) hYX
  filter_upwards [heq] with ω hω
  refine ⟨M ω,hM0 ω,?_⟩
  intro s t
  simpa only [congrFun hω s,congrFun hω t] using hYH ω s t
end Asakura
