import PowerMomentHolder

open MeasureTheory
open scoped NNReal ENNReal Topology
namespace Asakura

theorem power_moment_cube_modification {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (X : UnitCube 1 → Ω → ℝ) (hX : ∀ t, Measurable (X t))
    (H : ℝ) (hH : 0 < H)
    (hbound : ∀ p : ℝ≥0, 1 ≤ p → ∃ c : ℝ, 0 ≤ c ∧ ∀ s t,
      eLpNorm (X s-X t) p P ≤ ENNReal.ofReal (c*(dist s t)^H)) :
    ∃ Y : UnitCube 1 → Ω → ℝ,
      (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∀ t, Y t =ᵐ[P] X t) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max 1 (2/H))
  have hn1 : (1:ℝ) < n := (le_max_left _ _).trans_lt hn
  have hn0 : (0:ℝ) < n := by linarith
  have hn' : 2/H < (n:ℝ) := (le_max_right _ _).trans_lt hn
  have hnH := (div_lt_iff₀ hH).mp hn'
  have he : H/2 < H-1/(n:ℝ) := by
    have hi : 1/(n:ℝ) < H/2 := (div_lt_iff₀ hn0).mpr (by nlinarith)
    linarith
  have hp : (1:ℝ≥0) ≤ n := by exact_mod_cast hn1.le
  obtain ⟨c,hc,hb⟩ := hbound n hp
  obtain ⟨Y,M,hYm,hYc,hYX,_⟩ := kolmogorov_cube_holder P X hX (n:ℝ≥0) hp
    c (H-1/(n:ℝ)) (H/2) hc (by positivity) he
    (by simpa only [NNReal.coe_natCast,Nat.cast_one,sub_add_cancel] using hb)
  exact ⟨Y,hYm,hYc,hYX⟩
end Asakura
