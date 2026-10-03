import Chapter12BoundedLpConvergence

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- Truncation preserves the generating information, is bounded, and converges
in every finite Lp. This supplies the unbounded step in cylinder density. -/
theorem bounded_truncations_Lp {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ m)
    (f : Ω → ℝ) (hf : AEStronglyMeasurable[G] f P)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞) (hi : MemLp f p P) :
    ∃ v : ℕ → Ω → ℝ,
      (∀ n, StronglyMeasurable[G] (v n)) ∧
      (∀ n w, |v n w| ≤ (n : ℝ)) ∧
      Tendsto (fun n => eLpNorm (v n-f) p P) atTop (𝓝 0) := by
  let g := hf.mk f
  have hgm : StronglyMeasurable[G] g := hf.stronglyMeasurable_mk
  have hgi : MemLp g p P := hi.ae_eq hf.ae_eq_mk
  let v := fun n : ℕ => {w | |g w| ≤ (n : ℝ)}.indicator g
  have hvm : ∀ n, StronglyMeasurable[G] (v n) := fun n =>
    hgm.indicator (measurableSet_le (by simpa only [Real.norm_eq_abs] using hgm.measurable.norm) measurable_const)
  have hvb : ∀ n w, |v n w| ≤ (n : ℝ) := by
    intro n w
    by_cases hw : |g w| ≤ (n : ℝ)
    · simpa [v,Set.indicator,hw] using hw
    · simp [v,Set.indicator,hw]
  have hvi : UnifIntegrable v p P :=
    (unifIntegrable_const hp hpt hgi).ae_mono
      (fun n => ((hvm n).mono hG).aestronglyMeasurable) (fun n => by
        exact ae_of_all _ fun w => by
          by_cases hw : |g w| ≤ (n : ℝ)
          · simp [v,Set.indicator,hw]
          · simp [v,Set.indicator,hw])
  have hlim : ∀ᵐ w ∂P, Tendsto (fun n => v n w) atTop (𝓝 (g w)) := by
    apply ae_of_all
    intro w
    obtain ⟨N,hN⟩ := exists_nat_ge |g w|
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hw : |g w| ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
    simp [v,Set.indicator,hw]
  have ht := tendsto_Lp_finite_of_tendsto_ae hp hpt
    (fun n => ((hvm n).mono hG).aestronglyMeasurable) hgi hvi hlim
  refine ⟨v,hvm,hvb,?_⟩
  have he : ∀ n, eLpNorm (v n-f) p P = eLpNorm (v n-g) p P := fun n =>
    eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hf.ae_eq_mk)
  simpa only [he] using ht

end Asakura.Chapter12
