import Chapter12BoundedCylinderDensity
import Chapter12LpTruncation
import Chapter5ContinuousCylinderSigma

open MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- All finite Lp: truncate, use increasing conditional expectations, then
smooth in the actual finite-dimensional distribution. -/
theorem cylinder_Lp_density {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
    [∀ n, FiniteDimensional ℝ (E n)] [∀ n, MeasurableSpace (E n)]
    [∀ n, BorelSpace (E n)]
    (X : (n : ℕ) → Ω → E n) (hX : ∀ n, Measurable (X n))
    (hmono : Monotone (fun n => MeasurableSpace.comap (X n) inferInstance))
    (f : Ω → ℝ)
    (hf : AEStronglyMeasurable[⨆ n, MeasurableSpace.comap (X n) inferInstance] f P)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤) (hi : MemLp f p P)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (g : E n → ℝ), HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      eLpNorm (fun w => f w-g (X n w)) p P < ENNReal.ofReal ε := by
  let G := ⨆ n, MeasurableSpace.comap (X n) inferInstance
  have hG : G ≤ m := iSup_le fun n => (hX n).comap_le
  obtain ⟨v,hvm,hvb,hvt⟩ := bounded_truncations_Lp P G hG f hf p hp hpt hi
  obtain ⟨k,hk⟩ := (hvt.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr (half_pos hε)))).exists
  have hvi : MemLp (v k) 2 P := MemLp.of_bound
    ((hvm k).mono hG).aestronglyMeasurable k
    (ae_of_all _ fun w => by simpa only [Real.norm_eq_abs] using hvb k w)
  let U := hvi.toLp (v k)
  have hUm : AEStronglyMeasurable[G] U P :=
    (hvm k).aestronglyMeasurable.congr hvi.coeFn_toLp.symm
  have hUb : ∀ᵐ w ∂P, |U w| ≤ (k : ℝ) := by
    filter_upwards [hvi.coeFn_toLp] with w hw
    rw [hw]; exact hvb k w
  obtain ⟨n,g,hgc,hgd,hge⟩ := bounded_cylinder_Lp_density P E X hX hmono U hUm
    k (Nat.cast_nonneg k) hUb p hp hpt (ε/2) (half_pos hε)
  refine ⟨n,g,hgc,hgd,?_⟩
  have hu : eLpNorm (f-(U : Ω → ℝ)) p P < ENNReal.ofReal (ε/2) := by
    rw [eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hvi.coeFn_toLp),eLpNorm_sub_comm]
    exact hk
  have he : (fun w => f w-g (X n w)) =
      (f-(U : Ω → ℝ))+(fun w => U w-g (X n w)) := by funext w; simp
  rw [he]
  calc
    _ ≤ eLpNorm (f-(U : Ω → ℝ)) p P + eLpNorm (fun w => U w-g (X n w)) p P := eLpNorm_add_le hp
    _ < ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) :=
      ENNReal.add_lt_add_of_lt_of_le (ne_top_of_lt hge) hu hge.le
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]; congr 1; ring

/-- Continuity supplies the countable generating information, so no separate
sigma-algebra generation hypothesis is needed for the Brownian application. -/
theorem continuous_process_cylinder_Lp_density {Ω K E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace K] [FirstCountableTopology K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : K → Ω → E) (hWm : ∀ t, Measurable (W t))
    (hWc : ∀ w, Continuous (fun t => W t w))
    (q : ℕ → K) (hq : DenseRange q) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable[MeasurableSpace.comap (fun w t => W t w) inferInstance] f P)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤) (hi : MemLp f p P)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (g : (Fin n → E) → ℝ), HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      eLpNorm (fun w => f w-g (fun i => W (q i) w)) p P < ENNReal.ofReal ε := by
  have he := Asakura.Chapter5.continuous_process_countable_sigma W hWc q hq
  rw [he,← Asakura.Chapter5.prefix_coordinate_sigma (fun n => W (q n))] at hf
  exact cylinder_Lp_density P (fun n => Fin n → E) (fun n w i => W (q i) w)
    (fun n => Measurable.of_eval fun i => hWm (q i))
    (Asakura.Chapter5.prefix_coordinate_monotone (fun n => W (q n))) f hf p hp hpt hi ε hε

end Asakura.Chapter12
