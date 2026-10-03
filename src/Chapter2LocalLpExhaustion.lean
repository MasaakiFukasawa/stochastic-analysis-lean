import Chapter2LocalLpQuotient

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem local_lp_cofinal_convergence {S I : Type*} [MeasurableSpace S]
    (μ : Measure S) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : ℕ → Set S) (B : I → Set S)
    (hKB : ∀ j, ∃ i, K j ⊆ B i) (hBK : ∀ i, ∃ j, B i ⊆ K j)
    (f : ℕ → S → ℝ) (g : S → ℝ)
    (hf : ∀ n j, MemLp (f n) p (μ.restrict (K j)))
    (hg : ∀ j, MemLp g p (μ.restrict (K j))) :
    Tendsto (fun n => localLpDistance μ p K (f n) g (hf n) hg) atTop (𝓝 0) ↔
    ∀ i, Tendsto (fun n => (eLpNorm (f n-g) p (μ.restrict (B i))).toReal) atTop (𝓝 0) := by
  have hnorm : ∀ j, (fun n => dist ((hf n j).toLp (f n)) ((hg j).toLp g)) =
      (fun n => (eLpNorm (f n-g) p (μ.restrict (K j))).toReal) := by
    intro j; funext n; rw [dist_edist,Lp.edist_toLp_toLp]
  have hsmall {C D : Set S} (hCD : C ⊆ D) (hD : ∀ n, MemLp (f n-g) p (μ.restrict D))
      (hlim : Tendsto (fun n => (eLpNorm (f n-g) p (μ.restrict D)).toReal) atTop (𝓝 0)) :
      Tendsto (fun n => (eLpNorm (f n-g) p (μ.restrict C)).toReal) atTop (𝓝 0) := by
    exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n =>
      ENNReal.toReal_mono (hD n).eLpNorm_lt_top.ne
        (eLpNorm_mono_measure _ (Measure.restrict_mono hCD le_rfl))) hlim
  change Tendsto (fun n => countableDistance _ _) _ _ ↔ _
  rw [countable_distance_convergence_iff]
  constructor
  · intro hl i
    obtain ⟨j,hj⟩ := hBK i
    have hh := tendsto_iff_dist_tendsto_zero.mp (hl j)
    rw [hnorm j] at hh
    exact hsmall hj (fun n => (hf n j).sub (hg j)) hh
  · intro hl j
    obtain ⟨i,hi⟩ := hKB j
    obtain ⟨k,hk⟩ := hBK i
    have hBi n := ((hf n k).sub (hg k)).mono_measure (Measure.restrict_mono hk le_rfl)
    apply tendsto_iff_dist_tendsto_zero.mpr
    rw [hnorm j]
    exact hsmall hi hBi (hl i)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_lp_cofinal_convergence
