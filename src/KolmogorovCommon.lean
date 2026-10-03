import KolmogorovCube
import HolderSeminorm
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace Asakura

/-- C.2: a SINGLE continuous modification works for every admissible exponent,
with a measurable supremum over all pairs of cube points and its Lp bound. -/
theorem kolmogorov_cube_common_version {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : UnitCube d → Ω → ℝ) (hX : ∀ s, Measurable (X s))
    (p : ℝ≥0) (hp : 1 ≤ p) (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε)
    (h : ∀ s t, eLpNorm (X s - X t) p μ ≤
      ENNReal.ofReal (c * (dist s t)^(ε + d/(p:ℝ)))) :
    ∃ Y : UnitCube d → Ω → ℝ,
      (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∀ t, Y t =ᵐ[μ] X t) ∧
      ∀ α : ℝ, 0 < α → α < ε →
        Measurable (fun ω => holderSup (fun t => Y t ω) α) ∧
        eLpNorm (fun ω => holderSup (fun t => Y t ω) α) p μ ≤ ENNReal.ofReal
          ((2 * 2^α) * ((c * (6:ℝ)^(d/(p:ℝ))) / (1 - 2^α * 2^(-ε)))) := by
  obtain ⟨Y,M,hYm,hYc,hYX,hMm,hM0,hYH,hMbound⟩ :=
    kolmogorov_cube_holder μ X hX p hp c ε (ε/2) hc (by linarith) (by linarith) h
  refine ⟨Y,hYm,hYc,hYX,?_⟩
  intro α hα hαε
  have hsupm := holderSup_process_measurable (DyadicSet d) (dyadicSet_dense d)
    (dyadicSet_countable d) Y hYm hYc α hα
  refine ⟨hsupm, ?_⟩
  obtain ⟨Z,N,hZm,hZc,hZX,hNm,hN0,hZH,hNbound⟩ :=
    kolmogorov_cube_holder μ X hX p hp c ε α hc hα hαε h
  have heq : ∀ᵐ ω ∂μ, (fun t => Y t ω) = (fun t => Z t ω) :=
    continuous_modifications_agree μ (DyadicSet d) (dyadicSet_dense d)
      (dyadicSet_countable d) Y Z (Filter.Eventually.of_forall hYc)
      (Filter.Eventually.of_forall hZc) (fun t => (hYX t).trans (hZX t).symm)
  apply le_trans (eLpNorm_mono_enorm_ae hsupm.aestronglyMeasurable ?_) hNbound
  filter_upwards [heq] with ω hω
  rw [enorm_eq_self, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hN0 ω), hω]
  exact holderSup_le_of_bound (fun t => Z t ω) α (N ω) hα (hN0 ω) (hZH ω)
end Asakura
