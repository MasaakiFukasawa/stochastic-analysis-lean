import KolmogorovConstant
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace Asakura

/-- Appendix C, Theorem C.2.1: one continuous modification, every positive
admissible Holder exponent, measurable full supremum, and the printed bound.
The real-valued p >= 1 is represented as a nonnegative real p in Lean.
The dimension is positive, as for the manuscript's maximum over 1,...,d. -/
theorem kolmogorov_continuity {d : ℕ} (hd : 1 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
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
          ((2*c / (2^(-α)-2^(-ε))) * (6 * Real.sqrt d)^(ε+d/(p:ℝ))) := by
  obtain ⟨Y,hYm,hYc,hYX,hYH⟩ := kolmogorov_cube_common_version μ X hX p hp c ε hc hε h
  refine ⟨Y,hYm,hYc,hYX,?_⟩
  intro α hα hαε
  refine ⟨(hYH α hα hαε).1, (hYH α hα hαε).2.trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  exact kolmogorov_printed_constant d hd (p:ℝ) c ε α
    (by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℝ≥0)<1) hp)) hc hε hαε

/-- The final sentence of C.2.1: for an already continuous process, no change
of process is needed, and the same supremum estimate holds. -/
theorem kolmogorov_already_continuous {d : ℕ} (hd : 1 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : UnitCube d → Ω → ℝ) (hX : ∀ s, Measurable (X s))
    (hcont : ∀ ω, Continuous (fun t => X t ω))
    (p : ℝ≥0) (hp : 1 ≤ p) (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε)
    (h : ∀ s t, eLpNorm (X s - X t) p μ ≤
      ENNReal.ofReal (c * (dist s t)^(ε + d/(p:ℝ)))) :
    ∀ α : ℝ, 0 < α → α < ε →
      Measurable (fun ω => holderSup (fun t => X t ω) α) ∧
      eLpNorm (fun ω => holderSup (fun t => X t ω) α) p μ ≤ ENNReal.ofReal
        ((2*c / (2^(-α)-2^(-ε))) * (6 * Real.sqrt d)^(ε+d/(p:ℝ))) := by
  obtain ⟨Y,hYm,hYc,hYX,hYH⟩ := kolmogorov_continuity hd μ X hX p hp c ε hc hε h
  have heq : ∀ᵐ ω ∂μ, (fun t => Y t ω) = (fun t => X t ω) :=
    continuous_modifications_agree μ (DyadicSet d) (dyadicSet_dense d)
      (dyadicSet_countable d) Y X (Filter.Eventually.of_forall hYc)
      (Filter.Eventually.of_forall hcont) hYX
  intro α hα hαε
  refine ⟨holderSup_process_measurable (DyadicSet d) (dyadicSet_dense d)
    (dyadicSet_countable d) X hX hcont α hα, ?_⟩
  have hnorm : eLpNorm (fun ω => holderSup (fun t => X t ω) α) p μ =
      eLpNorm (fun ω => holderSup (fun t => Y t ω) α) p μ := by
    apply eLpNorm_congr_ae
    filter_upwards [heq] with ω hω
    rw [hω]
  rw [hnorm]
  exact (hYH α hα hαε).2
end Asakura
