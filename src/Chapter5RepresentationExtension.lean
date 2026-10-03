import Chapter5ContinuousCylinderSigma
import Chapter5RepresentationClosure

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology ContDiff
namespace Asakura.Chapter5

theorem centered_L2_is_subtract_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Lp ℝ 2 P) :
    ((U - (condExpL2 ℝ ℝ bot_le U : Lp ℝ 2 P) : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P]
      fun w => U w - ∫ z, U z ∂P := by
  have he := (Lp.memLp U).condExpL2_ae_eq_condExp (𝕜 := ℝ) bot_le
  simp only [Lp.toLp_coeFn,condExp_bot] at he
  exact (Lp.coeFn_sub U _).trans (Filter.EventuallyEq.rfl.sub he)

/-- Extension of the preceding smooth representation lemma to every
L2 payoff of the continuous process. Density is proved in the preceding
file and the centering is the actual L2 conditional-expectation projection.
Only the preceding smooth representation and the Chapter 2 isometry
remain inputs to this step of the manuscript's proof. -/
theorem representation_extension_from_smooth_lemma
    {Ω K E H : Type*} [MeasurableSpace Ω]
    [TopologicalSpace K] [FirstCountableTopology K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : K → Ω → E) (hWm : ∀ t, Measurable (W t))
    (hWc : ∀ w, Continuous (fun t => W t w))
    (q : ℕ → K) (hq : DenseRange q)
    (I : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hrep : ∀ (n : ℕ) (g : (Fin n → E) → ℝ)
      (hg : MemLp (fun w => g (fun i => W (q i) w)) 2 P),
      HasCompactSupport g → ContDiff ℝ ∞ g →
      ∃ h, I h = hg.toLp (fun w => g (fun i => W (q i) w)) -
        (condExpL2 ℝ ℝ bot_le (hg.toLp (fun w => g (fun i => W (q i) w))) : Lp ℝ 2 P))
    (U : Lp ℝ 2 P)
    (hU : AEStronglyMeasurable[MeasurableSpace.comap (fun w t => W t w) inferInstance] U P) :
    ∃! h, I h = U - (condExpL2 ℝ ℝ bot_le U : Lp ℝ 2 P) := by
  let Q : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P :=
    (lpMeas ℝ ℝ ⊥ 2 P).subtypeL.comp (condExpL2 ℝ ℝ bot_le)
  let C : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P := ContinuousLinearMap.id ℝ _ - Q
  have hclosed : IsClosed {V : Lp ℝ 2 P | C V ∈ range I} :=
    I.isometry.isClosedEmbedding.isClosed_range.preimage C.continuous
  have hmem : U ∈ closure {V : Lp ℝ 2 P | C V ∈ range I} := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨n,g,hg,hgc,hgd,hge⟩ := continuous_process_smooth_cylinder_density P W hWm hWc q hq U hU ε hε
    refine ⟨hg.toLp _,hrep n g hg hgc hgd,?_⟩
    simpa only [dist_eq_norm] using hge
  obtain ⟨h,hh⟩ := hclosed.closure_subset hmem
  refine ⟨h,hh,?_⟩
  intro k hk
  exact I.injective (hk.trans hh.symm)

end Asakura.Chapter5
