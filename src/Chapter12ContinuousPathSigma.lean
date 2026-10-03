import Chapter12BrownianBridge

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- Passing from all evaluations to the Borel sigma-algebra of a continuous
path introduces no new information. -/
theorem continuous_path_sigma {Ω K : Type*} [TopologicalSpace K]
    [SecondCountableTopology K] [LocallyCompactSpace K]
    (X : Ω → C(K,ℝ)) :
    MeasurableSpace.comap X inferInstance =
      MeasurableSpace.comap (fun w t => X w t) inferInstance := by
  apply le_antisymm
  · letI : MeasurableSpace Ω := MeasurableSpace.comap (fun w t => X w t) inferInstance
    apply Measurable.comap_le
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (measurable_pi_apply t).comp
      (Measurable.of_comap_le (f := fun w t => X w t) le_rfl)
  · letI : MeasurableSpace Ω := MeasurableSpace.comap X inferInstance
    apply Measurable.comap_le
    exact Measurable.of_eval fun t => (ContinuousMap.measurable_eval t).comp
      (Measurable.of_comap_le (f := X) le_rfl)

/-- The independence just proved for every bridge coordinate is independence
of the bridge as a continuous-path-valued random variable. -/
theorem bridge_path_terminal_independent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (hT : 0 < T)
    (X B : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X) (hXg : HasGaussianLaw X P)
    (hcov : ∀ s : Icc (0:ℝ) T,
      cov[(fun w => X w ⟨T,hT.le,le_rfl⟩),(fun w => X w s); P] = s.val)
    (hB : ∀ w s, B w s = X w s-s.val/T*X w ⟨T,hT.le,le_rfl⟩) :
    IndepFun B (fun w => X w ⟨T,hT.le,le_rfl⟩) P := by
  have hi := (bridge_terminal_independent P T hT X hXm hXg hcov).symm
  change Indep (MeasurableSpace.comap B inferInstance)
    (MeasurableSpace.comap (fun w => X w ⟨T,hT.le,le_rfl⟩) inferInstance) P
  rw [continuous_path_sigma B]
  change Indep (MeasurableSpace.comap
    (fun w (s : Icc (0:ℝ) T) => X w s-s.val/T*X w ⟨T,hT.le,le_rfl⟩) inferInstance)
    (MeasurableSpace.comap (fun w => X w ⟨T,hT.le,le_rfl⟩) inferInstance) P at hi
  simpa only [hB] using hi

end Asakura.Chapter12
