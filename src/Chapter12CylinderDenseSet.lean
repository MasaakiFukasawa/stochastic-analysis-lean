import Chapter12CylinderDensity

open MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- A class containing smooth compact cylinders is dense in Lp. This bundles
the approximation result into the dense-test hypothesis used for closability. -/
theorem cylinder_class_dense {Ω K E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace K] [FirstCountableTopology K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : K → Ω → E) (hWm : ∀ t, Measurable (W t))
    (hWc : ∀ w, Continuous (fun t => W t w))
    (q : ℕ → K) (hq : DenseRange q)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hpt : p ≠ ⊤)
    (hgen : ∀ f : Lp ℝ p P,
      AEStronglyMeasurable[MeasurableSpace.comap (fun w t => W t w) inferInstance] f P)
    (S : Set (Lp ℝ p P))
    (hS : ∀ (n : ℕ) (g : (Fin n → E) → ℝ), HasCompactSupport g → ContDiff ℝ ∞ g →
      ∀ (hi : MemLp (fun w => g (fun i => W (q i) w)) p P), hi.toLp _ ∈ S) : Dense S := by
  intro f
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨n,g,hgc,hgd,hge⟩ := continuous_process_cylinder_Lp_density P W hWm hWc q hq
    f (hgen f) p (Fact.out : 1 ≤ p) hpt (Lp.memLp f) ε hε
  obtain ⟨C,hC⟩ := hgc.isCompact_range hgd.continuous |>.exists_bound_of_continuousOn
    continuous_id.continuousOn
  have hi : MemLp (fun w => g (fun i : Fin n => W (q i) w)) p P := MemLp.of_bound
    (hgd.continuous.measurable.comp (Measurable.of_eval fun i => hWm (q i))).aestronglyMeasurable C
    (ae_of_all _ fun w => hC _ ⟨(fun i => W (q i) w),rfl⟩)
  refine ⟨hi.toLp _,hS n g hgc hgd hi,?_⟩
  rw [dist_eq_norm]
  have he : f-hi.toLp _ = ((Lp.memLp f).sub hi).toLp _ := by
    rw [MemLp.toLp_sub (Lp.memLp f) hi]
    congr 1
    exact Lp.ext (Lp.memLp f).coeFn_toLp.symm
  rw [he,Lp.norm_toLp]
  have hg' : eLpNorm ((f : Ω → ℝ)-(fun w => g (fun i : Fin n => W (q i) w))) p P < ENNReal.ofReal ε := hge
  exact (ENNReal.toReal_lt_toReal (ne_top_of_lt hg') ENNReal.ofReal_ne_top).mpr hg' |>.trans_eq
    (ENNReal.toReal_ofReal hε.le)

end Asakura.Chapter12
