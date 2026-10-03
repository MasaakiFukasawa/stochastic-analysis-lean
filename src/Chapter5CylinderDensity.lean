import Chapter5SmoothCylinderApproximation
import Chapter1WrittenConvergence
import Mathlib.MeasureTheory.Function.FactorsThrough

open MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology
namespace Asakura.Chapter5

/-- A random variable measurable with respect to a finite vector can be
approximated in L2 by smooth functions of that same vector. -/
theorem finite_vector_smooth_L2 {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → E) (hX : Measurable X) (U : Lp ℝ 2 P)
    (hU : AEStronglyMeasurable[MeasurableSpace.comap X inferInstance] U P)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : E → ℝ) (hg : MemLp (g ∘ X) 2 P),
      HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      ‖U - hg.toLp (g ∘ X)‖ ≤ ε := by
  obtain ⟨f,hf,he⟩ := hU.stronglyMeasurable_mk.measurable.exists_eq_measurable_comp
  have hUf : (U : Ω → ℝ) =ᵐ[P] f ∘ X := by
    simpa only [he] using hU.ae_eq_mk
  have hi : MemLp (f ∘ X) 2 P := (Lp.memLp U).ae_eq hUf
  obtain ⟨g,hgc,hgd,_,hge⟩ := smooth_cylinder_approximation P X hX f hf hi ε hε
  obtain ⟨B,hB⟩ := hgc.isCompact_range hgd.continuous |>.exists_bound_of_continuousOn
    continuous_id.continuousOn
  have hgi : MemLp (g ∘ X) 2 P := MemLp.of_bound
    (hgd.continuous.measurable.comp hX).aestronglyMeasurable B
    (ae_of_all _ fun w => hB _ ⟨X w,rfl⟩)
  refine ⟨g,hgi,hgc,hgd,?_⟩
  have heq : U - hgi.toLp (g ∘ X) = (hi.sub hgi).toLp (f ∘ X - g ∘ X) := by
    rw [MemLp.toLp_sub hi hgi]
    congr 1
    exact Lp.ext (hUf.trans hi.coeFn_toLp.symm)
  rw [heq,Lp.norm_toLp]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hge).trans_eq (ENNReal.toReal_ofReal hε.le)

/-- The increasing-information step is the convex-tail proof of Chapter 1,
followed by the finite-vector approximation, not an assumed density theorem. -/
theorem cylinder_approximation_of_generating_vectors {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
    [∀ n, FiniteDimensional ℝ (E n)] [∀ n, MeasurableSpace (E n)]
    [∀ n, BorelSpace (E n)]
    (X : (n : ℕ) → Ω → E n) (hX : ∀ n, Measurable (X n))
    (hmono : Monotone (fun n => MeasurableSpace.comap (X n) inferInstance))
    (U : Lp ℝ 2 P)
    (hU : AEStronglyMeasurable[⨆ n, MeasurableSpace.comap (X n) inferInstance] U P)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (g : E n → ℝ) (hg : MemLp (g ∘ X n) 2 P),
      HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧ ‖U - hg.toLp (g ∘ X n)‖ < ε := by
  let G := fun n => MeasurableSpace.comap (X n) inferInstance
  have hle : ∀ n, G n ≤ m := fun n => (hX n).comap_le
  have htop : (⨆ n, G n) ≤ m := iSup_le hle
  letI : Fact ((⨆ n, G n) ≤ m) := ⟨htop⟩
  have he : (condExpL2 ℝ ℝ htop U : Lp ℝ 2 P) = U :=
    (lpMeas ℝ ℝ (⨆ n, G n) 2 P).starProjection_eq_self_iff.mpr hU
  have ht := Asakura.Chapter1Written.conditional_upward_L2_written G hmono hle U
  rw [he] at ht
  obtain ⟨n,hn⟩ := (Metric.tendsto_atTop.mp ht) (ε/2) (by linarith)
  have hn' : ‖U - (condExpL2 ℝ ℝ (hle n) U : Lp ℝ 2 P)‖ < ε/2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hn n le_rfl
  obtain ⟨g,hg,hgc,hgd,hge⟩ := finite_vector_smooth_L2 P (X n) (hX n)
    (condExpL2 ℝ ℝ (hle n) U) (aestronglyMeasurable_condExpL2 (hle n) U)
    (ε/2) (by linarith)
  refine ⟨n,g,hg,hgc,hgd,?_⟩
  have ht := norm_sub_le_norm_sub_add_norm_sub U (condExpL2 ℝ ℝ (hle n) U : Lp ℝ 2 P) (hg.toLp (g ∘ X n))
  linarith

end Asakura.Chapter5
