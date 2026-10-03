import EndToEndContinuousPathRepresentative
import EndToEndContinuousFSpace

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
namespace Asakura.EndToEnd
set_option backward.isDefEq.respectTransparency false

/-- The compact-convergence topology on real continuous paths is Polish. -/
theorem real_continuous_path_polish : PolishSpace C(ℝ,ℝ) := by
  letI := continuousFSpaceMetric (A:=ℝ) (F:=ℝ)
  letI : CompleteSpace C(ℝ,ℝ) := continuousFSpaceMetric_complete
  infer_instance

/-- A countable dense set of jointly measurable coordinates determines a
jointly measurable continuous-path realization. -/
theorem path_from_countable_coordinates
    {E Ω K : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    [TopologicalSpace K] [PolishSpace C(K,ℝ)]
    (q : ℕ → K) (hq : DenseRange q)
    (P : Measure Ω) (N : E → K → Ω → ℝ)
    (hc : ∀ x w, Continuous (fun t => N x t w))
    (G : ℕ → E × Ω → ℝ) (hG : ∀ n, Measurable (G n))
    (he : ∀ x, ∀ᵐ w ∂P, ∀ n, G n (x,w)=N x (q n) w) :
    ∃ R : E × Ω → C(K,ℝ), Measurable R ∧
      ∀ x, ∀ᵐ w ∂P, ∀ t, R (x,w) t=N x t w := by
  classical
  let J : C(K,ℝ) → ℕ → ℝ := fun f n => f (q n)
  have hJc : Continuous J := continuous_pi (fun n => continuous_eval_const (q n))
  have hJi : Function.Injective J := by
    intro f g heq
    apply ContinuousMap.coe_injective
    exact hq.equalizer f.continuous g.continuous heq
  obtain ⟨D,hDm,hD⟩ := (hJc.measurableEmbedding hJi).exists_measurable_extend
    (g := id) measurable_id (fun _ => ⟨0⟩)
  let V : E × Ω → ℕ → ℝ := fun z n => G n z
  refine ⟨fun z => D (V z),hDm.comp (measurable_pi_iff.mpr hG),?_⟩
  intro x
  filter_upwards [he x] with w hw
  let f : C(K,ℝ) := ⟨fun t => N x t w,hc x w⟩
  have hV : V (x,w)=J f := funext hw
  intro t
  change D (V (x,w)) t = f t
  rw [hV]
  exact congrArg (fun h : C(K,ℝ) => h t) (congrFun hD f)

#print axioms real_continuous_path_polish
#print axioms path_from_countable_coordinates
end Asakura.EndToEnd
