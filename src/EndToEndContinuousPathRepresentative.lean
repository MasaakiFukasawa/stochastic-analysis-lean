import EndToEndLpRepresentative
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.DenseEmbedding

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
namespace Asakura.EndToEnd
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Joint continuous-path representatives are recovered from countably many
L2 coordinates. Continuity holds for every path of the constructed map. -/
theorem continuous_path_joint_representative
    {E Ω K : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    [TopologicalSpace K] [CompactSpace K] [T2Space K] [SecondCountableTopology K] [Nonempty K]
    (P : Measure Ω) (N : E → K → Ω → ℝ)
    (hc : ∀ x w, Continuous (fun t => N x t w))
    (hLp : ∀ x t, MemLp (N x t) 2 P)
    (hs : ∀ t, StronglyMeasurable (fun x => (hLp x t).toLp (N x t))) :
    ∃ R : E × Ω → C(K,ℝ), Measurable R ∧
      ∀ x, ∀ᵐ w ∂P, ∀ t, R (x,w) t=N x t w := by
  classical
  let q := denseSeq K
  let J : C(K,ℝ) → ℕ → ℝ := fun f n => f (q n)
  have hJc : Continuous J := continuous_pi (fun n => continuous_eval_const (q n))
  have hJi : Function.Injective J := by
    intro f g he
    apply ContinuousMap.coe_injective
    apply (denseRange_denseSeq K).equalizer f.continuous g.continuous
    exact he
  have hJ := hJc.measurableEmbedding hJi
  obtain ⟨D,hDm,hD⟩ := hJ.exists_measurable_extend (g := id) measurable_id
    (fun _ => ⟨0⟩)
  have hcoord n := lp_joint_representative P
    (fun x => (hLp x (q n)).toLp (N x (q n))) (hs (q n))
  choose G hGm hGe using hcoord
  let V : E × Ω → ℕ → ℝ := fun z n => G n z
  refine ⟨fun z => D (V z),hDm.comp (measurable_pi_iff.mpr hGm),?_⟩
  intro x
  have he n : ∀ᵐ w ∂P, G n (x,w)=N x (q n) w :=
    (hGe n x).symm.trans (hLp x (q n)).coeFn_toLp
  filter_upwards [ae_all_iff.mpr he] with w hw
  let f : C(K,ℝ) := ⟨fun t => N x t w,hc x w⟩
  have hV : V (x,w)=J f := funext hw
  intro t
  change D (V (x,w)) t = f t
  rw [hV]
  exact congrArg (fun h : C(K,ℝ) => h t) (congrFun hD f)

#print axioms continuous_path_joint_representative
end Asakura.EndToEnd
