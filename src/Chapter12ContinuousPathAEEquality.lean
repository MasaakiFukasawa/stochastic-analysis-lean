import Chapter12CylinderAllSobolevOrders
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Bases

open MeasureTheory TopologicalSpace
namespace Asakura.Chapter12

theorem continuous_path_ae_equality {Ω K E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace K] [SeparableSpace K] [Nonempty K]
    [TopologicalSpace E] [T2Space E]
    (P : Measure Ω) (X Y : Ω → C(K,E))
    (h : ∀t,(fun w => X w t)=ᵐ[P] (fun w => Y w t)) : X=ᵐ[P] Y := by
  obtain ⟨t,ht⟩ := TopologicalSpace.exists_dense_seq (α:=K)
  filter_upwards [ae_all_iff.mpr (fun n => h (t n))] with w hw
  apply ContinuousMap.ext
  exact congrFun (ht.equalizer (X w).continuous (Y w).continuous (funext hw))
end Asakura.Chapter12
#print axioms Asakura.Chapter12.continuous_path_ae_equality
