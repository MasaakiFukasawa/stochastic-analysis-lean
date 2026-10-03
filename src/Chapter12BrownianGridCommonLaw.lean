import Chapter6GridPrefix
import Chapter7BrownianPathLaw

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter6 Asakura.Chapter7
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem brownian_grid_common_law {Ω Ω' I:Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype I]
    (P:Measure Ω) (Q:Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d:ℕ} (B:BrownianSystem P d) (C:BrownianSystem Q d)
    (h:ℝ) (hh:0≤h) (k:I → ℕ) (j:I → Fin d) :
    IdentDistrib (fun w i => B.W (j i) (realTimeClamp ((k i:ℝ)*h)) w)
      (fun w i => C.W (j i) (realTimeClamp ((k i:ℝ)*h)) w) P Q := by
  classical
  let N := Finset.univ.sup k
  have hk i:k i≤N := Finset.le_sup (f:=k) (Finset.mem_univ i)
  let L:(Fin N → Fin d → ℝ) →L[ℝ] (I → ℝ) := ContinuousLinearMap.pi (fun i => gridPrefix (k i) (j i))
  obtain ⟨hm,hchar,_⟩ := B.grid_law h hh N
  obtain ⟨hm',hchar',_⟩ := C.grid_law h hh N
  have hl:IdentDistrib (finiteNoiseGrid (fun j r => B.W j (realTimeClamp r)) h N)
      (finiteNoiseGrid (fun j r => C.W j (realTimeClamp r)) h N) P Q :=
    ⟨hm.aemeasurable,hm'.aemeasurable,Measure.ext_of_charFunDual (hchar.trans hchar'.symm)⟩
  have hf := hl.comp L.continuous.measurable
  have he:(fun w => L (finiteNoiseGrid (fun j r => B.W j (realTimeClamp r)) h N w))=ᵐ[P]
      (fun w i => B.W (j i) (realTimeClamp ((k i:ℝ)*h)) w) := by
    filter_upwards [ae_all_iff.mpr (fun i => gridPrefix_brownian_sample P B h (k i) (hk i) (j i))] with w hw
    exact funext hw
  have he':(fun w => L (finiteNoiseGrid (fun j r => C.W j (realTimeClamp r)) h N w))=ᵐ[Q]
      (fun w i => C.W (j i) (realTimeClamp ((k i:ℝ)*h)) w) := by
    filter_upwards [ae_all_iff.mpr (fun i => gridPrefix_brownian_sample Q C h (k i) (hk i) (j i))] with w hw
    exact funext hw
  exact (IdentDistrib.of_ae_eq hf.aemeasurable_fst he).symm.trans
    (hf.trans (IdentDistrib.of_ae_eq hf.aemeasurable_snd he'))
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_grid_common_law
