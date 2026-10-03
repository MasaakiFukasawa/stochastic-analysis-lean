import Chapter7NaturalBrownianSystem
import Chapter2LocalNullModification
import Chapter2LocalCovarianceAE

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2200000

/-- Removing one common measurable null set from the Brownian coordinates
preserves their actual local-martingale and covariance characterization. -/
noncomputable def zeroOnNullBrownian
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) (N : Set Ω) (hm : MeasurableSet[m] N) (hz : P N = 0) :
    BrownianSystem P 1 := by
  classical
  have hN t := B.null t N hm hz
  have hn : ∀ᵐ w ∂P,w ∉ N := by simpa [ae_iff] using hz
  let Y := fun j t w => if w ∈ N then 0 else B.W j t w
  have hY j : LocalMProcessWitness P B.F (Y j) :=
    local_martingale_null_modification P B.F N hN hz (B.W j) (B.martingale j)
  have he j : ∀ᵐ w ∂P,∀ t,t < ⊤ → B.W j t w = Y j t w :=
    hn.mono fun w hw t _ => (if_neg hw).symm
  exact {
    F := B.F
    mono := B.mono
    le := B.le
    null := B.null
    W := Y
    C := B.C
    martingale := hY
    cov := fun j k => LocalCovarianceWitness.congr_ae_processes P B.F B.mono B.le
      (B.martingale j) (B.martingale k) (hY j) (hY k) (B.cov j k) (he j) (he k)
    clock := B.clock }

end Asakura.Chapter7
