import Chapter12L2SectionMap
import Chapter12FiberwiseClosedGraph
import Chapter12ConditionalPairing

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [SigmaFinite P] (ν : Measure S) [SigmaFinite ν]

noncomputable def randomSectionsIsometry :
    Lp ℝ 2 (P.prod ν) →ₗᵢ[ℝ] Lp (Lp ℝ 2 P) 2 ν :=
  (l2SectionsIsometry ν P).comp
    (Lp.compMeasurePreservingₗᵢ ℝ Prod.swap (Measure.measurePreserving_swap (μ := ν) (ν := P)))

theorem randomSectionsIsometry_coe (f : Lp ℝ 2 (P.prod ν)) :
    ∀ᵐ t ∂ν,(randomSectionsIsometry P ν f t : Ω → ℝ) =ᵐ[P] (fun w => f (w,t)) := by
  have hs := Lp.coeFn_compMeasurePreserving f
    (Measure.measurePreserving_swap (μ := ν) (ν := P))
  have hss := Measure.ae_ae_of_ae_prod hs
  have hl := l2SectionLp_coe ν P
    (Lp.compMeasurePreservingₗᵢ ℝ Prod.swap (Measure.measurePreserving_swap (μ := ν) (ν := P)) f)
  filter_upwards [hl,hss] with t ht hv
  exact ht.trans hv

end Asakura.Chapter12
