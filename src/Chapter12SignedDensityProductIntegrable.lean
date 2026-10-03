import Chapter12SignedDensityVariation

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem signed_density_product_integrable {S : Type*} [MeasurableSpace S]
    (ν : SignedMeasure S) (g h : S → ℝ) (hg : Measurable g) (hh : Measurable h)
    (hgi : Integrable g ν.totalVariation)
    (hhi : Integrable h (signedWeighted ν g).totalVariation) :
    Integrable (fun x => h x*g x) ν.totalVariation := by
  rw [signed_weighted_totalVariation ν g hgi] at hhi
  have hi := (integrable_withDensity_iff_integrable_smul' hg.enorm
    (ae_of_all _ (fun x => enorm_lt_top))).mp hhi
  apply Integrable.mono' hi.norm (hh.mul hg).aestronglyMeasurable
  exact ae_of_all _ (fun x => by simp [norm_mul,mul_comm])

end Asakura.Chapter12
#print axioms Asakura.Chapter12.signed_density_product_integrable
