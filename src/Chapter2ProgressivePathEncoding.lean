import Chapter2ItoIntegrandEncoding
import Chapter2CumulativeAdapted

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Progressive functions need only be defined on the time domain. A
measurable extension of each path is constructed without an extra global
path-measurability assumption. -/
theorem progressive_paths_measurable_encoding
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (H : Ω × ℝ → ℝ)
    (hH : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val))) :
    ∃ G : Ω × ℝ → ℝ, (∀ ω, Measurable (fun r => G (ω,r))) ∧
      ∀ n ω r, r ∈ Icc 0 (c n) → G (ω,r) = H (ω,r) := by
  have hex (ω : Ω) : ∃ g : ℝ → ℝ, Measurable g ∧ ∀ n r, r ∈ Icc 0 (c n) → g r = H (ω,r) := by
    let f := fun n r => H (ω,(projIcc 0 (c n) (hc n) (intervalClamp 0 (c n) (hc n) r):ℝ))
    have hf n : Measurable (f n) := by
      letI : MeasurableSpace Ω := F (realTimeClamp (c n))
      have hm := progressive_clamped_measurable 0 (c n) (hc n)
        (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val)) _ (hH n) ⟨c n,right_mem_Icc.mpr (hc n)⟩
      exact hm.comp (measurable_const.prodMk measurable_id)
    have he n r (hr : r ∈ Icc 0 (c n)) : f n r = H (ω,r) := by
      dsimp only [f]
      rw [intervalClamp_eq 0 (c n) (hc n) hr,projIcc_of_mem (hc n) hr]
    obtain ⟨g,hg,hgf⟩ := exists_measurable_piecewise (fun n => Icc 0 (c n))
      (fun _ => measurableSet_Icc) f hf (fun i j hij r hr => (he i r hr.1).trans (he j r hr.2).symm)
    exact ⟨g,hg,fun n r hr => (hgf n hr).trans (he n r hr)⟩
  choose g hg he using hex
  exact ⟨fun z => g z.1 z.2,hg,fun n ω r hr => he ω n r hr⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.progressive_paths_measurable_encoding
