import Chapter2ProgressivePathEncoding

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option backward.isDefEq.respectTransparency false

/-- Joint measurable extension of a parameter family, from progressive
measurability on finite prefixes alone. Values on the time domain are preserved. -/
theorem parameter_progressive_measurable_encoding
    {Ω E : Type*} {m : MeasurableSpace Ω} [MeasurableSpace E]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hle : ∀ t, F t ≤ m) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (H : E × (Ω × ℝ) → ℝ)
    (hp : ∀ n, @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val)))) inferInstance
      (fun z : E × (Ω × Icc (0:ℝ) (c n)) => H (z.1,(z.2.1,z.2.2.val)))) :
    ∃ G : E × (Ω × ℝ) → ℝ, Measurable G ∧
      ∀ n x ω r, r ∈ Icc 0 (c n) → G (x,(ω,r)) = H (x,(ω,r)) := by
  let f := fun n (z : E × (Ω × ℝ)) => H (z.1,(z.2.1,(projIcc 0 (c n) (hc n) z.2.2:ℝ)))
  have hf n : Measurable (f n) := by
    letI : Fact (0 ≤ c n) := ⟨hc n⟩
    have hprod : ((inferInstance : MeasurableSpace E).prod
        (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val)))) ≤
        (inferInstance : MeasurableSpace (E × (Ω × Icc (0:ℝ) (c n)))) := by
      exact sup_le_sup le_rfl (MeasurableSpace.comap_mono
        (progressive_space_le_product _ (fun t => hle _)))
    have hmap : Measurable (fun z : E × (Ω × ℝ) => (z.1,(z.2.1,projIcc 0 (c n) (hc n) z.2.2))) :=
      measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
        (continuous_projIcc.measurable.comp (measurable_snd.comp measurable_snd)))
    exact ((hp n).mono hprod le_rfl).comp hmap
  let S := fun n => {z : E × (Ω × ℝ) | z.2.2 ∈ Icc 0 (c n)}
  have he n z (hz : z ∈ S n) : f n z = H z := by
    dsimp only [f]
    rw [projIcc_of_mem (hc n) hz]
  obtain ⟨G,hG,hGe⟩ := exists_measurable_piecewise S
    (fun n => (measurable_snd.comp measurable_snd) measurableSet_Icc) f hf
    (fun i j hij z hz => (he i z hz.1).trans (he j z hz.2).symm)
  exact ⟨G,hG,fun n x ω r hr => (hGe n hr).trans (he n _ hr)⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.parameter_progressive_measurable_encoding
