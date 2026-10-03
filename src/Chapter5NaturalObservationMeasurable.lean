import Chapter5NaturalMartingaleRepresentation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete

/-- Explicit use of the appendix's measurable representative lemma for
a single terminal variable in the null-augmented Brownian filtration. -/
theorem natural_observation_aestronglyMeasurable
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (W : ClosedTime T → Ω → ℝ) (t : ClosedTime T) (ht : t<⊤)
    (hFnat : F t=Asakura.nullAugmentation (m := m) P (pastSigma W t))
    (X : Ω → ℝ) (hX : Measurable[F t] X) :
    AEStronglyMeasurable[MeasurableSpace.comap
      (fun w (s : Σ _ : Fin 1,{r : ℝ // 0≤r ∧ (r:EReal)<T}) => W (realTimeClamp s.2.val) w) inferInstance] X P := by
  let K := Σ _ : Fin 1,{r : ℝ // 0≤r ∧ (r:EReal)<T}
  let G := MeasurableSpace.comap (fun w (s : K) => W (realTimeClamp s.2.val) w) inferInstance
  have hpast : pastSigma W t≤G := by
    apply iSup_le
    intro r
    obtain ⟨s,hs,hsT,he⟩ := finite_closed_time_real r.val (r.property.trans_lt ht)
    rw [← he]
    apply Measurable.comap_le
    exact (measurable_pi_apply (⟨0,⟨s,hs,hsT⟩⟩ : K)).comp
      (Measurable.of_comap_le (f := fun w (s : K) => W (realTimeClamp s.2.val) w) le_rfl)
  have haug : F t≤Asakura.nullAugmentation (m := m) P G := by
    rw [hFnat]
    exact null_augmentation_mono (m := m) P hpast
  obtain ⟨g,hg,he⟩ := Asakura.nullAugmentation_real_version (m := m) P G X (hX.mono haug le_rfl)
  exact hg.stronglyMeasurable.aestronglyMeasurable.congr he.symm

end Asakura.Chapter5
