import Chapter5MartingaleRepresentationConstructed
import FullAuditNaturalFiltration
import MeasurableVersion

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

/-- The measurable-function representative lemma from the appendix
supplies the Brownian observation measurability; this is no longer an
extra input to the martingale representation theorem. -/
theorem natural_brownian_martingale_representation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (W A : ClosedTime T → Ω → ℝ)
    (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (c : ℕ → ℝ) (hc : ∀ j,0<c j) (hcm : StrictMono c) (hcT : ∀ j,(c j:EReal)<T)
    (hct : StrictMono (fun j => realTimeClamp (T := T) (c j)))
    (hcut : ∀ j,realTimeClamp (T := T) (c j)<⊤)
    (hcc : ∀ t,t<⊤ → ∃ j,t<realTimeClamp (T := T) (c j))
    (hco : ∀ r,∃ j,r≤c j)
    (hFnat : ∀ t,t<⊤ → F t=Asakura.nullAugmentation (m := m) P (pastSigma W t))
    (Y : ClosedTime T → Ω → ℝ)
    (hYm : ∀ t,t<⊤ → Measurable[F t] (Y t))
    (hY2 : ∀ t,t<⊤ → MemLp (Y t) 2 P)
    (hY : ∀ s t,t<⊤ → s≤t → P[Y t|F s] =ᵐ[P] Y s) :
    ∃ G : Ω × ℝ → ℝ,∃ J : ClosedTime T → Ω → ℝ,
      Measurable G ∧
      (∀ l,@Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c l) => F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) (c l) => G (z.1,z.2.val))) ∧
      LocalMProcessWitness P F J ∧ ItoCovarianceFormula P F W G J ∧
      (∀ R : ℝ,MemLp G 2 (P.prod (volume.restrict (Ioc 0 R)))) ∧
      ∀ t,t<⊤ → Y t =ᵐ[P] fun w => Y ⊥ w+J t w := by
  have hgen : ∀ t,t<⊤ → ∀ X : Ω → ℝ,Measurable[F t] X →
      AEStronglyMeasurable[MeasurableSpace.comap
        (fun w (s : Σ _ : Fin 1,{r : ℝ // 0≤r ∧ (r:EReal)<T}) => W (realTimeClamp s.2.val) w) inferInstance] X P := by
    intro t ht X hX
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
      rw [hFnat t ht]
      exact null_augmentation_mono (m := m) P hpast
    obtain ⟨g,hg,he⟩ := Asakura.nullAugmentation_real_version (m := m) P G X (hX.mono haug le_rfl)
    exact hg.stronglyMeasurable.aestronglyMeasurable.congr he.symm
  exact brownian_martingale_representation_constructed P hT F hF hle hnull W A hW hA hclock
    c hc hcm hcT hct hcut hcc hco hgen Y hYm hY2 hY

end Asakura.Chapter5
