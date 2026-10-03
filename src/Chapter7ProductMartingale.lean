import Chapter7ProductConditional
import Chapter2LocalCovarianceRules

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Actual M2 martingales retain their martingale identities when an
independent filtered probability coordinate is added. -/
theorem m2_product_fst
    {Ω Γ : Type*} [m : MeasurableSpace Ω] [n : MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (H : ClosedTime T → MeasurableSpace Γ)
    (hle : ∀ t,F t ≤ m) (hHl : ∀ t,H t ≤ n)
    (X : ClosedTime T → Ω → ℝ) (hX : ContinuousM2Witness P F X) :
    ContinuousM2Witness (P.prod Q) (fun t => productSigma (F t) (H t))
      (fun t z => X t z.1) := by
  letI : MeasurableSpace Ω := m
  letI : MeasurableSpace Γ := n
  refine ⟨fun t => (hX.adapted t).comp (@measurable_fst Ω Γ (F t) (H t)),
    fun t => (hX.moment t).comp_measurePreserving measurePreserving_fst,
    fun z => hX.path z.1,?_,?_⟩
  · intro s t hst
    exact (product_conditional_fst P Q (F s) (H s) (hle s) (hHl s) (X t)
      ((hX.moment t).integrable (by norm_num))).trans
      (Measure.quasiMeasurePreserving_fst.ae (hX.martingale s t hst))
  · exact Measure.quasiMeasurePreserving_fst.ae hX.initial

/-- The original bounded localizers also work on the product space. -/
theorem local_product_fst
    {Ω Γ : Type*} [m : MeasurableSpace Ω] [n : MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (H : ClosedTime T → MeasurableSpace Γ)
    (hle : ∀ t,F t ≤ m) (hHl : ∀ t,H t ≤ n)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X) :
    LocalMProcessWitness (P.prod Q) (fun t => productSigma (F t) (H t))
      (fun t z => X t z.1) := by
  letI : MeasurableSpace Ω := m
  letI : MeasurableSpace Γ := n
  obtain ⟨τ,hs,hm,ht,hc,hb⟩ := hX.localizers
  refine ⟨fun j z => τ j z.1,fun j t => (hs j t).preimage (@measurable_fst Ω Γ (F t) (H t)),
    fun z => hm z.1,fun j z => ht j z.1,fun z => hc z.1,?_⟩
  intro j
  exact ⟨m2_product_fst P Q F H hle hHl _ (hb j).1,
    fun t => ((hb j).2 t).comp_measurePreserving measurePreserving_fst⟩

theorem variation_product_fst
    {Ω Γ : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (H : ClosedTime T → MeasurableSpace Γ)
    (A : ClosedTime T → Ω → ℝ) (hA : LocalVariationWitness F A) :
    LocalVariationWitness (fun t => productSigma (F t) (H t)) (fun t z => A t z.1) := by
  obtain ⟨τ,hs,hm,ht,hc,hb⟩ := hA.localizers
  exact ⟨fun j z => τ j z.1,fun j t => (hs j t).preimage (@measurable_fst Ω Γ (F t) (H t)),
    fun z => hm z.1,fun j z => ht j z.1,fun z => hc z.1,fun j z => hb j z.1⟩

theorem covariance_product_fst
    {Ω Γ : Type*} [m : MeasurableSpace Ω] [n : MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (H : ClosedTime T → MeasurableSpace Γ)
    (hle : ∀ t,F t ≤ m) (hHl : ∀ t,H t ≤ n)
    (X Y A : ClosedTime T → Ω → ℝ) (hA : LocalCovarianceWitness P F X Y A) :
    LocalCovarianceWitness (P.prod Q) (fun t => productSigma (F t) (H t))
      (fun t z => X t z.1) (fun t z => Y t z.1) (fun t z => A t z.1) :=
  ⟨local_product_fst P Q F H hle hHl _ hA.defect,variation_product_fst F H A hA.variation⟩

/-- Actual M2 martingales retain their martingale identities when an
independent filtered probability coordinate is added. -/
theorem m2_product_snd
    {Ω Γ : Type*} [m : MeasurableSpace Ω] [n : MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (H : ClosedTime T → MeasurableSpace Γ)
    (hle : ∀ t,F t ≤ m) (hHl : ∀ t,H t ≤ n)
    (X : ClosedTime T → Γ → ℝ) (hX : ContinuousM2Witness Q H X) :
    ContinuousM2Witness (P.prod Q) (fun t => productSigma (F t) (H t))
      (fun t z => X t z.2) := by
  letI : MeasurableSpace Ω := m
  letI : MeasurableSpace Γ := n
  refine ⟨fun t => (hX.adapted t).comp (@measurable_snd Ω Γ (F t) (H t)),
    fun t => (hX.moment t).comp_measurePreserving measurePreserving_snd,
    fun z => hX.path z.2,?_,?_⟩
  · intro s t hst
    exact (product_conditional_snd P Q (F s) (H s) (hle s) (hHl s) (X t)
      ((hX.moment t).integrable (by norm_num))).trans
      (Measure.quasiMeasurePreserving_snd.ae (hX.martingale s t hst))
  · exact Measure.quasiMeasurePreserving_snd.ae hX.initial

/-- The original bounded localizers also work on the product space. -/
theorem local_product_snd
    {Ω Γ : Type*} [m : MeasurableSpace Ω] [n : MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (H : ClosedTime T → MeasurableSpace Γ)
    (hle : ∀ t,F t ≤ m) (hHl : ∀ t,H t ≤ n)
    (X : ClosedTime T → Γ → ℝ) (hX : LocalMProcessWitness Q H X) :
    LocalMProcessWitness (P.prod Q) (fun t => productSigma (F t) (H t))
      (fun t z => X t z.2) := by
  letI : MeasurableSpace Ω := m
  letI : MeasurableSpace Γ := n
  obtain ⟨τ,hs,hm,ht,hc,hb⟩ := hX.localizers
  refine ⟨fun j z => τ j z.2,fun j t => (hs j t).preimage (@measurable_snd Ω Γ (F t) (H t)),
    fun z => hm z.2,fun j z => ht j z.2,fun z => hc z.2,?_⟩
  intro j
  exact ⟨m2_product_snd P Q F H hle hHl _ (hb j).1,
    fun t => ((hb j).2 t).comp_measurePreserving measurePreserving_snd⟩

theorem variation_product_snd
    {Ω Γ : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (H : ClosedTime T → MeasurableSpace Γ)
    (A : ClosedTime T → Γ → ℝ) (hA : LocalVariationWitness H A) :
    LocalVariationWitness (fun t => productSigma (F t) (H t)) (fun t z => A t z.2) := by
  obtain ⟨τ,hs,hm,ht,hc,hb⟩ := hA.localizers
  exact ⟨fun j z => τ j z.2,fun j t => (hs j t).preimage (@measurable_snd Ω Γ (F t) (H t)),
    fun z => hm z.2,fun j z => ht j z.2,fun z => hc z.2,fun j z => hb j z.2⟩

theorem covariance_product_snd
    {Ω Γ : Type*} [m : MeasurableSpace Ω] [n : MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (H : ClosedTime T → MeasurableSpace Γ)
    (hle : ∀ t,F t ≤ m) (hHl : ∀ t,H t ≤ n)
    (X Y A : ClosedTime T → Γ → ℝ) (hA : LocalCovarianceWitness Q H X Y A) :
    LocalCovarianceWitness (P.prod Q) (fun t => productSigma (F t) (H t))
      (fun t z => X t z.2) (fun t z => Y t z.2) (fun t z => A t z.2) :=
  ⟨local_product_snd P Q F H hle hHl _ hA.defect,variation_product_snd F H A hA.variation⟩

end Asakura.Chapter7
