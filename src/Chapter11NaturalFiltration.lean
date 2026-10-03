import FullAuditNaturalFiltration

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit
set_option maxHeartbeats 1000000

/-- Adding a deterministic drift does not change the uncompleted natural
filtration. -/
theorem natural_filtration_deterministic_shift {Ω ι : Type*} [Preorder ι]
    (X : ι → Ω → ℝ) (d : ι → ℝ) (s : ι) :
    pastSigma (fun t w => X t w+d t) s=pastSigma X s := by
  apply le_antisymm
  · apply iSup_le
    intro t
    have hx : Measurable[pastSigma X s] (X t.val) :=
      (natural_process_adapted X t.val).mono (past_sigma_mono X t.property) le_rfl
    exact (hx.add_const (d t.val)).comap_le
  · apply iSup_le
    intro t
    have hy : Measurable[pastSigma (fun t w => X t w+d t) s] (fun w => X t.val w+d t.val) :=
      (natural_process_adapted (fun t w => X t w+d t) t.val).mono
        (past_sigma_mono _ t.property) le_rfl
    have hx := hy.sub_const (d t.val)
    have he : (fun w => X t.val w+d t.val-d t.val)=X t.val := by funext w;ring
    rw [he] at hx
    exact hx.comap_le

/-- Equivalent measures have exactly the same completed sigma algebra. -/
theorem null_augmentation_equivalent {Ω : Type*} [m : MeasurableSpace Ω]
    (P Q : Measure Ω) (ha : ∀ p : Ω → Prop,(∀ᵐ w ∂P,p w) ↔ ∀ᵐ w ∂Q,p w)
    (G : MeasurableSpace Ω) :
    Asakura.nullAugmentation (m := m) P G=Asakura.nullAugmentation (m := m) Q G := by
  apply le_antisymm
  · rintro A ⟨hm,B,hB,he⟩
    exact ⟨hm,B,hB,(ha _).mp he⟩
  · rintro A ⟨hm,B,hB,he⟩
    exact ⟨hm,B,hB,(ha _).mpr he⟩

/-- The natural-filtration hypothesis survives the Black--Scholes change of
measure and its deterministic Brownian shift. -/
theorem completed_natural_filtration_shift {Ω ι : Type*} [m : MeasurableSpace Ω]
    [Preorder ι] (P Q : Measure Ω)
    (ha : ∀ p : Ω → Prop,(∀ᵐ w ∂P,p w) ↔ ∀ᵐ w ∂Q,p w)
    (X : ι → Ω → ℝ) (d : ι → ℝ) (s : ι) :
    Asakura.nullAugmentation (m := m) Q (pastSigma (fun t w => X t w+d t) s)=
      Asakura.nullAugmentation (m := m) P (pastSigma X s) := by
  rw [natural_filtration_deterministic_shift,null_augmentation_equivalent P Q ha]

/-- Pointwise-in-time almost-everywhere equality is sufficient after the
null augmentation; no common event indexed by uncountably many times is
silently assumed. -/
theorem completed_natural_filtration_ae_congr {Ω ι : Type*} [m : MeasurableSpace Ω]
    [Preorder ι] (P : Measure Ω) (X Y : ι → Ω → ℝ) (s : ι)
    (hX : ∀ t,Measurable[m] (X t)) (hY : ∀ t,Measurable[m] (Y t))
    (he : ∀ t,t≤s → X t=ᵐ[P] Y t) :
    Asakura.nullAugmentation (m := m) P (pastSigma X s)=
      Asakura.nullAugmentation (m := m) P (pastSigma Y s) := by
  have hle (U V : ι → Ω → ℝ) (hU : ∀ t,Measurable[m] (U t))
      (hV : ∀ t,Measurable[m] (V t)) (he : ∀ t,t≤s → U t=ᵐ[P] V t) :
      Asakura.nullAugmentation (m := m) P (pastSigma U s)≤
        Asakura.nullAugmentation (m := m) P (pastSigma V s) := by
    have hp : pastSigma U s≤Asakura.nullAugmentation (m := m) P (pastSigma V s) := by
      apply iSup_le
      intro t
      apply Measurable.comap_le
      intro A hA
      refine ⟨hU t.val hA,(V t.val)⁻¹' A,?_,?_⟩
      · exact ((natural_process_adapted V t.val).mono (past_sigma_mono V t.property) le_rfl) hA
      · filter_upwards [he t.val t.property] with w hw
        simp only [mem_preimage,hw]
    rintro A ⟨hm,B,hB,hAB⟩
    obtain ⟨_,C,hC,hBC⟩ := hp B hB
    exact ⟨hm,C,hC,hAB.trans hBC⟩
  exact le_antisymm (hle X Y hX hY he) (hle Y X hY hX (fun t ht => (he t ht).symm))

end Asakura.Chapter11
