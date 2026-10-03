import FullAuditDoobWeak
import FullAuditDoobStrong

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- Convert the real-valued weak estimate to its weighted-measure form. -/
theorem doob_tail_measure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : Integrable Y μ) (hpos : 0 ≤ᵐ[μ] Y)
    (B : Set Ω) (hB : MeasurableSet B) (t : ℝ) (ht : 0 < t)
    (h : μ.real B ≤ t⁻¹ * ∫ ω in B, Y ω ∂μ) :
    ENNReal.ofReal t * μ B ≤ (μ.withDensity (fun ω => ENNReal.ofReal (Y ω))) B := by
  have hr : t * μ.real B ≤ ∫ ω in B, Y ω ∂μ := by
    have hh := mul_le_mul_of_nonneg_left h ht.le
    simpa [← mul_assoc, ht.ne'] using hh
  have he := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_mul ht.le, Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ B),
    ofReal_integral_eq_lintegral_ofReal hY.integrableOn (ae_restrict_of_ae hpos)] at he
  rwa [withDensity_apply _ hB]

/-- Parts (1)--(2) of Doob's theorem connected to the actual adapted process:
first hitting time, optional sampling, truncation, layer cake, Holder, MCT. -/
theorem doob_process_strong_written {Ω ι : Type*} {m : MeasurableSpace Ω}
    [Fintype ι] [LinearOrder ι] [OrderTop ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ i, F i ≤ m)
    (X : ι → Ω → ℝ) (hmX : ∀ i, Measurable[F i] (X i))
    (hY : Integrable (X ⊤) P) (hpos : ∀ i, 0 ≤ᵐ[P] X i)
    (hdom : ∀ i, X i ≤ᵐ[P] P[X ⊤ | F i]) (p : ℝ) (hp : 1 < p) :
    (∫⁻ ω, ENNReal.ofReal (Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω)) ^ p ∂P) ^ (1/p) ≤
      ENNReal.ofReal (p/(p-1)) * (∫⁻ ω, ENNReal.ofReal (X ⊤ ω) ^ p ∂P) ^ (1/p) := by
  classical
  let M : Ω → ℝ := Finset.univ.sup' Finset.univ_nonempty X
  have hM : Measurable[m] M := Finset.measurable_sup' _ (fun i _ => (hmX i).mono (hle i) le_rfl)
  have hMe : ∀ ω, M ω = Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) := by
    intro ω
    exact Finset.sup'_apply _ _ _
  let S : Ω → ℝ := fun ω => max 0 (M ω)
  have hS : Measurable[m] S := measurable_const.max hM
  have hSpos : ∀ ω, 0 ≤ S ω := fun ω => le_max_left _ _
  have he : ∀ t > 0, {ω | t ≤ S ω} = {ω | ∃ i, t ≤ X i ω} := by
    intro t ht
    ext ω
    simp only [S,le_max_iff,not_le.mpr ht,false_or,hMe,Finset.le_sup'_iff,
      Finset.mem_univ,true_and,mem_setOf_eq]
  have htail : ∀ t > 0, ENNReal.ofReal t * P {ω | t ≤ S ω} ≤
      (P.withDensity (fun ω => ENNReal.ofReal (X ⊤ ω))) {ω | t ≤ S ω} := by
    intro t ht
    have hB : MeasurableSet[m] {ω | t ≤ S ω} := measurableSet_le measurable_const hS
    have hw := doob_weak_written P F hF hle X hmX hY hpos hdom t ht
    rw [← he t ht] at hw
    exact doob_tail_measure P hY (hpos ⊤) _ hB t ht hw
  have h := doob_strong_written P (X ⊤) S ((hmX ⊤).mono (hle ⊤) le_rfl) hS hSpos p hp htail
  have hval : ∀ ω, ENNReal.ofReal (S ω) = ENNReal.ofReal (Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω)) := by
    intro ω
    simp [S,ENNReal.ofReal_max,hMe]
  simpa only [hval] using h

end Asakura.FullAudit
