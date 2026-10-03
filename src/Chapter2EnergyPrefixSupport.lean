import Chapter2GlobalEnergyIdentity

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete

set_option backward.isDefEq.respectTransparency false

theorem energy_measure_ae_prefix
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ν : Measure (Ω × ℝ)) (α : ℕ → Ω → Measure ℝ) (c : ℕ → ℝ)
    (hs : ∀ n ω, ∀ᵐ r ∂α n ω, r ∈ Icc 0 (c n))
    (he : ∀ f : Ω × ℝ → ℝ≥0∞, Measurable f →
      (∫⁻ z, f z ∂ν) = ∫⁻ ω, ⨆ n, ∫⁻ r, f (ω,r) ∂α n ω ∂P) :
    ∀ᵐ z ∂ν, ∃ n, z.2 ∈ Icc 0 (c n) := by
  let S : Set (Ω × ℝ) := {z | ∃ n, z.2 ∈ Icc 0 (c n)}
  have hS : MeasurableSet S := by
    have heS : S = ⋃ n, {z : Ω × ℝ | z.2 ∈ Icc 0 (c n)} := by ext z; simp [S]
    rw [heS]
    exact MeasurableSet.iUnion (fun n => measurable_snd measurableSet_Icc)
  have hh := he (Sᶜ.indicator (fun _ => (1:ℝ≥0∞))) (measurable_const.indicator hS.compl)
  have hz n ω : (∫⁻ r, Sᶜ.indicator (fun _ => (1:ℝ≥0∞)) (ω,r) ∂α n ω) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hs n ω] with r hr
    exact indicator_of_notMem (show (ω,r) ∉ Sᶜ from fun h => h ⟨n,hr⟩) _
  simp only [hz,iSup_const,lintegral_zero] at hh
  rw [lintegral_indicator hS.compl] at hh
  rw [ae_iff]
  simpa only [lintegral_const,one_mul,Measure.restrict_apply_univ,S,compl_setOf] using hh

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.energy_measure_ae_prefix
