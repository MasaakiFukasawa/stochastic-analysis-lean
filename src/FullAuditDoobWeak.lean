import FullAuditDoobStopping

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written

/-- The first inequality in the manuscript's Doob theorem, using its capped
first-hitting time and the written countable optional sampling proof. -/
theorem doob_weak_written {Ω ι : Type*} {m : MeasurableSpace Ω}
    [Fintype ι] [LinearOrder ι] [OrderTop ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ i, F i ≤ m)
    (X : ι → Ω → ℝ) (hmX : ∀ i, Measurable[F i] (X i))
    (hY : Integrable (X ⊤) P) (hpos : ∀ i, 0 ≤ᵐ[P] X i)
    (hdom : ∀ i, X i ≤ᵐ[P] P[X ⊤ | F i]) (a : ℝ) (ha : 0 < a) :
    P.real {ω | ∃ i, a ≤ X i ω} ≤
      a⁻¹ * ∫ ω in {ω | ∃ i, a ≤ X i ω}, X ⊤ ω ∂P := by
  let τ := cappedFirstHit X a
  have hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i} := cappedFirstHit_stopping F hF X hmX a
  let G := writtenStoppedSpace m F τ hτ
  have hG : G ≤ m := fun A hA => hA.1
  let V : Ω → ℝ := fun ω => X (τ ω) ω
  let Z : Ω → ℝ := fun ω => P[X ⊤ | F (τ ω)] ω
  have hmV : Measurable[m] V :=
    (stopped_value_measurable_countable m F hF hle τ hτ X hmX).mono hG le_rfl
  have hZe : Z =ᵐ[P] P[X ⊤ | G] := closed_optional_sampling_written P F hF hle τ hτ hY
  have hZi : Integrable Z P := integrable_condExp.congr hZe.symm
  have hVpos : 0 ≤ᵐ[P] V := (ae_all_iff.mpr hpos).mono fun ω hω => hω (τ ω)
  have hVZ : V ≤ᵐ[P] Z := (ae_all_iff.mpr hdom).mono fun ω hω => hω (τ ω)
  have hVi : Integrable V P := hZi.mono' hmV.aestronglyMeasurable (by
    filter_upwards [hVpos,hVZ] with ω hp hd
    rw [Real.norm_eq_abs,abs_of_nonneg hp]
    exact hd)
  have htotal : ∫ ω, V ω ∂P ≤ ∫ ω, X ⊤ ω ∂P := by
    calc
      _ ≤ ∫ ω, Z ω ∂P := integral_mono_ae hVi hZi hVZ
      _ = ∫ ω, P[X ⊤ | G] ω ∂P := integral_congr_ae hZe
      _ = _ := integral_condExp hG
  let B : Set Ω := {ω | ∃ i, a ≤ X i ω}
  have hBm : MeasurableSet[m] B := by
    have he : B = ⋃ i, {ω | a ≤ X i ω} := by ext ω; simp [B]
    rw [he]
    exact MeasurableSet.iUnion fun i => measurableSet_le measurable_const ((hmX i).mono (hle i) le_rfl)
  have hhit : a * P.real B ≤ ∫ ω in B, V ω ∂P := by
    calc
      _ = ∫ ω in B, a ∂P := by simp [mul_comm]
      _ ≤ _ := integral_mono_ae (integrable_const _) hVi.integrableOn
        ((ae_restrict_mem hBm).mono fun ω hω => cappedFirstHit_level X a ω hω)
  have hmiss : ∫ ω in Bᶜ, V ω ∂P = ∫ ω in Bᶜ, X ⊤ ω ∂P := by
    apply setIntegral_congr_fun hBm.compl
    intro ω hω
    change X (cappedFirstHit X a ω) ω = X ⊤ ω
    rw [cappedFirstHit_no_hit X a ω hω]
  have hvsum := integral_add_compl hBm hVi
  have hysum := integral_add_compl hBm hY
  rw [hmiss] at hvsum
  have hbound : a * P.real B ≤ ∫ ω in B, X ⊤ ω ∂P := by linarith
  change P.real B ≤ a⁻¹ * (∫ ω in B, X ⊤ ω ∂P)
  rw [mul_comm a⁻¹, ← div_eq_mul_inv]
  exact (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hbound)

/-- The last inequality in part (1), including its absolute terminal moment. -/
theorem doob_weak_terminal_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : Integrable Y P)
    (B : Set Ω) (hB : MeasurableSet B) (a : ℝ) (ha : 0 < a) :
    a⁻¹ * (∫ ω in B, Y ω ∂P) ≤ a⁻¹ * (∫ ω, |Y ω| ∂P) := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ha.le)
  calc
    _ ≤ ∫ ω in B, |Y ω| ∂P := integral_mono_ae hY.integrableOn hY.abs.integrableOn
      (Eventually.of_forall fun ω => le_abs_self _)
    _ ≤ _ := setIntegral_le_integral hY.abs (Eventually.of_forall fun ω => abs_nonneg _)

end Asakura.FullAudit
