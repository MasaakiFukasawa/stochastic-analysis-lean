import Chapter1WrittenL1

open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Asakura.Chapter2Written

/-- The optional-sampling proof identifies its two limits by Fatou applied to
|f_n-Z|, without extracting an almost-everywhere convergent subsequence. -/
theorem written_L1_ae_limit_unique {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℕ → Ω → ℝ) (F Z : Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hF : AEStronglyMeasurable F μ) (hZ : AEStronglyMeasurable Z μ)
    (hpath : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (F ω)))
    (hL1 : Tendsto (fun n => eLpNorm (f n-Z) 1 μ) atTop (𝓝 0)) :
    F =ᵐ[μ] Z := by
  have he : (fun ω => ‖F ω-Z ω‖ₑ) =ᵐ[μ]
      (fun ω => liminf (fun n => ‖f n ω-Z ω‖ₑ) atTop) := by
    filter_upwards [hpath] with ω hω
    exact ((hω.sub tendsto_const_nhds).enorm.liminf_eq).symm
  have ht : Tendsto (fun n => ∫⁻ ω, ‖f n ω-Z ω‖ₑ ∂μ) atTop (𝓝 0) := by
    simpa only [eLpNorm_one_eq_lintegral_enorm ((hf _).sub hZ), Pi.sub_apply] using hL1
  have hi : (∫⁻ ω, ‖F ω-Z ω‖ₑ ∂μ) = 0 := by
    apply le_antisymm _ zero_le
    calc
      _ = ∫⁻ ω, liminf (fun n => ‖f n ω-Z ω‖ₑ) atTop ∂μ := lintegral_congr_ae he
      _ ≤ liminf (fun n => ∫⁻ ω, ‖f n ω-Z ω‖ₑ ∂μ) atTop :=
        lintegral_liminf_le' (fun n => ((hf n).sub hZ).enorm)
      _ = 0 := ht.liminf_eq
  have hz := (lintegral_eq_zero_iff' ((hF.sub hZ).enorm)).mp hi
  filter_upwards [hz] with ω hω
  simpa only [Pi.zero_apply, enorm_eq_zero, Pi.sub_apply, sub_eq_zero] using hω

/-- The backward L1 limit used in the manuscript, supplied by the previously
checked convex-combination and cutoff proof, is identified by the Fatou step. -/
theorem written_backward_limit_identification {Ω : Type*} {m : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (G : ℕ → MeasurableSpace Ω) (hG : Antitone G) (hle : ∀ n, G n ≤ m)
    {Y F : Ω → ℝ} (hmY : Measurable[m] Y) (hY : Integrable Y P)
    (hF : AEStronglyMeasurable F P)
    (hpath : ∀ᵐ ω ∂P, Tendsto (fun n => P[Y | G n] ω) atTop (𝓝 (F ω))) :
    F =ᵐ[P] P[Y | ⨅ n, G n] := by
  apply written_L1_ae_limit_unique P (fun n => P[Y | G n]) F _
    (fun _ => integrable_condExp.aestronglyMeasurable) hF integrable_condExp.aestronglyMeasurable hpath
  exact (Asakura.Chapter1Written.conditional_L1_written G hle hmY hY).2 hG

/-- The final C5 step. H is the stopped sigma algebra and is contained in the
intersection; its measurable stopped value is integrable by the identification. -/
theorem written_backward_stop_identification {Ω : Type*} {m : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (G : ℕ → MeasurableSpace Ω) (hG : Antitone G) (hle : ∀ n, G n ≤ m)
    (H : MeasurableSpace Ω) (hHG : H ≤ ⨅ n, G n)
    {Y F : Ω → ℝ} (hmY : Measurable[m] Y) (hY : Integrable Y P)
    (hF : StronglyMeasurable[H] F)
    (hpath : ∀ᵐ ω ∂P, Tendsto (fun n => P[Y | G n] ω) atTop (𝓝 (F ω))) :
    F =ᵐ[P] P[Y | H] := by
  have hIm : (⨅ n, G n) ≤ m := (iInf_le G 0).trans (hle 0)
  have hHm : H ≤ m := hHG.trans hIm
  have he := written_backward_limit_identification G hG hle hmY hY
    (hF.mono hHm).aestronglyMeasurable hpath
  have hFi : Integrable F P := integrable_condExp.congr he.symm
  calc
    F =ᵐ[P] P[F | H] := Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable hHm hF hFi).symm
    _ =ᵐ[P] P[P[Y | ⨅ n, G n] | H] := condExp_congr_ae he
    _ =ᵐ[P] P[Y | H] := condExp_condExp_of_le hHG hIm

end Asakura.Chapter2Written
