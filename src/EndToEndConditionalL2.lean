import Chapter1WrittenInteger

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.EndToEnd
open Asakura.Chapter1Written

theorem conditional_natural_L2 {Ω : Type*} {m : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (G : ℕ → MeasurableSpace Ω) (hle : ∀ n, G n ≤ m)
    {X : Ω → ℝ} (hX : MemLp X 2 P) :
    (Monotone G → Tendsto (fun n => eLpNorm (P[X | G n]-P[X | ⨆ n, G n]) 2 P) atTop (𝓝 0)) ∧
    (Antitone G → Tendsto (fun n => eLpNorm (P[X | G n]-P[X | ⨅ n, G n]) 2 P) atTop (𝓝 0)) := by
  constructor
  · intro hG
    have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp
      (conditional_upward_L2_written G hG hle hX.toLp)
    apply ht.congr
    intro n
    exact eLpNorm_congr_ae ((hX.condExpL2_ae_eq_condExp (𝕜 := ℝ) (hle n)).sub
      (hX.condExpL2_ae_eq_condExp (𝕜 := ℝ) (iSup_le hle)))
  · intro hG
    have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp
      (conditional_downward_L2_written G hG hle hX.toLp)
    apply ht.congr
    intro n
    exact eLpNorm_congr_ae ((hX.condExpL2_ae_eq_condExp (𝕜 := ℝ) (hle n)).sub
      (hX.condExpL2_ae_eq_condExp (𝕜 := ℝ) ((iInf_le G 0).trans (hle 0))))

theorem conditional_integer_L2 {Ω : Type*} {m : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (G : ℤ → MeasurableSpace Ω) (hG : Monotone G) (hle : ∀ z, G z ≤ m)
    {X : Ω → ℝ} (hX : MemLp X 2 P) :
    Tendsto (fun z => eLpNorm (P[X | G z]-P[X | ⨆ z, G z]) 2 P) atTop (𝓝 0) ∧
    Tendsto (fun z => eLpNorm (P[X | G z]-P[X | ⨅ z, G z]) 2 P) atBot (𝓝 0) := by
  have hsup : (⨆ n : ℕ, G (n : ℤ)) = ⨆ z : ℤ, G z := by
    apply le_antisymm
    · exact iSup_le (fun n => le_iSup G (n : ℤ))
    · apply iSup_le
      intro z
      exact (hG (Int.self_le_toNat z)).trans (le_iSup (fun n : ℕ => G (n : ℤ)) z.toNat)
  have hinf : (⨅ n : ℕ, G (-(n : ℤ))) = ⨅ z : ℤ, G z := by
    apply le_antisymm
    · apply le_iInf
      intro z
      apply (iInf_le (fun n : ℕ => G (-(n : ℤ))) (-z).toNat).trans
      apply hG
      have := Int.self_le_toNat (-z)
      omega
    · exact le_iInf (fun n => iInf_le G (-(n : ℤ)))
  constructor
  · apply integer_limit_from_naturals
    have hm : Monotone (fun n : ℕ => G (n : ℤ)) := by
      intro i j hij
      exact hG (by exact_mod_cast hij)
    have hh := (conditional_natural_L2 (fun n : ℕ => G (n : ℤ)) (fun n => hle _) hX).1 hm
    simpa only [hsup] using hh
  · have hm : Antitone (fun n : ℕ => G (-(n : ℤ))) := by
      intro i j hij
      apply hG
      omega
    have hh := (conditional_natural_L2 (fun n : ℕ => G (-(n : ℤ))) (fun n => hle _) hX).2 hm
    rw [hinf] at hh
    have hh' := integer_limit_from_naturals
      (fun z : ℤ => eLpNorm (P[X | G (-z)]-P[X | ⨅ z, G z]) 2 P) 0 hh
    simpa [Function.comp_def] using hh'.comp (tendsto_neg_atBot_atTop : Tendsto (fun z : ℤ => -z) atBot atTop)

end Asakura.EndToEnd

#print axioms Asakura.EndToEnd.conditional_integer_L2
