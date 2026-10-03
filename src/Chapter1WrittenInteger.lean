import Chapter1WrittenL1

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter1Written

/-- The restriction to nonnegative integers loses no information at +infinity. -/
theorem integer_limit_from_naturals {E : Type*} [TopologicalSpace E]
    (f : ℤ → E) (y : E) (h : Tendsto (fun n : ℕ => f n) atTop (𝓝 y)) :
    Tendsto f atTop (𝓝 y) := by
  have hn : Tendsto Int.toNat atTop atTop := by
    apply tendsto_atTop.mpr
    intro n
    refine eventually_atTop.mpr ⟨(n : ℤ), ?_⟩
    intro z hz
    omega
  apply (h.comp hn).congr'
  filter_upwards [eventually_ge_atTop (0 : ℤ)] with z hz
  have he : (z.toNat : ℤ) = z := by omega
  simp [Function.comp_def, he]

/-- The original integer-indexed statement, in both directions, with the written
Jensen and convex-tail/cutoff proofs as its dependencies. -/
theorem conditional_integer_L1_written {Ω : Type*} {m : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (G : ℤ → MeasurableSpace Ω) (hG : Monotone G) (hle : ∀ z, G z ≤ m)
    {X : Ω → ℝ} (hmX : Measurable X) (hX : Integrable X P) :
    Tendsto (fun z => eLpNorm (P[X | G z]-P[X | ⨆ z, G z]) 1 P) atTop (𝓝 0) ∧
    Tendsto (fun z => eLpNorm (P[X | G z]-P[X | ⨅ z, G z]) 1 P) atBot (𝓝 0) := by
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
    have hh := (conditional_L1_written (fun n : ℕ => G (n : ℤ)) (fun n => hle _) hmX hX).1 hm
    simpa only [hsup] using hh
  · have hm : Antitone (fun n : ℕ => G (-(n : ℤ))) := by
      intro i j hij
      apply hG
      omega
    have hh := (conditional_L1_written (fun n : ℕ => G (-(n : ℤ))) (fun n => hle _) hmX hX).2 hm
    rw [hinf] at hh
    have hh' := integer_limit_from_naturals
      (fun z : ℤ => eLpNorm (P[X | G (-z)]-P[X | ⨅ z, G z]) 1 P) 0 hh
    simpa [Function.comp_def] using hh'.comp (tendsto_neg_atBot_atTop : Tendsto (fun z : ℤ => -z) atBot atTop)

end Asakura.Chapter1Written
