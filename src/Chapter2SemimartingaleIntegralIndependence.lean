import Chapter2SemimartingaleAssociativity

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option backward.isDefEq.respectTransparency false

theorem VariationIntegralFormula.congr_integrator
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hcT : ∀ n, (c n:EReal) < T)
    (A B I : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hI : VariationIntegralFormula P c hc A H I)
    (he : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → A t ω = B t ω) :
    VariationIntegralFormula P c hc B H I := by
  intro n
  obtain ⟨ξ,hs,hξ,hi,hform⟩ := hI n
  refine ⟨ξ,hs,?_,hi,hform⟩
  have hbelow (r : ℝ) : realTimeClamp (T := T) (intervalClamp 0 (c n) (hc n) r) < ⊤ := by
    apply lt_of_le_of_lt (real_time_clamp_mono (intervalClamp_mem 0 (c n) (hc n) r).2)
    change (realTimeClamp (c n):EReal) < T
    rw [real_time_clamp_eq _ (hc n) (hcT n).le]
    exact hcT n
  filter_upwards [he,hξ] with ω heω hξω
  intro s t hst
  rw [hξω s t hst,heω _ (hbelow t),heω _ (hbelow s)]

theorem ItoCovarianceFormula.congr_integrator
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (M N J : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hM : LocalMProcessWitness P F M) (hN : LocalMProcessWitness P F N)
    (hJ : ItoCovarianceFormula P F M H J)
    (he : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → M t ω = N t ω) :
    ItoCovarianceFormula P F N H J := by
  intro Z C hZ hC
  exact hJ Z C hZ (hC.congr_ae_processes P F hF hle hN hZ hM hZ
    (he.mono fun ω hω t ht => (hω t ht).symm) (.of_forall fun _ _ _ => rfl))

/-- Independence of the decomposition and its representatives, using the
proved A_loc/M_loc uniqueness and actual signed/Ito formulas. -/
theorem semimartingale_integral_independent_of_decomposition
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (X A M B N Y Z : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hX : SemimartingaleDecomposition P F X A M)
    (hX' : SemimartingaleDecomposition P F X B N)
    (hY : SemimartingaleIntegralFormula P F c hc A M H Y)
    (hZ : SemimartingaleIntegralFormula P F c hc B N H Z) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → Y t ω = Z t ω := by
  have he := hX.unique P F hF hle hX'
  obtain ⟨I,J,hD,hI,hJ⟩ := hY
  have hY' : SemimartingaleIntegralFormula P F c hc B N H Y :=
    ⟨I,J,hD,hI.congr_integrator P c hc hcT A B I H
      (he.mono fun ω hω t ht => (hω t ht).1),
      hJ.congr_integrator P F hF hle M N J H hX.martingale hX'.martingale
        (he.mono fun ω hω t ht => (hω t ht).2)⟩
  exact hY'.unique P hT F hF hle hnull c hc hcc B N Y Z H hX'.martingale hZ

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.semimartingale_integral_independent_of_decomposition
