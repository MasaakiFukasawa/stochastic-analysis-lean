import Chapter4ClockVariationIntegral
import Chapter3LocalItoFormula
import Chapter3ContinuousIntegralConstruction
import Chapter4ConstructedScalarIto

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Ito formula with constructed stochastic integral and ordinary time
integral, simultaneously for all finite times when the bracket is time. -/
theorem constructed_clock_ito
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (f f₁ f₂ : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (h₁ : ∀ x, HasDerivAt f (f₁ x) x) (h₂ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcm : Monotone c)
    (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hclock : ∀ n ω r, r ∈ Icc 0 (c n) → C (realTimeClamp r) ω = r) :
    ∃ Z : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F X
        (fun z => f₁ (X (realTimeClamp z.2) z.1)) Z ∧
      ∀ᵐ ω ∂P, ∀ d : ℝ, 0 ≤ d → (d:EReal) < T →
        f (X (realTimeClamp d) ω) = f (X ⊥ ω)+Z (realTimeClamp d) ω+
          (∫ r in 0..d, f₂ (X (realTimeClamp r) ω))/2 := by
  obtain ⟨Z,J,hZ,hZI,hJ,he⟩ := constructed_local_ito P hT F hF hle hnull X C hX hC
    f f₁ f₂ hf h₁ h₂ c hc hcm hcT hcc
  have htime := clock_variation_integral_all_times P C J _ c hc hcT hclock hJ
  refine ⟨Z,hZ,hZI,?_⟩
  filter_upwards [he,htime] with ω heω htω
  intro d hd hdT
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d : EReal) < T
    rw [real_time_clamp_eq d hd hdT.le]
    exact hdT
  obtain ⟨j,hj⟩ := hcc _ hdt
  have hdc : d ≤ c j := by
    change (realTimeClamp d : EReal) < (realTimeClamp (c j) : EReal) at hj
    rw [real_time_clamp_eq d hd hdT.le,real_time_clamp_eq (c j) (hc j) (hcT j).le] at hj
    exact EReal.coe_le_coe_iff.mp hj.le
  have hh := heω _ hdt
  rw [htω j d ⟨hd,hdc⟩] at hh
  exact hh

end Asakura.Chapter4
