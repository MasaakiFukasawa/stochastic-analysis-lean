import Chapter2ElementaryGridEnergy
import Chapter2LenglartConvergence
import Chapter2LocalSeparation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The continuity estimate for actual elementary Ito integrals. Their
local-martingale property and quadratic variation are constructed from
X and the finite trading grids, rather than assumed. -/
theorem elementary_grid_integral_probability_limit
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (N : ℕ → ℕ) (u : ℕ → ℕ → ClosedTime T)
    (hu : ∀ n, StrictMonoOn (u n) (Iic (N n)))
    (G : ℕ → ℕ → Ω → ℝ)
    (hGm : ∀ n i, i < N n → Measurable[F (u n i)] (G n i))
    (hG : ∀ n i, i < N n → MemLp (G n i) ∞ P)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσtop : ∀ ω, σ ω < ⊤)
    (hprob : ∀ δ > 0, Tendsto (fun n => P {ω | δ ≤
      ∑ i ∈ Finset.range (N n), G n i ω^2*stepIncrement (u n i) (u n (i+1)) (fun t => A t ω) (σ ω)}) atTop (𝓝 0)) :
    let Z := fun n t ω => ∑ i ∈ Finset.range (N n),
      G n i ω*stepIncrement (u n i) (u n (i+1)) (fun t => X t ω) t
    (∀ n, LocalMProcessWitness P F (Z n)) ∧
    ∀ ε > 0, Tendsto (fun n => P {ω | ε ≤ ⨆ t, |Z n (min (σ ω) t) ω|}) atTop (𝓝 0) := by
  intro Z
  have hx n := elementary_grid_quadratic_variation P F hF hle hnull X A hX hA
    (N n) (u n) (hu n) (G n) (hGm n) (hG n)
  choose hZ Q hQ hQid using hx
  refine ⟨hZ,?_⟩
  apply local_martingale_probability_of_quadratic_variation P F hF hle hnull Z Q hZ hQ σ hσ hσtop
  intro δ hδ
  have he n : P {ω | δ ≤ Q n (σ ω) ω} = P {ω | δ ≤
      ∑ i ∈ Finset.range (N n), G n i ω^2*stepIncrement (u n i) (u n (i+1)) (fun t => A t ω) (σ ω)} := by
    apply measure_congr
    filter_upwards [hQid n] with ω hω
    change (δ ≤ Q n (σ ω) ω) = _
    rw [hω (σ ω) (hσtop ω)]
  simpa only [he] using hprob δ hδ

/-- Vanishing elementary energy implies a zero gain process. This is the
separation needed when passing to equivalence classes of integrands. -/
theorem elementary_grid_zero_of_zero_energy
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (N : ℕ) (u : ℕ → ClosedTime T) (hu : StrictMonoOn u (Iic N))
    (G : ℕ → Ω → ℝ) (hGm : ∀ i < N, Measurable[F (u i)] (G i))
    (hG : ∀ i < N, MemLp (G i) ∞ P)
    (hz : ∀ᵐ ω ∂P, ∀ t, t < ⊤ →
      ∑ i ∈ Finset.range N, G i ω^2*stepIncrement (u i) (u (i+1)) (fun t => A t ω) t = 0) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ →
      ∑ i ∈ Finset.range N, G i ω*stepIncrement (u i) (u (i+1)) (fun t => X t ω) t = 0 := by
  obtain ⟨hZ,Q,hQ,hQi⟩ := elementary_grid_quadratic_variation P F hF hle hnull X A hX hA N u hu G hGm hG
  apply local_zero_variation_implies_zero P F hF hle _ Q hQ
  filter_upwards [hz,hQi] with ω hzω hiω
  intro t ht
  exact (hiω t ht).trans (hzω t ht)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.elementary_grid_integral_probability_limit
#print axioms Asakura.Chapter2Complete.elementary_grid_zero_of_zero_energy
