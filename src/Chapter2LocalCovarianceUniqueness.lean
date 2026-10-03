import Chapter2LocalCovarianceConstruction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Full uniqueness argument for local covariation, with independent
localizers for A and B and the two local product defects. The finite-variation
premise is weaker than A_loc, so in particular includes its adapted decompositions. -/
theorem local_covariation_unique
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X Y A B : ClosedTime T → Ω → ℝ)
    (hMA : LocalMProcessWitness P F (fun t ω => X t ω * Y t ω-A t ω))
    (hMB : LocalMProcessWitness P F (fun t ω => X t ω * Y t ω-B t ω))
    (τ σ : ℕ → Ω → ClosedTime T)
    (hτ : ∀ n t, MeasurableSet[F t] {ω | τ n ω ≤ t})
    (hσ : ∀ n t, MeasurableSet[F t] {ω | σ n ω ≤ t})
    (hτmono : ∀ ω, Monotone (fun n => τ n ω))
    (hσmono : ∀ ω, Monotone (fun n => σ n ω))
    (hτcofinal : ∀ ω t, t < ⊤ → ∃ n, t < τ n ω)
    (hσcofinal : ∀ ω t, t < ⊤ → ∃ n, t < σ n ω)
    (hA : ∀ n ω, ∃ U V : ClosedTime T → ℝ, Monotone U ∧ Monotone V ∧
      ∀ t, A (min (τ n ω) t) ω = U t-V t)
    (hB : ∀ n ω, ∃ U V : ClosedTime T → ℝ, Monotone U ∧ Monotone V ∧
      ∀ t, B (min (σ n ω) t) ω = U t-V t) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → A t ω = B t ω := by
  have hZ : LocalMProcessWitness P F (fun t ω => A t ω-B t ω) := by
    have h := hMB.add P F hF hle (hMA.smul P F (-1))
    convert h using 1
    funext t ω
    ring
  have hr (n) := (written_stopping_min_max F (τ n) (σ n) (hτ n) (hσ n)).1
  have hrm (ω) := (hτmono ω).min (hσmono ω)
  have hrc (ω) := (common_localizers_cofinal (fun n => τ n ω) (fun n => σ n ω)
    (hτmono ω) (hσmono ω) (hτcofinal ω) (hσcofinal ω)).2
  have hBV (n ω) : ∃ U V : ClosedTime T → ℝ, Monotone U ∧ Monotone V ∧
      ∀ t, A (min (min (τ n ω) (σ n ω)) t) ω-B (min (min (τ n ω) (σ n ω)) t) ω = U t-V t := by
    obtain ⟨Ap,An,hAp,hAn,heA⟩ := hA n ω
    obtain ⟨Bp,Bn,hBp,hBn,heB⟩ := hB n ω
    refine ⟨fun t => Ap (min (σ n ω) t)+Bn (min (τ n ω) t),
      fun t => An (min (σ n ω) t)+Bp (min (τ n ω) t),
      (hAp.comp (monotone_const.min monotone_id)).add (hBn.comp (monotone_const.min monotone_id)),
      (hAn.comp (monotone_const.min monotone_id)).add (hBp.comp (monotone_const.min monotone_id)),?_⟩
    intro t
    have ha := heA (min (σ n ω) t)
    have hb := heB (min (τ n ω) t)
    simp only [← min_assoc,min_comm (σ n ω) (τ n ω)] at ha hb
    rw [ha,hb]
    ring
  have hz := local_finite_variation_intersection_zero P F hF hle _ hZ
    (fun n ω => min (τ n ω) (σ n ω)) hr hrm hrc hBV
  exact hz.mono fun ω hω t ht => sub_eq_zero.mp (hω t ht)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_covariation_unique
