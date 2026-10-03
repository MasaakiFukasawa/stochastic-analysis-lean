import FullAuditMartingalePathNorm

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written

/-- Differences of the actual process versions satisfy the conditional identity. -/
theorem martingale_difference_identity {Ω ι : Type*} {m : MeasurableSpace Ω}
    [Preorder ι] (P : Measure Ω) [IsProbabilityMeasure P] (F : ι → MeasurableSpace Ω)
    (X Y : ι → Ω → ℝ) (hiX : ∀ t, Integrable (X t) P) (hiY : ∀ t, Integrable (Y t) P)
    (hX : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s)
    (hY : ∀ s t, s ≤ t → P[Y t | F s] =ᵐ[P] Y s) :
    ∀ s t, s ≤ t → P[X t-Y t | F s] =ᵐ[P] X s-Y s := by
  intro s t hst
  exact (condExp_sub (hiX t) (hiY t) (F s)).trans ((hX s t hst).sub (hY s t hst))

theorem continuous_martingale_path_difference_bound {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X Y : ClosedTime T → Ω → ℝ)
    (hmX : ∀ t, Measurable[F t] (X t)) (hmY : ∀ t, Measurable[F t] (Y t))
    (h2X : ∀ t, MemLp (X t) 2 P) (h2Y : ∀ t, MemLp (Y t) 2 P)
    (hcX : ∀ ω, Continuous (fun t => X t ω)) (hcY : ∀ ω, Continuous (fun t => Y t ω))
    (hX : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s)
    (hY : ∀ s t, s ≤ t → P[Y t | F s] =ᵐ[P] Y s) :
    eLpNorm (continuousPath X hcX-continuousPath Y hcY) 2 P ≤
      2 * eLpNorm (X ⊤-Y ⊤) 2 P := by
  have hc : ∀ ω, Continuous (fun t => (X t-Y t) ω) := fun ω => (hcX ω).sub (hcY ω)
  have h := continuous_martingale_path_norm P F hF hle (fun t => X t-Y t)
    (fun t => (hmX t).sub (hmY t)) (fun t => (h2X t).sub (h2Y t)) hc
    (martingale_difference_identity P F X Y (fun t => (h2X t).integrable (by norm_num))
      (fun t => (h2Y t).integrable (by norm_num)) hX hY)
  have he : continuousPath (fun t => X t-Y t) hc = continuousPath X hcX-continuousPath Y hcY := by
    funext ω
    ext t
    rfl
  rwa [he] at h

/-- The full-time L2 distance is at most twice the terminal L2 distance. -/
theorem martingale_path_Lp_distance {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X Y : ClosedTime T → Ω → ℝ)
    (hmX : ∀ t, Measurable[F t] (X t)) (hmY : ∀ t, Measurable[F t] (Y t))
    (h2X : ∀ t, MemLp (X t) 2 P) (h2Y : ∀ t, MemLp (Y t) 2 P)
    (hcX : ∀ ω, Continuous (fun t => X t ω)) (hcY : ∀ ω, Continuous (fun t => Y t ω))
    (hX : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s)
    (hY : ∀ s t, s ≤ t → P[Y t | F s] =ᵐ[P] Y s) :
    dist ((continuous_martingale_path_memLp P F hF hle X hmX h2X hcX hX).toLp (continuousPath X hcX))
      ((continuous_martingale_path_memLp P F hF hle Y hmY h2Y hcY hY).toLp (continuousPath Y hcY)) ≤
      2 * dist ((h2X ⊤).toLp (X ⊤)) ((h2Y ⊤).toLp (Y ⊤)) := by
  have h := continuous_martingale_path_difference_bound P F hF hle X Y hmX hmY h2X h2Y hcX hcY hX hY
  rw [Lp.dist_edist,Lp.dist_edist,Lp.edist_toLp_toLp,Lp.edist_toLp_toLp]
  have hf : 2 * eLpNorm (X ⊤-Y ⊤) 2 P ≠ ∞ := ENNReal.mul_ne_top (by norm_num) ((h2X ⊤).sub (h2Y ⊤)).eLpNorm_ne_top
  have hr := ENNReal.toReal_mono hf h
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofNat] using hr

end Asakura.FullAudit
