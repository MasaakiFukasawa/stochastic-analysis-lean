import Chapter2FiniteDensity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Remove the finite-interval subtype notation from the elementary
strategy. This identifies the actual integrands on the Stieltjes support. -/
theorem finite_grid_projection_identity
    (a b : ℝ) (hab : a ≤ b) (N : ℕ) (u : ℕ → Icc a b) (G : ℕ → ℝ)
    (r : ℝ) (hr : r ∈ Icc a b) :
    (∑ j ∈ Finset.range N, (Ico (u j) (u (j+1))).indicator (fun _ => G j) (projIcc a b hab r)) =
    ∑ j ∈ Finset.range N, (Ico (u j).val (u (j+1)).val).indicator (fun _ => G j) r := by
  classical
  apply Finset.sum_congr rfl
  intro j hj
  have hp : (projIcc a b hab r : ℝ) = r := congrArg Subtype.val (projIcc_of_mem hab hr)
  have he : projIcc a b hab r ∈ Ico (u j) (u (j+1)) ↔ r ∈ Ico (u j).val (u (j+1)).val := by
    change ((u j).val ≤ (projIcc a b hab r : ℝ) ∧ (projIcc a b hab r : ℝ) < (u (j+1)).val) ↔ _
    rw [hp]
    rfl
  by_cases hh : r ∈ Ico (u j).val (u (j+1)).val
  · rw [indicator_of_mem (he.2 hh),indicator_of_mem hh]
  · rw [indicator_of_notMem (fun h => hh (he.1 h)),indicator_of_notMem hh]

/-- The finite-interval density theorem in the manuscript's real-time
notation, ready for diagonalization over increasing time intervals. -/
theorem finite_step_density_real
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (b : ℝ) (hb : 0 < b) [Fact (0 ≤ b)] (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, MonotoneOn (A ω) (Icc 0 b)) (hc : ∀ ω, ContinuousOn (A ω) (Icc 0 b))
    (hm : ∀ t, Measurable (fun ω => A ω t))
    (F : ℝ → MeasurableSpace Ω) (hF : Monotone F)
    (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (had : ∀ t ∈ Icc 0 b, Measurable[F t] (fun ω => A ω t))
    (hnull : ∀ t N, MeasurableSet N → P N = 0 → MeasurableSet[F t] N)
    (H : Ω × ℝ → ℝ)
    (hH : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) b => F t.val)) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => H (z.1,z.2.val)))
    (p : ℝ) (hp : 0 < p)
    (hi : ∀ᵐ ω ∂P, Integrable (fun r => |H (ω,r)|^p)
      (intervalStieltjes 0 b hb.le (A ω) (hA ω)
        (fun r hr => (hc ω r hr).mono inter_subset_left)).measure) :
    ∃ (N : ℕ → ℕ) (u : ℕ → ℕ → ℝ) (V : ℕ → ℕ → Ω → ℝ),
      (∀ n, StrictMonoOn (u n) (Iic (N n))) ∧
      (∀ n j, j ≤ N n → u n j ∈ Icc 0 b) ∧
      (∀ n j, j < N n → Measurable[F (u n j)] (V n j) ∧ MemLp (V n j) ∞ P) ∧
      let μ := fun ω => (intervalStieltjes 0 b hb.le (A ω) (hA ω)
        (fun r hr => (hc ω r hr).mono inter_subset_left)).measure
      let E := fun n ω r => |(∑ j ∈ Finset.range (N n),
        (Ico (u n j) (u n (j+1))).indicator (fun _ => V n j ω) r)-H (ω,r)|^p
      (∀ n, ∀ᵐ ω ∂P, Integrable (E n ω) (μ ω)) ∧
      ∀ ε > 0, Tendsto (fun n => P {ω | ε ≤ ∫ r, E n ω r ∂μ ω}) atTop (𝓝 0) := by
  classical
  let μ := fun ω => (intervalStieltjes 0 b hb.le (A ω) (hA ω)
    (fun r hr => (hc ω r hr).mono inter_subset_left)).measure
  have hproj ω : (fun r => H (ω,(projIcc 0 b hb.le r:ℝ))) =ᵐ[μ ω] fun r => H (ω,r) := by
    filter_upwards [interval_stieltjes_ae_mem_Ioc 0 b hb.le (A ω) (hA ω)
      (fun r hr => (hc ω r hr).mono inter_subset_left)] with r hr
    rw [show (projIcc 0 b hb.le r:ℝ) = r from congrArg Subtype.val (projIcc_of_mem hb.le ⟨hr.1.le,hr.2⟩)]
  have hip : ∀ᵐ ω ∂P, Integrable (fun r => |H (ω,(projIcc 0 b hb.le r:ℝ))|^p) (μ ω) := by
    filter_upwards [hi] with ω hω
    exact hω.congr ((hproj ω).symm.mono (fun r hr => congrArg (fun x : ℝ => |x|^p) hr))
  obtain ⟨N,u,V,hmono,hadapt,hint,hlim⟩ := finite_step_density P b hb A hA hc hm
    (fun t : Icc (0:ℝ) b => F t.val) (fun s t hst => hF hst) (fun t => hle t.val)
    (fun t => had t.val t.property) (fun t => hnull t.val)
    (fun z : Ω × Icc (0:ℝ) b => H (z.1,z.2.val)) hH p hp hip
  have he n ω :
      (fun r => |(∑ j ∈ Finset.range (N n), (Ico (u n j) (u n (j+1))).indicator
        (fun _ => V n j ω) (projIcc 0 b hb.le r))-H (ω,(projIcc 0 b hb.le r:ℝ))|^p) =ᵐ[μ ω]
      (fun r => |(∑ j ∈ Finset.range (N n), (Ico (u n j).val (u n (j+1)).val).indicator
        (fun _ => V n j ω) r)-H (ω,r)|^p) := by
    filter_upwards [hproj ω,interval_stieltjes_ae_mem_Ioc 0 b hb.le (A ω) (hA ω)
      (fun r hr => (hc ω r hr).mono inter_subset_left)] with r hh hr
    rw [hh,finite_grid_projection_identity 0 b hb.le (N n) (u n) (fun j => V n j ω) r ⟨hr.1.le,hr.2⟩]
  refine ⟨N,(fun n j => (u n j).val),V,(fun n i hi j hj hij => hmono n hi hj hij),
    (fun n j _ => (u n j).property),hadapt,?_,?_⟩
  · intro n
    filter_upwards [hint n] with ω hω
    exact hω.congr (he n ω)
  · intro ε hε
    have heq n ω : (∫ r,
        |(∑ j ∈ Finset.range (N n), (Ico (u n j) (u n (j+1))).indicator
          (fun _ => V n j ω) (projIcc 0 b hb.le r))-H (ω,(projIcc 0 b hb.le r:ℝ))|^p ∂μ ω) =
        ∫ r, |(∑ j ∈ Finset.range (N n), (Ico (u n j).val (u n (j+1)).val).indicator
          (fun _ => V n j ω) r)-H (ω,r)|^p ∂μ ω := integral_congr_ae (he n ω)
    dsimp only [μ] at heq
    simpa only [heq] using hlim ε hε

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.finite_grid_projection_identity
#print axioms Asakura.Chapter2Complete.finite_step_density_real
