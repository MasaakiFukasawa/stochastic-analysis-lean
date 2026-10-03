import Chapter2FiniteExpectedApproximation
import Chapter2CappedStieltjes
import Chapter2LocalizedApproximation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Remove the deterministic bound on A using its actual level-stopped
(capped) measures. The elementary approximants approach the clipped H in
probability for the original, uncapped Stieltjes measure. -/
theorem finite_localized_clipped_step_approximation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (b : ℝ) (hb : 0 < b) [Fact (0 ≤ b)] (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, MonotoneOn (A ω) (Icc 0 b)) (hc : ∀ ω, ContinuousOn (A ω) (Icc 0 b))
    (hm : ∀ t, Measurable (fun ω => A ω t))
    (F : Icc (0:ℝ) b → MeasurableSpace Ω) (hF : Monotone F)
    (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (had : ∀ t : Icc (0:ℝ) b, Measurable[F t] (fun ω => A ω t.val))
    (hnull : ∀ t N, MeasurableSet N → P N = 0 → MeasurableSet[F t] N)
    (H : Ω × Icc (0:ℝ) b → ℝ)
    (hH : @Measurable _ _ (progressiveSpace F) inferInstance H)
    (p : ℝ) (hp : 0 < p) :
    ∃ (N : ℕ → ℕ) (u : ℕ → ℕ → Icc (0:ℝ) b) (V : ℕ → ℕ → Ω → ℝ),
      (∀ n, StrictMonoOn (u n) (Iic (N n))) ∧
      (∀ n j, j < N n → Measurable[F (u n j)] (V n j) ∧ MemLp (V n j) ∞ P) ∧
      (∀ n (q : Ω × Icc (0:ℝ) b), |∑ j ∈ Finset.range (N n),
        (Ico (u n j) (u n (j+1))).indicator (fun _ => V n j q.1) q.2| ≤ (n:ℝ)+1) ∧
      ∀ ε > 0, Tendsto (fun n => P {ω | ε ≤ ∫ r,
        |(∑ j ∈ Finset.range (N n), (Ico (u n j) (u n (j+1))).indicator (fun _ => V n j ω)
          (projIcc 0 b hb.le r))-
          max (-((n:ℝ)+1)) (min ((n:ℝ)+1) (H (ω,projIcc 0 b hb.le r)))| ^ p
          ∂(intervalStieltjes 0 b hb.le (A ω) (hA ω)
            (fun r hr => (hc ω r hr).mono inter_subset_left)).measure}) atTop (𝓝 0) := by
  classical
  let k := fun n : ℕ => (n:ℝ)+1
  have hk n : 0 < k n := by dsimp [k]; positivity
  let B := fun n ω => cappedPath 0 (k n) (A ω)
  have hBn n ω := capped_path_monotone 0 b (k n) (A ω) (hA ω)
  have hBc n ω := capped_path_continuous 0 b (k n) (A ω) (hc ω)
  let hBr := fun n ω r (hr : r ∈ Icc 0 b) => (hBc n ω r hr).mono (inter_subset_left (t := Ici r))
  have hBm n r := capped_path_measurable 0 (k n) A hm r
  have hBk n ω := capped_path_mass_bound 0 b (k n) (A ω) (hk n).le
  have hBad n t := capped_path_adapted 0 b (k n) hb.le F hF A had t
  let Hm := fun n q => max (-(k n)) (min (k n) (H q))
  have hHmeas n : @Measurable _ _ (progressiveSpace F) inferInstance (Hm n) :=
    measurable_const.max (measurable_const.min hH)
  have hHb n q : |Hm n q| ≤ k n :=
    abs_le.2 ⟨le_max_left _ _,max_le (by linarith [hk n]) (min_le_left _ _)⟩
  have hex n := finite_expected_step_approximation P b hb (B n) (hBn n) (hBr n) (hBm n)
    (k n) (hBk n) F hF hle (hBc n) (hk n).le (hBad n) hnull
    (Hm n) (hHmeas n) (k n) (hk n).le (hHb n) p (1/k n) hp (one_div_pos.2 (hk n))
  choose N u V hmono hVm hVbound hSi hSsmall using hex
  let f := fun n ω r => |(∑ j ∈ Finset.range (N n),
    (Ico (u n j) (u n (j+1))).indicator (fun _ => V n j ω) (projIcc 0 b hb.le r))-
    Hm n (ω,projIcc 0 b hb.le r)| ^ p
  let S := fun n ω => ∫ r, f n ω r ∂(intervalStieltjes 0 b hb.le (B n ω) (hBn n ω) (hBr n ω)).measure
  let R := fun n ω => ∫ r, f n ω r ∂(intervalStieltjes 0 b hb.le (A ω) (hA ω)
    (fun r hr => (hc ω r hr).mono inter_subset_left)).measure
  let E := fun n => {ω | k n < A ω b-A ω 0}
  have hpos n ω : 0 ≤ S n ω := integral_nonneg fun r => Real.rpow_nonneg (abs_nonneg _) p
  have hmean : Tendsto (fun n => ∫ ω, S n ω ∂P) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n => 1/k n) atTop (𝓝 0) from tendsto_one_div_add_atTop_nhds_zero_nat)
    · exact fun n => integral_nonneg (hpos n)
    · exact fun n => (hSsmall n).le
  have hRS (n ω) (hω : ω ∉ E n) : R n ω ≤ S n ω := by
    have hgood : A ω b-A ω 0 ≤ k n := not_lt.1 hω
    have he := capped_stieltjes_measure_agrees 0 b (k n) hb.le (hk n).le (A ω) (hA ω) (hc ω) hgood
    change (∫ r, f n ω r ∂_) ≤ (∫ r, f n ω r ∂_)
    rw [he]
  refine ⟨N,u,V,hmono,hVm,hVbound,?_⟩
  intro ε hε
  exact localized_error_probability_limit P R S E hSi (fun n => .of_forall (hpos n)) hRS
    (finite_real_tail_probability P (fun ω => A ω b-A ω 0) ((hm b).sub (hm 0))) hmean ε hε

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.finite_localized_clipped_step_approximation
