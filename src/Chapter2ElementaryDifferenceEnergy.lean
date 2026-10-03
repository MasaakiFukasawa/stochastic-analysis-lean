import Chapter2FiniteElementaryEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The actual quadratic variation of differences of two elementary
integrals is their squared-integrand difference. The representations may
have different grids and different finite horizons. -/
theorem elementary_difference_energy
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c) (hcT : ∀ n, (c n:EReal) < T)
    (hAm : ∀ n ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (hAc : ∀ n ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (N : ℕ → ℕ) (u : ℕ → ℕ → ℝ) (V : ℕ → ℕ → Ω → ℝ)
    (hu : ∀ n, StrictMonoOn (u n) (Iic (N n)))
    (hub : ∀ n i, i ≤ N n → u n i ∈ Icc 0 (c n))
    (hVm : ∀ n i, i < N n → Measurable[F (realTimeClamp (u n i))] (V n i))
    (hVi : ∀ n i, i < N n → MemLp (V n i) ∞ P) :
    let Z := fun n t ω => ∑ i ∈ Finset.range (N n), V n i ω*
      stepIncrement (realTimeClamp (u n i)) (realTimeClamp (u n (i+1))) (fun t => X t ω) t
    let H := fun n ω r => ∑ i ∈ Finset.range (N n),
      (Ico (u n i) (u n (i+1))).indicator (fun _ => V n i ω) r
    ∀ n k, ∃ Q, LocalCovarianceWitness P F (fun t ω => Z n t ω-Z k t ω)
      (fun t ω => Z n t ω-Z k t ω) Q ∧
      ∀ᵐ ω ∂P, ∀ j, j ≤ max n k →
        Q (realTimeClamp (c j)) ω = ∫ r, (H n ω r-H k ω r)^2
          ∂(intervalStieltjes 0 (c j) (hc j) (fun r => A (realTimeClamp r) ω) (hAm j ω)
            (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure := by
  classical
  intro Z H n k
  let l := max n k
  let s := (Finset.range (N n)).disjSum (Finset.range (N k))
  let a := Sum.elim (u n) (u k)
  let b := Sum.elim (fun i => u n (i+1)) (fun i => u k (i+1))
  let G := Sum.elim (V n) (fun i ω => -V k i ω)
  have hinc q i (hi : i < N q) : u q i ≤ u q (i+1) :=
    (hu q).monotoneOn hi.le (show i+1 ∈ Iic (N q) by change i+1 ≤ N q; omega) (by omega)
  have hbnd q (hq : q ≤ l) i (hi : i ≤ N q) : u q i ∈ Icc 0 (c l) :=
    ⟨(hub q i hi).1,(hub q i hi).2.trans (hcm hq)⟩
  have ha i (hi : i ∈ s) : a i ∈ Icc 0 (c l) := by
    cases i with
    | inl i => exact hbnd n (le_max_left _ _) i (by simpa [s] using hi : i < N n).le
    | inr i => exact hbnd k (le_max_right _ _) i (by simpa [s] using hi : i < N k).le
  have hb i (hi : i ∈ s) : b i ∈ Icc 0 (c l) := by
    cases i with
    | inl i => exact hbnd n (le_max_left _ _) (i+1) (by
        have hh : i < N n := by simpa [s] using hi
        omega)
    | inr i => exact hbnd k (le_max_right _ _) (i+1) (by
        have hh : i < N k := by simpa [s] using hi
        omega)
  have hab i (hi : i ∈ s) : a i ≤ b i := by
    cases i with
    | inl i => exact hinc n i (by simpa [s] using hi)
    | inr i => exact hinc k i (by simpa [s] using hi)
  have hGm i (hi : i ∈ s) : Measurable[F (realTimeClamp (a i))] (G i) := by
    cases i with
    | inl i => exact hVm n i (by simpa [s] using hi)
    | inr i => exact (hVm k i (by simpa [s] using hi)).neg
  have hGi i (hi : i ∈ s) : MemLp (G i) ∞ P := by
    cases i with
    | inl i => exact hVi n i (by simpa [s] using hi)
    | inr i => exact (hVi k i (by simpa [s] using hi)).neg
  have heZ : (fun t ω => ∑ i ∈ s, G i ω*stepIncrement (realTimeClamp (a i)) (realTimeClamp (b i)) (fun t => X t ω) t) =
      (fun t ω => Z n t ω-Z k t ω) := by
    funext t ω
    simp only [s,G,a,b,Finset.sum_disjSum,Sum.elim_inl,Sum.elim_inr,neg_mul,Finset.sum_neg_distrib]
    rfl
  have heH ω r : (∑ i ∈ s, (Ico (a i) (b i)).indicator (fun _ => G i ω) r) = H n ω r-H k ω r := by
    simp only [s,G,a,b,Finset.sum_disjSum,Sum.elim_inl,Sum.elim_inr]
    have he i : (Ico (u k i) (u k (i+1))).indicator (fun _ => -V k i ω) r =
        -(Ico (u k i) (u k (i+1))).indicator (fun _ => V k i ω) r := by
      by_cases hr : r ∈ Ico (u k i) (u k (i+1)) <;> simp [hr]
    simp only [he,Finset.sum_neg_distrib]
    rfl
  obtain ⟨_,Q,hQ,hQi⟩ := finite_elementary_stieltjes_energy P F hF hle hnull X A hX hA
    (c l) (hc l) (hcT l) (hAm l) s a b G hab ha hb hGm hGi
  rw [heZ] at hQ
  refine ⟨Q,hQ,?_⟩
  filter_upwards [hQi] with ω hω
  intro j hj
  obtain ⟨hr,heq⟩ := hω (c j) ⟨hc j,hcm hj⟩
  rw [heq]
  have hrest := interval_stieltjes_restrict_Iic 0 (c l) (c j) (hc j) (hcm hj)
    (fun r => A (realTimeClamp r) ω) (hAm l ω) hr (hAm j ω)
      (fun r hr => (hAc j ω r hr).mono inter_subset_left)
  rw [← hrest]
  apply integral_congr_ae
  exact .of_forall (fun r => congrArg (fun x : ℝ => x^2) (heH ω r))

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.elementary_difference_energy
