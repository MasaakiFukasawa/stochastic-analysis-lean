import Chapter4PredictableBrownianIncrement
import Chapter4CoefficientPointMoment
import Mathlib.MeasureTheory.SpecificCodomains.Pi

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

noncomputable def eulerGrid {Ω : Type*} {dim noise : ℕ}
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (W : Fin noise → ℝ → Ω → ℝ) (ξ : Ω → Fin dim → ℝ) (h : ℝ) : ℕ → Ω → Fin dim → ℝ
  | 0 => ξ
  | k+1 => fun w i => eulerGrid μ σ W ξ h k w i+μ i (eulerGrid μ σ W ξ h k w)*h+
      ∑ j,σ i j (eulerGrid μ σ W ξ h k w)*(W j ((k+1)*h) w-W j (k*h) w)

/-- The Euler recursion itself constructs adapted, square-integrable grid
values, without adding boundedness of coefficients or the initial value. -/
theorem euler_grid_adapted_memLp
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hA : ∀ j,LocalCovarianceWitness P F (W j) (W j) (A j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → A j (realTimeClamp r) w=r)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (L : ℝ) (hL : 0≤L)
    (hμ : ∀ i x y,(μ i x-μ i y)^2≤L*‖x-y‖^2)
    (hσ : ∀ i j x y,(σ i j x-σ i j y)^2≤L*‖x-y‖^2)
    (ξ : Ω → Fin dim → ℝ) (hξa : Measurable[F ⊥] ξ) (hξ : MemLp ξ 2 P)
    (h : ℝ) (hh : 0≤h) :
    ∀ k : ℕ,(((k:ℝ)*h : ℝ):EReal)<T →
      Measurable[F (realTimeClamp ((k:ℝ)*h))] (eulerGrid μ σ (fun j r => W j (realTimeClamp r)) ξ h k) ∧
      MemLp (eulerGrid μ σ (fun j r => W j (realTimeClamp r)) ξ h k) 2 P := by
  let Y := eulerGrid μ σ (fun j r => W j (realTimeClamp r)) ξ h
  have hμc i := Vector.coordinate_continuous_of_square_lipschitz (μ i) L hL (hμ i)
  have hσc i j := Vector.coordinate_continuous_of_square_lipschitz (σ i j) L hL (hσ i j)
  have hz : realTimeClamp (T:=T) 0=⊥ := by
    apply Subtype.ext
    exact real_time_clamp_eq 0 le_rfl hT.le
  intro k
  induction k with
  | zero =>
    intro _
    constructor
    · convert hξa using 1
      · congr 1
        convert hz using 1 <;> norm_num
      · rfl
    · exact hξ
  | succ k ih =>
    intro hkT
    have hk0 : 0≤(k:ℝ)*h := by positivity
    have hs0 : 0≤((k:ℝ)+1)*h := by positivity
    have hks : (k:ℝ)*h≤((k:ℝ)+1)*h := by nlinarith
    have hsT : ((((k:ℝ)+1)*h : ℝ):EReal)<T := by simpa only [Nat.cast_add,Nat.cast_one] using hkT
    obtain ⟨hYa,hYi⟩ := ih ((EReal.coe_le_coe hks).trans_lt hsT)
    have hYas := hYa.mono (hF (real_time_clamp_mono hks)) le_rfl
    have hinc i j := predictable_brownian_increment_square_moment P hT F hF hle hnull
      (W j) (A j) (hW j) (hA j) (hclock j) (((k:ℝ)+1)*h) hs0 hsT ((k:ℝ)*h) ⟨hk0,hks⟩
      (fun w => σ i j (Y k w)) ((hσc i j).measurable.comp hYa)
      (square_lipschitz_coefficient_memLp P (σ i j) L hL (hσ i j) (Y k) hYi)
    have he : Y (k+1)=fun w i => Y k w i+μ i (Y k w)*h+
        ∑ j,σ i j (Y k w)*(W j (realTimeClamp (((k:ℝ)+1)*h)) w-W j (realTimeClamp ((k:ℝ)*h)) w) := rfl
    have had : Measurable[F (realTimeClamp (((k:ℝ)+1)*h))] (Y (k+1)) := by
      letI : MeasurableSpace Ω := F (realTimeClamp (((k:ℝ)+1)*h))
      rw [he]
      apply measurable_pi_iff.mpr
      intro i
      apply (((measurable_pi_apply i).comp hYas).add (((hμc i).measurable.comp hYas).mul_const h)).add
      apply Finset.measurable_sum
      intro j _
      exact ((hσc i j).measurable.comp hYas).mul
        (((hW j).adapted P F _ (real_time_below _ hs0 hsT)).sub
          (((hW j).adapted P F _ (real_time_below _ hk0 ((EReal.coe_le_coe hks).trans_lt hsT))).mono
            (hF (real_time_clamp_mono hks)) le_rfl))
    constructor
    · convert had using 1
      congr 1
      norm_cast
    · change MemLp (Y (k+1)) 2 P
      rw [he]
      apply memLp_pi_iff.mpr
      intro i
      have hi := (memLp_pi_iff.mp hYi i).add
        ((square_lipschitz_coefficient_memLp P (μ i) L hL (hμ i) (Y k) hYi).mul_const h)
      have hj := memLp_finsetSum' Finset.univ (fun j _ => (hinc i j).1)
      convert hi.add hj using 1
      funext w
      simp only [Pi.add_apply,Finset.sum_apply]
      rfl

end Asakura.Chapter4
