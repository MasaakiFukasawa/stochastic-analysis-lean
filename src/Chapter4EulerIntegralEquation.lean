import Chapter4EulerInterpolationAlgebra
import Chapter4UnboundedElementaryIto
import Chapter4ElementaryTimeIntegral
import Chapter4FiniteItoSum
import Chapter4M2FinitePath

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- The actual Euler interpolation satisfies its drift-plus-Ito equation.
The stochastic terms are constructed from the grid recursion, not assumed. -/
theorem euler_interpolation_ito_equation
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
    (h : ℝ) (hh : 0≤h)
    (n : ℕ) (hnT : (((n:ℝ)*h : ℝ):EReal)<T) :
    let Wr := fun j r => W j (realTimeClamp r)
    let Y := eulerGrid μ σ Wr ξ h
    ∃ N : Fin dim → Fin noise → ClosedTime T → Ω → ℝ,
      (∀ i j,ContinuousM2Witness P F (N i j)) ∧
      (∀ i j,LocalMProcessWitness P F (N i j)) ∧
      (∀ i j,ItoCovarianceFormula P F (W j)
        (fun z => ∑ k∈Finset.range n,(Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)).indicator (fun _ => σ i j (Y k z.1)) z.2) (N i j)) ∧
      (∀ w r,0≤r → ∀ i,eulerInterpolation μ σ Wr ξ h n r w i=ξ w i+
        (∫ a in 0..r,∑ k∈Finset.range n,(Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)).indicator (fun _ => μ i (Y k w)) a)+
        ∑ j,N i j (realTimeClamp r) w) := by
  classical
  dsimp only
  let Wr := fun j r => W j (realTimeClamp r)
  let Y := eulerGrid μ σ Wr ξ h
  let Z := fun k i j t w => σ i j (Y k w)*
    (W j (min (realTimeClamp (((k:ℝ)+1)*h)) t) w-W j (min (realTimeClamp ((k:ℝ)*h)) t) w)
  have hY := euler_grid_adapted_memLp P hT F hF hle hnull W A hW hA hclock μ σ L hL hμ hσ ξ hξa hξ h hh
  have hstep k (hk : k∈Finset.range n) i j := by
    have hkn : k+1≤n := Finset.mem_range.mp hk
    have hkh : (k:ℝ)*h≤((k:ℝ)+1)*h := by nlinarith
    have hnh : ((k:ℝ)+1)*h≤(n:ℝ)*h := mul_le_mul_of_nonneg_right (by exact_mod_cast hkn) hh
    have hkT : ((((k:ℝ)+1)*h : ℝ):EReal)<T := (EReal.coe_le_coe hnh).trans_lt hnT
    have hy := hY k ((EReal.coe_le_coe hkh).trans_lt hkT)
    exact brownian_elementary_ito_constructed P hT F hF hle hnull (W j) (A j) (hW j) (hA j) (hclock j)
      (((k:ℝ)+1)*h) (by positivity) hkT ((k:ℝ)*h) ⟨by positivity,hkh⟩
      (fun w => σ i j (Y k w))
      ((Vector.coordinate_continuous_of_square_lipschitz (σ i j) L hL (hσ i j)).measurable.comp hy.1)
      (square_lipschitz_coefficient_memLp P (σ i j) L hL (hσ i j) (Y k) hy.2)
  let N := fun i j t w => ∑ k∈Finset.range n,Z k i j t w
  refine ⟨N,?_,?_,?_,?_⟩
  · intro i j
    exact continuous_m2_finset_sum P F hF hle (Finset.range n) (fun k => Z k i j)
      (fun k hk => (hstep k hk i j).1)
  · intro i j
    exact local_martingale_finset_sum P hT F hF hle (Finset.range n) (fun k => Z k i j)
      (fun k hk => (hstep k hk i j).2.1)
  · intro i j
    exact finite_ito_sum P hT F hF hle hnull (W j) (hW j) (Finset.range n)
      (fun k z => (Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)).indicator (fun _ => σ i j (Y k z.1)) z.2)
      (fun k => Z k i j) (fun k hk => (hstep k hk i j).2.2)
  · intro w r hr i
    have hi (k : ℕ) : IntervalIntegrable (fun a => (Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)).indicator (fun _ => μ i (Y k w)) a) volume 0 r := by
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).mpr
      exact (integrable_const _).indicator measurableSet_Ioc
    rw [intervalIntegral.integral_finsetSum (fun k _ => hi k)]
    have ht (k : ℕ) := interval_indicator_constant_integral ((k:ℝ)*h) (((k:ℝ)+1)*h) r
      (μ i (Y k w)) (by positivity) (by nlinarith) hr
    simp_rw [ht]
    have hmin (a b : ℝ) : realTimeClamp (T:=T) (min a b)=min (realTimeClamp a) (realTimeClamp b) :=
      real_time_clamp_mono.map_min
    dsimp only [eulerInterpolation,N,Z,Wr,Y]
    simp only [hmin,Finset.sum_add_distrib]
    rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.range n)]
    ring

end Asakura.Chapter4
