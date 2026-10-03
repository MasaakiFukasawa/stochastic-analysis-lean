import Chapter4PredictableBrownianIncrement
import Chapter4FiniteSumPathMoment
import Mathlib.MeasureTheory.SpecificCodomains.Pi

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The within-cell estimate for the actual Brownian interpolation, with
all product integrability supplied by left-endpoint independence. -/
theorem brownian_cell_square_moment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hA : ∀ j,LocalCovarianceWitness P F (W j) (W j) (A j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → A j (realTimeClamp r) w=r)
    (r : ℝ) (hr : 0≤r) (hrT : (r:EReal)<T) (s : ℝ) (hs : s∈Icc 0 r)
    (b : Fin dim → Ω → ℝ) (σ : Fin dim → Fin noise → Ω → ℝ)
    (hb : ∀ i,MemLp (b i) 2 P)
    (hσa : ∀ i j,Measurable[F (realTimeClamp s)] (σ i j))
    (hσ : ∀ i j,MemLp (σ i j) 2 P) :
    let D := fun w i => b i w*(r-s)+∑ j,σ i j w*(W j (realTimeClamp r) w-W j (realTimeClamp s) w)
    MemLp D 2 P ∧
    (∫ w,‖D w‖^2 ∂P)≤2*(r-s)^2*(∑ i,∫ w,b i w^2 ∂P)+
      2*(noise:ℝ)*(r-s)*(∑ i,∑ j,∫ w,σ i j w^2 ∂P) := by
  dsimp only
  let Z := fun i j w => σ i j w*(W j (realTimeClamp r) w-W j (realTimeClamp s) w)
  let D := fun w i => b i w*(r-s)+∑ j,Z i j w
  have hz i j := predictable_brownian_increment_square_moment P hT F hF hle hnull
    (W j) (A j) (hW j) (hA j) (hclock j) r hr hrT s hs (σ i j) (hσa i j) (hσ i j)
  have hsum i := finite_sum_path_moment P (Z i) (fun j => (hz i j).1)
  have hadd i := path_sum_square_moment P (fun w => b i w*(r-s)) (fun w => ∑ j,Z i j w)
    ((hb i).mul_const (r-s)) (hsum i).1
  have hDi : MemLp D 2 P := memLp_pi_iff.mpr fun i => (hadd i).1
  have hcoord i : (∫ w,(D w i)^2 ∂P)≤2*(r-s)^2*(∫ w,b i w^2 ∂P)+
      2*(noise:ℝ)*(r-s)*(∑ j,∫ w,σ i j w^2 ∂P) := by
    have he1 : (∫ w,‖b i w*(r-s)‖^2 ∂P)=(r-s)^2*(∫ w,b i w^2 ∂P) := by
      simp only [Real.norm_eq_abs,sq_abs,mul_pow,integral_mul_const]
      ring
    have he2 : (∑ j,∫ w,‖Z i j w‖^2 ∂P)=(r-s)*(∑ j,∫ w,σ i j w^2 ∂P) := by
      simp only [Real.norm_eq_abs,sq_abs,Z,(hz i _).2,Finset.mul_sum]
    have hh := (hadd i).2
    rw [he1] at hh
    have hs' := (hsum i).2
    rw [he2] at hs'
    simp only [Real.norm_eq_abs,sq_abs] at hh hs'
    dsimp only [D]
    nlinarith only [hh,hs']
  refine ⟨hDi,?_⟩
  have hbnd : (∫ w,‖D w‖^2 ∂P)≤∑ i,∫ w,(D w i)^2 ∂P := by
    have hci i := (memLp_two_iff_integrable_sq ((memLp_pi_iff.mp hDi i).aestronglyMeasurable)).1 (memLp_pi_iff.mp hDi i)
    rw [← integral_finsetSum Finset.univ (fun i _ => hci i)]
    apply integral_mono (hDi.integrable_norm_pow (by norm_num : (2:ℕ)≠0))
      (integrable_finsetSum Finset.univ (fun i _ => hci i))
    exact fun w => pi_norm_sq_le_sum_sq (D w)
  apply hbnd.trans
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hcoord i)
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum] using hh

end Asakura.Chapter4
