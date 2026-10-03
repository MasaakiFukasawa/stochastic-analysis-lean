import Chapter4EulerCellMoment
import Chapter4CoefficientPointMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

lemma coefficient_square_expectation_bound
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → E) (hY : MemLp Y 2 P)
    (b : E → ℝ) (hb : MemLp (fun w => b (Y w)) 2 P)
    (K : ℝ) (hK : 0≤K) (hg : ∀ x,(b x)^2≤K*(1+‖x‖^2)) :
    (∫ w,(b (Y w))^2 ∂P)≤K*(1+∫ w,‖Y w‖^2 ∂P) := by
  have hi := hY.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hh := integral_mono ((memLp_two_iff_integrable_sq hb.aestronglyMeasurable).1 hb)
    (((integrable_const (1:ℝ)).add hi).const_mul K) (fun w => hg (Y w))
  simpa only [Pi.add_apply,integral_const_mul,integral_add (integrable_const (1:ℝ)) hi,
    integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

/-- An actual Brownian Euler cell has order-h mean square increment;
the bound uses only the second moment at the left endpoint. -/
theorem brownian_cell_growth_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hA : ∀ j,LocalCovarianceWitness P F (W j) (W j) (A j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → A j (realTimeClamp r) w=r)
    (r : ℝ) (hr : 0≤r) (hrT : (r:EReal)<T) (s : ℝ) (hs : s∈Icc 0 r)

    (Y : Ω → Fin dim → ℝ) (hYa : Measurable[F (realTimeClamp s)] Y) (hY : MemLp Y 2 P)
    (b : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (L : ℝ) (hL : 0≤L)
    (hb : ∀ i x y,(b i x-b i y)^2≤L*‖x-y‖^2)
    (hσ : ∀ i j x y,(σ i j x-σ i j y)^2≤L*‖x-y‖^2)
    (K : ℝ) (hK : 0≤K)
    (hbg : ∀ i x,(b i x)^2≤K*(1+‖x‖^2))
    (hσg : ∀ i j x,(σ i j x)^2≤K*(1+‖x‖^2))
    (R h : ℝ) (hh : 0≤h) (hhR : h≤R) (hrs : r-s≤h) :
    let D := fun w i => b i (Y w)*(r-s)+∑ j,σ i j (Y w)*(W j (realTimeClamp r) w-W j (realTimeClamp s) w)
    MemLp D 2 P ∧
    (∫ w,‖D w‖^2 ∂P)≤(2*(dim:ℝ)*(R+(noise:ℝ)^2)*K)*(1+∫ w,‖Y w‖^2 ∂P)*h := by
  have hbi i := square_lipschitz_coefficient_memLp P (b i) L hL (hb i) Y hY
  have hσi i j := square_lipschitz_coefficient_memLp P (σ i j) L hL (hσ i j) Y hY
  obtain ⟨hDi,hDb⟩ := brownian_cell_square_moment P hT F hF hle hnull W A hW hA hclock
    r hr hrT s hs (fun i w => b i (Y w)) (fun i j w => σ i j (Y w)) hbi
    (fun i j => (Vector.coordinate_continuous_of_square_lipschitz (σ i j) L hL (hσ i j)).measurable.comp hYa) hσi
  refine ⟨hDi,hDb.trans ?_⟩
  let B := K*(1+∫ w,‖Y w‖^2 ∂P)
  have hB : 0≤B := mul_nonneg hK (by positivity)
  have hbm : (∑ i,∫ w,(b i (Y w))^2 ∂P)≤(dim:ℝ)*B := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
      Finset.sum_le_sum (s:=Finset.univ) (fun i _ => coefficient_square_expectation_bound P Y hY (b i) (hbi i) K hK (hbg i))
  have hsm : (∑ i,∑ j,∫ w,(σ i j (Y w))^2 ∂P)≤(dim:ℝ)*((noise:ℝ)*B) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
      Finset.sum_le_sum (s:=Finset.univ) (fun i _ => Finset.sum_le_sum (s:=Finset.univ)
        (fun j _ => coefficient_square_expectation_bound P Y hY (σ i j) (hσi i j) K hK (hσg i j)))
  have hd : 0≤r-s := sub_nonneg.mpr hs.2
  have hd2 : (r-s)^2≤R*h := by nlinarith [mul_nonneg hh (sub_nonneg.mpr hhR)]
  have hb1 := mul_le_mul_of_nonneg_left hbm (show 0≤2*(r-s)^2 by positivity)
  have hb2 := mul_le_mul_of_nonneg_left hsm (show 0≤2*(noise:ℝ)*(r-s) by positivity)
  have hc1 := mul_le_mul_of_nonneg_right hd2 (show 0≤2*(dim:ℝ)*B by positivity)
  have hc2 := mul_le_mul_of_nonneg_right hrs (show 0≤2*(noise:ℝ)*(dim:ℝ)*(noise:ℝ)*B by positivity)
  dsimp only [B] at *
  nlinarith only [hb1,hb2,hc1,hc2]

end Asakura.Chapter4
