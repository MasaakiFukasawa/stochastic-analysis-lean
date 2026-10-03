import Chapter4FiniteSumPathMoment
import Chapter4BrownianFiniteMoment
import Chapter4ClockRegularity
import Chapter4FiniteItoSum
import Chapter4BrownianSystem

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem brownian_path_L2_envelope_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (R : ℝ) (hR : 0≤R) :
    ∃ G : Ω → ℝ,MemLp G 2 P ∧ (∀ w,0≤G w) ∧
      (∫ w,G w^2 ∂P)≤4*(d:ℝ)^2*R ∧
      ∀ w r,r∈Icc 0 R → ‖WithLp.toLp 2 (fun j => B.W j (realTimeClamp r) w)‖≤G w := by
  have hT : (0:EReal)<⊤ := by simp
  have hex j := by
    have hc : ∀ w (r : ℝ),0≤r → (r:EReal)<⊤ → B.C j j (realTimeClamp r) w=r :=
      fun w r hr _ => B.diagonal_clock j w r hr
    obtain ⟨hm,hc'⟩ := clock_regular_from_identity (B.C j j) hc
    have hi := identity_ito_integral P hT B.F B.mono B.le B.null (B.W j) (B.martingale j)
    exact brownian_ito_finite_path_moment P hT B.F B.mono B.le B.null (B.W j) (B.C j j) (fun _ _ => 1) (B.W j)
      (B.martingale j) (B.cov j j) hm hc' hc (fun _ _ => measurable_const) (fun _ _ _ => continuousAt_const)
      (B.martingale j) hi R hR (EReal.coe_lt_top R) (by simpa using (integrable_const (R-0) : Integrable (fun _ : Ω => R-0) P))
  choose hc hM hbound using hex
  let Z := fun j w => finiteRealPath (B.W j) R (hc j) w
  let G := fun w => ∑ j,‖Z j w‖
  have hGi : MemLp G 2 P := by
    simpa only [Finset.sum_fn] using memLp_finsetSum univ (fun j _ => (hM j).norm)
  have hG w : 0≤G w := sum_nonneg (fun _ _ => norm_nonneg _)
  have hGb : (∫ w,G w^2 ∂P)≤4*(d:ℝ)^2*R := by
    have hi j : Integrable (fun w => ‖Z j w‖^2) P := (hM j).integrable_norm_pow (by norm_num)
    calc
      _ ≤ ∫ w,(d:ℝ)*(∑ j,‖Z j w‖^2) ∂P := integral_mono (hGi.integrable_sq)
        ((integrable_finsetSum univ (fun j _ => hi j)).const_mul d)
        (fun w => by simpa only [G,Finset.card_univ,Fintype.card_fin] using (sq_sum_le_card_mul_sum_sq (s := univ) (f := fun j => ‖Z j w‖)))
      _ = (d:ℝ)*(∑ j,∫ w,‖Z j w‖^2 ∂P) := by
        rw [integral_const_mul,integral_finsetSum _ (fun j _ => hi j)]
      _ ≤ (d:ℝ)*(∑ _j : Fin d,4*R) := mul_le_mul_of_nonneg_left
        (sum_le_sum (fun j _ => by simpa [Z] using hbound j)) (Nat.cast_nonneg _)
      _ = _ := by simp; ring
  refine ⟨G,hGi,hG,hGb,?_⟩
  intro w r hr
  have he j : ‖B.W j (realTimeClamp r) w‖≤‖Z j w‖ := ContinuousMap.norm_coe_le_norm (Z j w) ⟨r,hr⟩
  have hs : ‖WithLp.toLp 2 (fun j => B.W j (realTimeClamp r) w)‖^2≤G w^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply (sum_le_sum (fun j _ => ?_)).trans (sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _))
    simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) (he j) 2
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun j => B.W j (realTimeClamp r) w)),hG w]

end Asakura.Chapter6
