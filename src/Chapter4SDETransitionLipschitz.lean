import Chapter4SDEInitialStability
import Chapter4TransitionLipschitz

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

lemma endpoint_second_moment_le_euclidean_path
    {Ω D : Type*} [MeasurableSpace Ω] [MetricSpace D] [CompactSpace D] [SecondCountableTopology D]
    {dim : ℕ} (P : Measure Ω) (Y : Ω → C(D,Fin dim → ℝ)) (hm : Measurable Y) (hi : MemLp Y 2 P) (r : D) :
    (∫ w,‖Y w r‖^2 ∂P)≤∫ w,‖squaredEuclideanPath (Y w)‖ ∂P := by
  apply integral_mono ((random_path_evaluation_memLp P Y hm hi r).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    (squared_euclidean_path_expected_bound P Y hm hi).1
  intro w
  have hh := pi_norm_sq_le_sum_sq (Y w r)
  have hb := (squaredEuclideanPath (Y w)).norm_coe_le_norm r
  change ‖∑ i,(Y w r i)^2‖≤_ at hb
  rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at hb
  exact hh.trans hb

/-- The transition operator of the constructed SDE maps bounded Lipschitz
functions to Lipschitz functions, by the actual initial-state estimate. -/
theorem sde_transition_preserves_lipschitz
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] {dim noise : ℕ}
    (B : BrownianSystem P noise) (L : ℝ) (hL : 0≤L)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hLip : ∀ x y,(∑ i,(μ i x-μ i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2)
    (Z : (Fin dim → ℝ) → HalfClosedTime → Ω → Fin dim → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W μ σ (fun _ => x) (Z x))
    (R : ℝ) (hR : 0≤R) :
    ∃ C : ℝ≥0,∀ (f : (Fin dim → ℝ) → ℝ) (Lf : ℝ≥0),LipschitzWith Lf f →
      ∀ K : ℝ,(∀ x,‖f x‖≤K) → LipschitzWith (Lf*C) (fun x => ∫ w,f (Z x (realTimeClamp R) w) ∂P) := by
  letI : MeasurableSpace Ω := m
  let A := (dim:ℝ)*2*Real.exp ((2*((dim:ℝ)*(2*R+8*(noise:ℝ)^2)*(L*dim))+1)*R)
  have hA : 0≤A := by dsimp only [A];positivity
  have hd x := sde_finite_path_memLp P (EReal.coe_lt_top 0) rfl B.F B.mono B.le B.null
    B.W (fun j => B.C j j) B.martingale (fun j => B.cov j j) (fun j w r hr _ => B.diagonal_clock j w r hr)
    L hL μ σ hLip (fun _ => x) (memLp_const x) (Z x) (hZ x) R hR (EReal.coe_lt_top R)
  have hm x : Measurable[m] (Z x (realTimeClamp R)) :=
    ((hZ x).adapted _ (real_time_below R hR (EReal.coe_lt_top R))).mono (B.le _) le_rfl
  have hs x y : (∫ w,‖Z x (realTimeClamp R) w-Z y (realTimeClamp R) w‖^2 ∂P)≤(A*dim)*‖x-y‖^2 := by
    have hpath := endpoint_second_moment_le_euclidean_path P
      (fun w => Vector.realVectorPath (Z x) (hZ x).path R (EReal.coe_lt_top R) w-
        Vector.realVectorPath (Z y) (hZ y).path R (EReal.coe_lt_top R) w)
      ((hd x).1.sub (hd y).1) ((hd x).2.1.sub (hd y).2.1) ⟨R,right_mem_Icc.mpr hR⟩
    have hstab := sde_initial_stability_euclidean P B L hL μ σ hLip
      (fun _ => x) (fun _ => y) (memLp_const x) (memLp_const y) (Z x) (Z y) (hZ x) (hZ y) R hR
    have hsum : (∑ i,(x i-y i)^2)≤(dim:ℝ)*‖x-y‖^2 := by
      calc
        _ ≤ ∑ i : Fin dim,‖x-y‖^2 := Finset.sum_le_sum (fun i _ => by
          have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm (x-y) i) 2
          simpa only [Pi.sub_apply,Real.norm_eq_abs,sq_abs] using hh)
        _ = _ := by simp
    have hh := hpath.trans hstab
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hh
    exact hh.trans (by simpa only [A,mul_assoc] using mul_le_mul_of_nonneg_left hsum hA)
  refine ⟨⟨Real.sqrt (A*dim),Real.sqrt_nonneg _⟩,?_⟩
  intro f Lf hf K hb
  have hh := transition_operator_lipschitz_of_square_stability P
    (fun x => Z x (realTimeClamp R)) hm (fun x => (hd x).2.2) (A*dim) (by positivity) hs f Lf hf K hb
  exact hh

end Asakura.Chapter4
