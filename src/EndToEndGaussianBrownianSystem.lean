import EndToEndJointGaussianProduct
import Chapter7NaturalBrownianSystem
import Chapter12FiniteGreekExponents

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Construct the common augmented natural filtration and all local
martingale and covariance witnesses from Gaussian process data. -/
noncomputable def gaussianBrownianSystem {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (Z : Fin d × ℝ≥0 → Ω → ℝ) (hZ : IsGaussianProcess Z P)
    (hm : ∀ q, Measurable (Z q)) (hc : ∀ i ω, Continuous (fun t => Z (i,t) ω))
    (hz : ∀ i, Z (i,0) =ᵐ[P] 0) (hmean : ∀ q, ∫ ω, Z q ω ∂P = 0)
    (hcov : ∀ i j u v, cov[Z (i,u), Z (j,v); P] =
      if i = j then ((min u v : ℝ≥0) : ℝ) else 0) : BrownianSystem P d := by
  let F0 := fun t => Asakura.nullAugmentation (m := m) P (jointPast Z t)
  let F := halfClosedFiltration m F0
  have hF0 : Monotone F0 := fun s t hst => null_augmentation_mono P (jointPast_mono Z hst)
  have hl t : F0 t ≤ m := fun _ he => he.1
  have ha i t : Measurable[F0 t] (Z (i,t)) := by
    apply (jointPast_adapted Z i t).mono _ le_rfl
    intro E hE
    exact ⟨jointPast_le Z hm t E hE, E, hE, EventuallyEq.rfl⟩
  have hM i : LocalMProcessWitness P F (fun t ω => Z (i,halfTimeReal t) ω) := by
    apply half_line_martingale_local P F0 hF0 hl (fun t => Z (i,t)) (ha i)
      (fun t => (hZ.hasGaussianLaw_eval (i,t)).memLp_two) (hc i) _ (hz i)
    intro s t hst
    exact (conditional_null_augmentation P (jointPast Z s) (jointPast_le Z hm s)
      (Z (i,t)) (hZ.hasGaussianLaw_eval (i,t)).integrable).symm.trans
      (gaussian_joint_martingale P Z hZ hm hmean hcov i s t hst)
  have hC i j : LocalCovarianceWitness P F
      (fun t ω => Z (i,halfTimeReal t) ω) (fun t ω => Z (j,halfTimeReal t) ω)
      (fun t _ => if i=j then (halfTimeReal t:ℝ) else 0) := by
    let V := fun t ω => Z (i,t) ω*Z (j,t) ω-(if i=j then (t:ℝ) else 0)
    have hv t : MemLp (V t) 2 P := by
      have hi : MemLp (Z (i,t)) 4 P := (hZ.hasGaussianLaw_eval (i,t)).memLp (by norm_num)
      have hj : MemLp (Z (j,t)) 4 P := (hZ.hasGaussianLaw_eval (j,t)).memLp (by norm_num)
      exact (hi.mul hj).sub (memLp_const _)
    have hva t : Measurable[F0 t] (V t) := ((ha i t).mul (ha j t)).sub measurable_const
    have hvc ω : Continuous (fun t => V t ω) := by
      dsimp only [V]
      split_ifs
      · exact ((hc i ω).mul (hc j ω)).sub continuous_subtype_val
      · exact ((hc i ω).mul (hc j ω)).sub continuous_const
    have hvM : ∀ s t, s ≤ t → P[V t | F0 s] =ᵐ[P] V s := by
      intro s t hst
      exact (conditional_null_augmentation P (jointPast Z s) (jointPast_le Z hm s)
        (V t) ((hv t).integrable (by norm_num))).symm.trans
        (gaussian_joint_product_martingale P Z hZ hm hmean hcov i j s t hst)
    have hv0 : V 0 =ᵐ[P] 0 := by
      filter_upwards [hz i,hz j] with ω hi hj
      simp only [V,hi,hj,Pi.zero_apply,NNReal.coe_zero,ite_self,mul_zero,sub_zero]
    refine ⟨half_line_martingale_local P F0 hF0 hl V hva hv hvc hvM hv0, ?_⟩
    obtain ⟨u,hu,hut,huc⟩ := deterministic_time_exhaustion (show (0:EReal) < ⊤ by simp)
    refine ⟨fun n _ => u n,?_,fun _ => hu,fun n _ => hut n,fun _ => huc,?_⟩
    · intro n t
      by_cases ht : u n ≤ t <;> simp [ht]
    · intro n ω
      refine ⟨fun t => if i=j then (halfTimeReal (min (u n) t):ℝ) else 0,
        fun _ => 0,?_,monotone_const,fun t => (sub_zero _).symm⟩
      split_ifs
      · intro s t hst
        exact half_time_real_mono ((monotone_const.min monotone_id) hst)
          ((min_le_left _ _).trans_lt (hut n))
      · exact monotone_const
  refine {
    F := F
    mono := half_closed_filtration_mono m F0 hF0 hl
    le := half_closed_filtration_le m F0 hl
    null := ?_
    W := fun i t ω => Z (i,halfTimeReal t) ω
    C := fun i j t _ => if i=j then (halfTimeReal t:ℝ) else 0
    martingale := hM
    cov := hC
    clock := ?_ }
  · intro t E hmE hzE
    by_cases ht : t < ⊤
    · have hi : F0 (halfTimeReal t) ≤ F t := by simp only [F,halfClosedFiltration,if_pos ht,le_refl]
      exact hi E (null_augmentation_null P (jointPast Z (halfTimeReal t)) E hmE hzE)
    · have hi : m ≤ F t := by simp only [F,halfClosedFiltration,if_neg ht,le_refl]
      exact hi E hmE
  · intro i j ω r hr
    split_ifs
    · exact changed_time_real r hr
    · rfl

end Asakura.EndToEnd

#print axioms Asakura.EndToEnd.gaussianBrownianSystem
