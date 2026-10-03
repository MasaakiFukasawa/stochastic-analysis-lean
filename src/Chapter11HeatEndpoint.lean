import Chapter11HeatGaussianRepresentation
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.HeineCantor

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace Asakura.Chapter11
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem gaussian_exp_abs_integrable (a : ℝ) :
    Integrable (fun z => Real.exp (a*|z|)) (gaussianReal 0 1) := by
  apply ((integrable_exp_mul_gaussianReal (μ:=0) (v:=1) a).add
    (integrable_exp_mul_gaussianReal (μ:=0) (v:=1) (-a))).mono' (by fun_prop)
  apply ae_of_all
  intro z
  simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Pi.add_apply]
  by_cases hz : 0≤z
  · rw [abs_of_nonneg hz]
    linarith [Real.exp_pos (-a*z)]
  · simp only [abs_of_neg (lt_of_not_ge hz),mul_neg,neg_mul]
    linarith [Real.exp_pos (a*z)]

theorem exponential_heat_average_continuous_box (f : ℝ → ℝ) (hf : Continuous f)
    (C m T R : ℝ) (hC : 0≤C) (hT : 0≤T) (hR : 0≤R)
    (hb : ∀ z,|f z|≤C*(1+Real.exp (m*z))) :
    ContinuousOn (fun q : ℝ × ℝ => ∫ z,f (q.2+Real.sqrt q.1*z) ∂gaussianReal 0 1)
      (Icc (-T) T ×ˢ Icc (-R) R) := by
  let A := Real.exp (|m| *R)
  let D := |m| *Real.sqrt T
  apply continuousOn_of_dominated (bound:=fun z => C*(1+A*Real.exp (D*|z|)))
  · intro q hq
    exact (hf.comp (by fun_prop)).aestronglyMeasurable
  · intro q hq
    apply ae_of_all
    intro z
    rw [Real.norm_eq_abs]
    apply (hb _).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply add_le_add_right
    dsimp only [A,D]
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hy : |q.2|≤R := abs_le.mpr hq.2
    have hs : Real.sqrt q.1≤Real.sqrt T := Real.sqrt_le_sqrt hq.1.2
    have hh : |q.2+Real.sqrt q.1*z|≤R+Real.sqrt T*|z| := by
      apply (abs_add_le _ _).trans
      rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
      exact add_le_add hy (mul_le_mul_of_nonneg_right hs (abs_nonneg _))
    have hh' := mul_le_mul_of_nonneg_left hh (abs_nonneg m)
    have hm : m*(q.2+Real.sqrt q.1*z)≤|m| *|q.2+Real.sqrt q.1*z| := by rw [←abs_mul];exact le_abs_self _
    nlinarith
  · exact ((integrable_const (1:ℝ)).add ((gaussian_exp_abs_integrable D).const_mul A)).const_mul C
  · exact ae_of_all _ fun z => (hf.comp (by fun_prop)).continuousOn

theorem exponential_heat_average_continuous (f : ℝ → ℝ) (hf : Continuous f)
    (C m : ℝ) (hC : 0≤C) (hb : ∀ z,|f z|≤C*(1+Real.exp (m*z))) :
    Continuous (fun q : ℝ × ℝ => ∫ z,f (q.2+Real.sqrt q.1*z) ∂gaussianReal 0 1) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  let T := |q.1|+1
  let R := |q.2|+1
  have hT : 0≤T := by dsimp [T];positivity
  have hR : 0≤R := by dsimp [R];positivity
  have ht1 : -T<q.1 := by dsimp [T];linarith [neg_abs_le q.1]
  have ht2 : q.1<T := by dsimp [T];linarith [le_abs_self q.1]
  have hr1 : -R<q.2 := by dsimp [R];linarith [neg_abs_le q.2]
  have hr2 : q.2<R := by dsimp [R];linarith [le_abs_self q.2]
  exact (exponential_heat_average_continuous_box f hf C m T R hC hT hR hb).continuousAt
    (prod_mem_nhds (Icc_mem_nhds ht1 ht2) (Icc_mem_nhds hr1 hr2))

/-- Compact-uniform convergence at maturity, proved for the exponential
rather than bounded growth actually allowed in the manuscript. -/
theorem exponential_heat_uniform_endpoint (f : ℝ → ℝ) (hf : Continuous f)
    (C m : ℝ) (hC : 0≤C) (hb : ∀ z,|f z|≤C*(1+Real.exp (m*z)))
    (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun t y => ∫ z,f (y+Real.sqrt t*z) ∂gaussianReal 0 1) f
      (𝓝[Icc (0:ℝ) 1] 0) K := by
  obtain ⟨R0,hR0⟩ := hK.exists_bound_of_continuousOn (continuous_id.continuousOn : ContinuousOn (fun y : ℝ => y) K)
  let R := max 0 R0
  have hKR : K⊆Icc (-R) R := by
    intro y hy
    apply abs_le.mp
    have hh : |y|≤R0 := by simpa only [Real.norm_eq_abs,id_eq] using hR0 y hy
    exact hh.trans (le_max_right _ _)
  have htime : Icc (0:ℝ) 1 ⊆ Icc (-1:ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [ht.1],ht.2⟩
  have hc := (exponential_heat_average_continuous_box f hf C m 1 R hC (by norm_num) (le_max_left _ _) hb).mono
    (prod_mono htime hKR)
  have hu := (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hc
  have hh := UniformContinuousOn.tendstoUniformlyOn
    (F:=fun t y => ∫ z,f (y+Real.sqrt t*z) ∂gaussianReal 0 1)
    (by convert hu using 1;funext q;rcases q with ⟨t,y⟩;rfl) (show (0:ℝ)∈Icc 0 1 by simp)
  simpa using hh

end Asakura.Chapter11
