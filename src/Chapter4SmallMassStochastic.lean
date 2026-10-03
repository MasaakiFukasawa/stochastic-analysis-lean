import Chapter4SmallMassKernel
import Chapter4SmallMassInitial
import Chapter4DeterministicItoEnergy
import Chapter3ContinuousIntegralConstruction

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The displayed mass-dependent convolution, built from actual Ito
integrals, converges in mean square to the displayed OU convolution. -/
theorem langevin_small_mass_stochastic_limit
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤mΩ)
    (hnull : ∀ t E,MeasurableSet[mΩ] E → P E=0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (κ γ σ R y v : ℝ) (hκ : 0<κ) (hγ : 0<γ) (hR : 0<R) (hRT : (R:EReal)<T) :
    ∃ (N : ℝ → ClosedTime T → Ω → ℝ) (Z : ClosedTime T → Ω → ℝ),
      (∀ m,LocalMProcessWitness P F (N m)) ∧ LocalMProcessWitness P F Z ∧
      (∀ m,ItoCovarianceFormula P F W (fun z => langevinKernel κ γ σ m (R-z.2)) (N m)) ∧
      ItoCovarianceFormula P F W (fun z => σ/γ*Real.exp (-κ/γ*(R-z.2))) Z ∧
      Tendsto (fun m => ∫ w,(langevinInitial κ γ m R y v+N m (realTimeClamp R) w-
        (Real.exp (-κ/γ*R)*y+Z (realTimeClamp R) w))^2 ∂P)
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hgc m : Continuous (fun r => langevinKernel κ γ σ m (R-r)) := by
    dsimp only [langevinKernel]
    fun_prop
  have hfc : Continuous (fun r : ℝ => σ/γ*Real.exp (-κ/γ*(R-r))) := by fun_prop
  have hnex m := continuous_adapted_ito_exists P hT F hF hle hnull W hW
    (fun z => langevinKernel κ γ σ m (R-z.2)) (fun r _ _ => by
      change Measurable[F (realTimeClamp r)] (fun _ : Ω => langevinKernel κ γ σ m (R-r))
      exact measurable_const) (fun _ _ _ _ => (hgc m).continuousOn)
  choose N hN hNI using hnex
  obtain ⟨Z,hZ,hZI⟩ := continuous_adapted_ito_exists P hT F hF hle hnull W hW
    (fun z => σ/γ*Real.exp (-κ/γ*(R-z.2))) (fun r _ _ => by
      change Measurable[F (realTimeClamp r)] (fun _ : Ω => σ/γ*Real.exp (-κ/γ*(R-r)))
      exact measurable_const) (fun _ _ _ _ => hfc.continuousOn)
  refine ⟨N,Z,hN,hZ,hNI,hZI,?_⟩
  have he m : (∫ w,(langevinInitial κ γ m R y v+N m (realTimeClamp R) w-
        (Real.exp (-κ/γ*R)*y+Z (realTimeClamp R) w))^2 ∂P)=
      (langevinInitial κ γ m R y v-Real.exp (-κ/γ*R)*y)^2+
        ∫ r in 0..R,(langevinKernel κ γ σ m r-σ/γ*Real.exp (-κ/γ*r))^2 := by
    have hI : ItoCovarianceFormula P F W
        (fun z => langevinKernel κ γ σ m (R-z.2)+(-1)*(σ/γ*Real.exp (-κ/γ*(R-z.2))))
        (fun t w => N m t w+(-1)*Z t w) := by
      convert hZI.add_smul P F hF hle W Z (N m) _ _ (hNI m) (-1) using 1 <;> ext z w <;> ring
    have hl := deterministic_brownian_integral_law P hT F hF hle hnull W A
      (fun t w => N m t w+(-1)*Z t w) hW hA ((hN m).add P F hF hle (hZ.smul P F (-1)))
      hclock (fun r => langevinKernel κ γ σ m (R-r)+(-1)*(σ/γ*Real.exp (-κ/γ*(R-r))))
      ((hgc m).add (continuous_const.mul hfc)) hI R hR.le hRT
    have hl' := ProbabilityTheory.gaussianReal_const_add hl (langevinInitial κ γ m R y v-Real.exp (-κ/γ*R)*y)
    have hh := gaussian_law_square_integral P _ _ _ hl'
    have hint := intervalIntegral.integral_comp_sub_left
      (fun r => (langevinKernel κ γ σ m r-σ/γ*Real.exp (-κ/γ*r))^2) (a:=0) (b:=R) R
    simp only [sub_self,sub_zero] at hint
    simp only [zero_add,add_zero,NNReal.coe_mk,NNReal.toReal,neg_one_mul,← sub_eq_add_neg] at hh
    rw [hint] at hh
    convert hh using 1
    congr 1
    funext w
    ring
  simp_rw [he]
  have hd := ((langevin_initial_limit κ γ R y v hγ hR).sub
    (tendsto_const_nhds (x:=Real.exp (-κ/γ*R)*y))).pow 2
  simpa only [sub_self,zero_pow (by norm_num : (2:ℕ)≠0),zero_add] using
    hd.add (langevin_kernel_L2_limit κ γ σ R hκ hγ hR.le)

end Asakura.Chapter4
