import Chapter9CoordinateScore
import FullAuditDenoising
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

open MeasureTheory
open scoped RealInnerProductSpace ENNReal NNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem gaussian_denoising_score {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (a : ℝ) (v : ℝ≥0) (hv : v≠0) :
    let Q := (μ.prod volume).withDensity (fun z => ENNReal.ofReal (gaussianKernel a v z.1 z.2))
    Q[componentScore a v|MeasurableSpace.comap Prod.snd inferInstance] =ᵐ[Q]
      (fun z => mixtureScore μ a v z.2) := by
  let Q := (μ.prod volume).withDensity (fun z => ENNReal.ofReal (gaussianKernel a v z.1 z.2))
  haveI : IsProbabilityMeasure Q := gaussian_joint_probability μ a v hv
  have hM := gaussian_joint_score_memLp μ a v hv
  have hSc : Continuous (componentScore (d := d) a v) := by unfold componentScore; fun_prop
  have hb := gaussian_joint_regression μ a v hv (componentScore a v)
    hSc.stronglyMeasurable (hM.integrable (by norm_num))
  apply hb.trans
  apply ae_of_all
  intro z
  exact normalized_density_integral μ (fun x => gaussianKernel a v x z.2)
    (by unfold gaussianKernel; fun_prop) (fun x => (gaussian_kernel_positive a v x z.2).le)
    _ (gaussian_mixture_positive μ a v hv z.2).2 (fun x => componentScore a v (x,z.2))

theorem l2_function_distance {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) (f g : Ω → E) (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    ‖hf.toLp f-hg.toLp g‖^2=∫ w,‖f w-g w‖^2 ∂P := by
  rw [Asakura.FullAudit.l2_squared_norm_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g),hf.coeFn_toLp,hg.coeFn_toLp]
    with w hs hf hg
  rw [hs,Pi.sub_apply,hf,hg]

/-- C2 written as an identity of actual mean squared losses, with an
identified conditional mean g rather than an abstract projection. -/
theorem conditional_mean_loss_identity {Ω E : Type*} {G m : MeasurableSpace Ω}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (hle : G ≤ m)
    (Z g s : Ω → E) (hZ : MemLp Z 2 P) (hs : MemLp s 2 P)
    (hsm : AEStronglyMeasurable[G] s P) (hce : P[Z|G]=ᵐ[P] g) :
    (∫ w,‖s w-Z w‖^2 ∂P)=
      (∫ w,‖s w-g w‖^2 ∂P)+(∫ w,‖Z w-g w‖^2 ∂P) := by
  have hg : MemLp g 2 P := MemLp.ae_eq hce (hZ.condExp (m := G) (by norm_num))
  have hproj : (condExpL2 E ℝ hle (hZ.toLp Z) : Lp E 2 P)=hg.toLp g := by
    apply Lp.ext
    exact (hZ.condExpL2_ae_eq_condExp (𝕜 := ℝ) hle).trans (hce.trans hg.coeFn_toLp.symm)
  have hsl : AEStronglyMeasurable[G] (hs.toLp s) P := hsm.congr hs.coeFn_toLp.symm
  have hh := Asakura.FullAudit.denoising_loss_identity P hle (hZ.toLp Z) (hs.toLp s) hsl
  rw [hproj,l2_function_distance P s Z hs hZ,l2_function_distance P s g hs hg,
    l2_function_distance P Z g hZ hg] at hh
  exact hh

/-- Full loss identity for the Gaussian joint law and its actual density
score. The competitor is any L² function of the observed coordinate. -/
theorem gaussian_denoising_loss {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (a : ℝ) (v : ℝ≥0) (hv : v≠0)
    (s : (Fin d → ℝ) × (Fin d → ℝ) → EuclideanSpace ℝ (Fin d))
    (hs : MemLp s 2 ((μ.prod volume).withDensity
      (fun z => ENNReal.ofReal (gaussianKernel a v z.1 z.2))))
    (hsm : AEStronglyMeasurable[MeasurableSpace.comap Prod.snd inferInstance] s
      ((μ.prod volume).withDensity (fun z => ENNReal.ofReal (gaussianKernel a v z.1 z.2)))) :
    let Q := (μ.prod volume).withDensity (fun z => ENNReal.ofReal (gaussianKernel a v z.1 z.2))
    MemLp (fun z => mixtureScore μ a v z.2) 2 Q ∧
    (∫ z,‖s z-componentScore a v z‖^2 ∂Q)=
      (∫ z,‖s z-mixtureScore μ a v z.2‖^2 ∂Q)+
      (∫ z,‖componentScore a v z-mixtureScore μ a v z.2‖^2 ∂Q) ∧
    (∫ z,‖mixtureScore μ a v z.2-componentScore a v z‖^2 ∂Q)≤
      (∫ z,‖s z-componentScore a v z‖^2 ∂Q) := by
  let Q := (μ.prod volume).withDensity (fun z => ENNReal.ofReal (gaussianKernel a v z.1 z.2))
  haveI : IsProbabilityMeasure Q := gaussian_joint_probability μ a v hv
  have hZ := gaussian_joint_score_memLp μ a v hv
  have hce := gaussian_denoising_score μ a v hv
  have he := conditional_mean_loss_identity Q measurable_snd.comap_le
    (componentScore a v) (fun z => mixtureScore μ a v z.2) s hZ hs hsm hce
  refine ⟨MemLp.ae_eq hce (hZ.condExp (by norm_num)),he,?_⟩
  rw [he]
  have hn : 0≤∫ z,‖s z-mixtureScore μ a v z.2‖^2 ∂Q := integral_nonneg (fun _ => sq_nonneg _)
  have hr : (∫ z,‖mixtureScore μ a v z.2-componentScore a v z‖^2 ∂Q)=
      ∫ z,‖componentScore a v z-mixtureScore μ a v z.2‖^2 ∂Q := by
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by dsimp only; rw [norm_sub_rev])
  rw [hr]
  exact le_add_of_nonneg_left hn
end Asakura.Chapter9
