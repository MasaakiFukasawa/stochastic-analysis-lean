import Chapter4BrownianCharacterization
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

open MeasureTheory Set
namespace Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

lemma trig_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : Measurable X) :
    Integrable (fun w => Real.cos (X w)) P ∧ Integrable (fun w => Real.sin (X w)) P :=
  ⟨Integrable.of_bound hX.cos.aestronglyMeasurable 1
    (ae_of_all _ fun w => Real.abs_cos_le_one _),
   Integrable.of_bound hX.sin.aestronglyMeasurable 1
    (ae_of_all _ fun w => Real.abs_sin_le_one _)⟩

/-- The angle-subtraction identities and C3 remove the past from a
conditional sine/cosine pair. -/
theorem conditional_trig_increment {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω) (hG : G≤m)
    (X Y : Ω → ℝ) (hX : Measurable[G] X) (hY : Measurable[m] Y) (q : ℝ)
    (hcos : P[(fun w => Real.cos (Y w)) | G] =ᵐ[P] fun w => q*Real.cos (X w))
    (hsin : P[(fun w => Real.sin (Y w)) | G] =ᵐ[P] fun w => q*Real.sin (X w)) :
    P[(fun w => Real.cos (Y w-X w)) | G] =ᵐ[P] (fun _ => q) ∧
    P[(fun w => Real.sin (Y w-X w)) | G] =ᵐ[P] (fun _ => (0:ℝ)) := by
  letI : MeasurableSpace Ω := m
  let Cx := fun w => Real.cos (X w)
  let Sx := fun w => Real.sin (X w)
  let Cy := fun w => Real.cos (Y w)
  let Sy := fun w => Real.sin (Y w)
  have hc : AEStronglyMeasurable Cx P := (hX.cos.mono hG le_rfl).aestronglyMeasurable
  have hs : AEStronglyMeasurable Sx P := (hX.sin.mono hG le_rfl).aestronglyMeasurable
  have hcb : ∀ᵐ w ∂P,‖Cx w‖≤1 := ae_of_all _ fun _ => Real.abs_cos_le_one _
  have hsb : ∀ᵐ w ∂P,‖Sx w‖≤1 := ae_of_all _ fun _ => Real.abs_sin_le_one _
  have hci : Integrable Cy P := (trig_integrable P hY).1
  have hsi : Integrable Sy P := (trig_integrable P hY).2
  have hcc := condExp_stronglyMeasurable_mul_of_bound hG hX.cos.stronglyMeasurable hci 1 hcb
  have hss := condExp_stronglyMeasurable_mul_of_bound hG hX.sin.stronglyMeasurable hsi 1 hsb
  have hcs := condExp_stronglyMeasurable_mul_of_bound hG hX.cos.stronglyMeasurable hsi 1 hcb
  have hsc := condExp_stronglyMeasurable_mul_of_bound hG hX.sin.stronglyMeasurable hci 1 hsb
  have hadd := condExp_add (hci.bdd_mul hc hcb) (hsi.bdd_mul hs hsb) G
  have hsub := condExp_sub (hsi.bdd_mul hc hcb) (hci.bdd_mul hs hsb) G
  have hec : (fun w => Real.cos (Y w-X w))=(Cx*Cy+Sx*Sy) := by
    funext w; simp only [Real.cos_sub,Pi.add_apply,Pi.mul_apply,Cx,Cy,Sx,Sy]; ring
  have hes : (fun w => Real.sin (Y w-X w))=(Cx*Sy-Sx*Cy) := by
    funext w; simp only [Real.sin_sub,Pi.sub_apply,Pi.mul_apply,Cx,Cy,Sx,Sy]; ring
  rw [hec,hes]
  constructor
  · filter_upwards [hadd,hcc,hss,hcos,hsin] with w ha hcc hss hc hs
    simp only [Pi.add_def,Pi.mul_def,Cx,Sx,Cy,Sy] at ha hcc hss ⊢
    rw [ha,hcc,hss,hc,hs]
    have hi := Real.sin_sq_add_cos_sq (X w)
    nlinarith [congrArg (fun z => q*z) hi]
  · filter_upwards [hsub,hcs,hsc,hcos,hsin] with w ha hcs hsc hc hs
    simp only [Pi.sub_def,Pi.mul_def,Cx,Sx,Cy,Sy] at ha hcs hsc ⊢
    rw [ha,hcs,hsc,hc,hs]
    ring

/-- Real and imaginary conditional expectations determine the full
complex characteristic function. -/
theorem conditional_characteristic_from_trig {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω)
    (Z : Ω → ℝ) (hZ : Measurable[m] Z) (q : ℝ)
    (hc : P[(fun w => Real.cos (Z w)) | G] =ᵐ[P] fun _ => q)
    (hs : P[(fun w => Real.sin (Z w)) | G] =ᵐ[P] fun _ => (0:ℝ)) :
    P[(fun w => Complex.exp ((Z w:ℂ)*Complex.I)) | G] =ᵐ[P] fun _ => (q:ℂ) := by
  letI : MeasurableSpace Ω := m
  let f := fun w => Complex.exp ((Z w:ℂ)*Complex.I)
  have hi : Integrable f P := Integrable.of_bound (show Measurable f from by dsimp [f]; fun_prop).aestronglyMeasurable 1
    (ae_of_all _ fun w => by simp [f,Complex.norm_exp])
  have hr := Complex.reCLM.comp_condExp_comm (m := G) hi
  have him := Complex.imCLM.comp_condExp_comm (m := G) hi
  have her : Complex.reCLM ∘ f=fun w => Real.cos (Z w) := by
    funext w; simp [f,Function.comp_def,Complex.exp_re]
  have hei : Complex.imCLM ∘ f=fun w => Real.sin (Z w) := by
    funext w; simp [f,Function.comp_def,Complex.exp_im]
  rw [her] at hr
  rw [hei] at him
  filter_upwards [hr,him,hc,hs] with w hr hi hc hs
  apply Complex.ext
  · exact hr.trans hc
  · exact hi.trans hs

end Asakura.Chapter4
