import Chapter9CovarianceOperator
import Mathlib.MeasureTheory.Function.Holder

open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter9
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Centering a square-integrable variable subtracts the outer product of
its mean, for every continuous bilinear form with complete codomain. -/
theorem centered_bilinear_integral {Ω E V : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → E) (hX : MemLp X 2 P)
    (B : E →L[ℝ] E →L[ℝ] V) :
    (∫ w,B (X w-∫ u,X u ∂P) (X w-∫ u,X u ∂P) ∂P)=
      (∫ w,B (X w) (X w) ∂P)-B (∫ u,X u ∂P) (∫ u,X u ∂P) := by
  let m := ∫ u,X u ∂P
  have hi := hX.integrable (by norm_num)
  have hXX : Integrable (fun w => B (X w) (X w)) P :=
    memLp_one_iff_integrable.mp (B.memLp_of_bilin 1 hX hX)
  have hXm : Integrable (fun w => B (X w) m) P := (B.flip m).integrable_comp hi
  have hmX : Integrable (fun w => B m (X w)) P := (B m).integrable_comp hi
  have h1 : (∫ w,B (X w) m ∂P)=B m m := (B.flip m).integral_comp_comm hi
  have h2 : (∫ w,B m (X w) ∂P)=B m m := (B m).integral_comp_comm hi
  change (∫ w,B (X w-m) (X w-m) ∂P)=(∫ w,B (X w) (X w) ∂P)-B m m
  have he w : B (X w-m) (X w-m)=B (X w) (X w)-B (X w) m-B m (X w)+B m m := by
    simp only [map_sub,ContinuousLinearMap.sub_apply]
    abel
  simp_rw [he]
  have ha := integral_add ((hXX.sub hXm).sub hmX) (integrable_const (B m m))
  have hb := integral_sub (hXX.sub hXm) hmX
  have hc := integral_sub hXX hXm
  dsimp only [Pi.sub_apply] at ha hb hc
  rw [ha,hb,hc,h1,h2]
  simp only [integral_const,probReal_univ,one_smul]
  abel

theorem bilinear_square_integrable {Ω E V : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → E) (hX : MemLp X 2 P)
    (B : E →L[ℝ] E →L[ℝ] V) :
    Integrable (fun w => B (X w) (X w)) P :=
  memLp_one_iff_integrable.mp (B.memLp_of_bilin 1 hX hX)

noncomputable def dyad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    E →L[ℝ] E →L[ℝ] (E →L[ℝ] E) :=
  (ContinuousLinearMap.smulRightL ℝ E E).comp (innerSL ℝ)

@[simp] theorem dyad_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) : dyad x y=(innerSL ℝ x).smulRight y := rfl

theorem covariance_operator_centering {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : Measure E) [IsProbabilityMeasure P]
    (h2 : MemLp (fun x : E => x) 2 P) :
    covarianceOperator P=(∫ x,dyad x x ∂P)-dyad (∫ x,x ∂P) (∫ x,x ∂P) :=
  centered_bilinear_integral P (fun x => x) h2 dyad

/-- The covariance of y-aX is a² times the covariance of X. This is the
operator identity underlying the posterior covariance term in the score Hessian. -/
theorem affine_dyad_covariance {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : Measure E) [IsProbabilityMeasure P]
    (h2 : MemLp (fun x : E => x) 2 P) (y : E) (a : ℝ) :
    (∫ x,dyad (y-a • x) (y-a • x) ∂P)-
      dyad (y-a • (∫ x,x ∂P)) (y-a • (∫ x,x ∂P))=a^2 • covarianceOperator P := by
  have hZ : MemLp (fun x : E => y-a • x) 2 P := (memLp_const y).sub (h2.const_smul a)
  have hmean : (∫ x,y-a • x ∂P)=y-a • (∫ x,x ∂P) := by
    have hia : Integrable (fun x : E => a • x) P := (h2.integrable (by norm_num)).smul a
    rw [integral_sub (integrable_const y) hia,integral_smul]
    simp
  have hh := centered_bilinear_integral P (fun x : E => y-a • x) hZ dyad
  rw [hmean] at hh
  rw [←hh]
  have he x : y-a • x-(y-a • (∫ x,x ∂P))=(-a) • (x-∫ x,x ∂P) := by
    simp only [smul_sub,neg_smul]
    abel
  simp_rw [he]
  have he2 (x : E) : dyad ((-a) • x) ((-a) • x)=a^2 • dyad x x := by
    simp only [map_smul,smul_apply,smul_smul]
    congr 1
    ring
  simp_rw [he2]
  rw [integral_smul]
  rfl
end Asakura.Chapter9
