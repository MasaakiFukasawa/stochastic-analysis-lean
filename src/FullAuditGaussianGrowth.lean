import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.LpSpace.Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- An equivalent convenient form of polynomial growth. -/
def PolyGrowth {E : Type*} [Norm E] (f : E → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ x, |f x| ≤ C*(1+‖x‖)^k

theorem PolyGrowth.mul {E : Type*} [SeminormedAddCommGroup E] {f g : E → ℝ}
    (hf : PolyGrowth f) (hg : PolyGrowth g) : PolyGrowth (fun x => f x*g x) := by
  obtain ⟨C,hC,k,hf⟩ := hf
  obtain ⟨D,hD,l,hg⟩ := hg
  refine ⟨C*D,mul_nonneg hC hD,k+l,fun x => ?_⟩
  rw [abs_mul]
  calc
    _ ≤ (C*(1+‖x‖)^k)*(D*(1+‖x‖)^l) := mul_le_mul (hf x) (hg x) (abs_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem PolyGrowth.add {E : Type*} [SeminormedAddCommGroup E] {f g : E → ℝ}
    (hf : PolyGrowth f) (hg : PolyGrowth g) : PolyGrowth (fun x => f x+g x) := by
  obtain ⟨C,hC,k,hf⟩ := hf
  obtain ⟨D,hD,l,hg⟩ := hg
  refine ⟨C+D,add_nonneg hC hD,max k l,fun x => ?_⟩
  have hx : 1 ≤ 1+‖x‖ := by linarith [norm_nonneg x]
  calc
    |f x+g x| ≤ |f x|+|g x| := abs_add_le _ _
    _ ≤ C*(1+‖x‖)^k+D*(1+‖x‖)^l := add_le_add (hf x) (hg x)
    _ ≤ C*(1+‖x‖)^(max k l)+D*(1+‖x‖)^(max k l) :=
      add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (le_max_left _ _)) hC)
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (le_max_right _ _)) hD)
    _ = _ := by ring

theorem polynomial_growth_coordinate {ι : Type*} [Fintype ι] (i : ι) :
    PolyGrowth (fun z : ι → ℝ => z i) := by
  refine ⟨1,by norm_num,1,fun z => ?_⟩
  have hz : |z i| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
  simpa only [one_mul,pow_one] using (show |z i| ≤ 1+‖z‖ by linarith)

theorem finite_gaussian_all_moments {ι : Type*} [Fintype ι] (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun z : ι → ℝ => z) p (Measure.pi fun _ => gaussianReal 0 1) := by
  apply MemLp.of_eval
  intro i
  simpa only [Function.comp_def,id_eq] using
    (memLp_id_gaussianReal' p hp).comp_measurePreserving
      (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i)

/-- Polynomial growth provides every integral required for the Gaussian IBP;
 no integrability of the target identity is postulated. -/
theorem polynomial_growth_gaussian_integrable {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → ℝ} (hm : Measurable f) (hf : PolyGrowth f) :
    Integrable f (Measure.pi fun _ => gaussianReal 0 1) := by
  obtain ⟨C,hC,k,hf⟩ := hf
  let μ : Measure (ι → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  have hn : MemLp (fun z : ι → ℝ => ‖z‖) (k:ℝ≥0∞) μ :=
    (finite_gaussian_all_moments (k:ℝ≥0∞) (by simp)).norm
  have hbase : MemLp (fun z : ι → ℝ => 1+‖z‖) (k:ℝ≥0∞) μ :=
    (memLp_const (μ := μ) (p := (k:ℝ≥0∞)) (1:ℝ)).add hn
  have hpow : Integrable (fun z : ι → ℝ => (1+‖z‖)^k) (Measure.pi fun _ => gaussianReal 0 1) := by
    have hp : Integrable (fun z : ι → ℝ => ‖1+‖z‖‖^k) μ := hbase.integrable_norm_pow'
    have he (z : ι → ℝ) : ‖1+‖z‖‖ = 1+‖z‖ := by rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    simpa only [he] using hp
  apply (hpow.const_mul C).mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hf z

end Asakura.FullAudit
