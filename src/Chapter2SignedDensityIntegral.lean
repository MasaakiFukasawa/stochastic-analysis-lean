import Chapter2SignedCumulativeContinuity
import Chapter2SignedMeasureIdentification
import FullAuditSignedIntegral
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable def signedWeighted {S : Type*} [MeasurableSpace S]
    (ν : SignedMeasure S) (g : S → ℝ) : SignedMeasure S :=
  ν.toJordanDecomposition.posPart.withDensityᵥ g - ν.toJordanDecomposition.negPart.withDensityᵥ g

theorem signed_weighted_apply {S : Type*} [MeasurableSpace S]
    (ν : SignedMeasure S) (g : S → ℝ) (hg : Integrable g ν.totalVariation)
    (B : Set S) (hB : MeasurableSet B) :
    signedWeighted ν g B = signedIntegralRaw ν (B.indicator g) := by
  have hp : ν.toJordanDecomposition.posPart ≤ ν.totalVariation := by intro s; exact le_add_right le_rfl
  have hn : ν.toJordanDecomposition.negPart ≤ ν.totalVariation := by intro s; exact le_add_left le_rfl
  simp only [signedWeighted,sub_apply,withDensityᵥ_apply (hg.mono_measure hp) hB,
    withDensityᵥ_apply (hg.mono_measure hn) hB,signedIntegralRaw,integral_indicator hB]

theorem signed_integral_const_mul {S : Type*} [MeasurableSpace S]
    (ν : SignedMeasure S) (f : S → ℝ) (c : ℝ) :
    signedIntegralRaw ν (fun x => c*f x) = c*signedIntegralRaw ν f := by
  simp only [signedIntegralRaw,integral_const_mul]
  ring

theorem signed_integral_indicator_const {S : Type*} [MeasurableSpace S]
    (ν : SignedMeasure S) (B : Set S) (hB : MeasurableSet B) (c : ℝ) :
    signedIntegralRaw ν (B.indicator (fun _ => c)) = c*ν B := by
  have he : B.indicator (fun _ => c) = fun x => c*(B.indicator (fun _ => (1:ℝ)) x) := by
    funext x
    by_cases hx : x ∈ B <;> simp [hx]
  rw [he,signed_integral_const_mul,signedIntegralRaw_indicator ν B hB]

/-- The change-of-density identity is first proved for genuine simple
functions, with integrability of their products included in the induction. -/
theorem signed_density_simple {S : Type*} [MeasurableSpace S]
    (ν κ : SignedMeasure S) (g : S → ℝ) (hg : Integrable g ν.totalVariation)
    (hκ : ∀ B, MeasurableSet B → κ B = signedIntegralRaw ν (B.indicator g))
    (f : SimpleFunc S ℝ) :
    Integrable (fun x => f x*g x) ν.totalVariation ∧
      signedIntegralRaw κ f = signedIntegralRaw ν (fun x => f x*g x) := by
  classical
  induction f using SimpleFunc.induction with
  | @const c B hB =>
    have he : (fun x => (SimpleFunc.piecewise B hB (SimpleFunc.const S c) (SimpleFunc.const S 0)) x*g x) =
        fun x => c*(B.indicator g x) := by
      funext x
      by_cases hx : x ∈ B <;> simp [hx]
    have hf : ((SimpleFunc.piecewise B hB (SimpleFunc.const S c) (SimpleFunc.const S 0)) : S → ℝ) =
        B.indicator (fun _ => c) := by
      funext x
      by_cases hx : x ∈ B <;> simp [hx]
    refine ⟨?_,?_⟩
    · rw [he]
      exact (hg.indicator hB).const_mul c
    · rw [he,hf,signed_integral_indicator_const κ B hB,signed_integral_const_mul,hκ B hB]
  | @add f k hd hf hk =>
    have he : (fun x => (f+k) x*g x) = fun x => f x*g x+k x*g x := by
      funext x
      simp only [SimpleFunc.coe_add,Pi.add_apply,add_mul]
    refine ⟨by rw [he]; exact hf.1.add hk.1,?_⟩
    change signedIntegralRaw κ (fun x => f x+k x) = _
    rw [show (fun x => f x+k x) = (fun x => 1*f x+k x) by funext x; ring,
      signed_integral_add_smul κ f k f.integrable_of_isFiniteMeasure k.integrable_of_isFiniteMeasure 1,
      one_mul,hf.2,hk.2,he]
    symm
    simpa only [one_mul] using signed_integral_add_smul ν (fun x => f x*g x) (fun x => k x*g x) hf.1 hk.1 1

/-- General associativity for signed integration, by the manuscript's
simple approximation and dominated convergence, rather than assuming an
integration rule for an unspecified signed measure. -/
theorem signed_density_integral {S : Type*} [MeasurableSpace S]
    (ν κ : SignedMeasure S) (g h : S → ℝ) (hg : Measurable g) (hh : Measurable h)
    (hgi : Integrable g ν.totalVariation) (hhi : Integrable h κ.totalVariation)
    (hhg : Integrable (fun x => h x*g x) ν.totalVariation)
    (hκ : ∀ B, MeasurableSet B → κ B = signedIntegralRaw ν (B.indicator g)) :
    signedIntegralRaw κ h = signedIntegralRaw ν (fun x => h x*g x) := by
  let f : ℕ → SimpleFunc S ℝ := SimpleFunc.approxOn h hh univ 0 (mem_univ 0)
  have hlim x : Tendsto (fun n => f n x) atTop (𝓝 (h x)) :=
    SimpleFunc.tendsto_approxOn hh (mem_univ 0) (by simp)
  have hb x n : ‖f n x‖ ≤ ‖h x‖+‖h x‖ := SimpleFunc.norm_approxOn_zero_le hh (mem_univ 0) x n
  have hdom (μ : Measure S) (hμ : μ ≤ κ.totalVariation) :
      Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, h x ∂μ)) := by
    exact Asakura.manuscript_dominated_convergence μ (fun n x => f n x) h (fun x => ‖h x‖+‖h x‖)
      (fun n => (f n).measurable) hh (hh.norm.add hh.norm)
      ((hhi.mono_measure hμ).norm.add (hhi.mono_measure hμ).norm)
      (fun n => ae_of_all _ (fun x => hb x n)) (ae_of_all _ hlim)
  have hprod (μ : Measure S) (hμ : μ ≤ ν.totalVariation) :
      Tendsto (fun n => ∫ x, f n x*g x ∂μ) atTop (𝓝 (∫ x, h x*g x ∂μ)) := by
    apply Asakura.manuscript_dominated_convergence μ (fun n x => f n x*g x)
      (fun x => h x*g x) (fun x => ‖h x*g x‖+‖h x*g x‖)
      (fun n => (f n).measurable.mul hg) (hh.mul hg) ((hh.mul hg).norm.add (hh.mul hg).norm)
      ((hhg.mono_measure hμ).norm.add (hhg.mono_measure hμ).norm)
    · intro n
      exact ae_of_all _ (fun x => by
        rw [norm_mul,norm_mul]
        nlinarith [mul_le_mul_of_nonneg_right (hb x n) (norm_nonneg (g x))])
    · exact ae_of_all _ (fun x => (hlim x).mul_const (g x))
  have hp (v : SignedMeasure S) : v.toJordanDecomposition.posPart ≤ v.totalVariation := by intro s; exact le_add_right le_rfl
  have hn (v : SignedMeasure S) : v.toJordanDecomposition.negPart ≤ v.totalVariation := by intro s; exact le_add_left le_rfl
  have hl := (hdom _ (hp κ)).sub (hdom _ (hn κ))
  have hr := (hprod _ (hp ν)).sub (hprod _ (hn ν))
  change Tendsto (fun n => signedIntegralRaw κ (f n)) atTop (𝓝 (signedIntegralRaw κ h)) at hl
  change Tendsto (fun n => signedIntegralRaw ν (fun x => f n x*g x)) atTop
    (𝓝 (signedIntegralRaw ν (fun x => h x*g x))) at hr
  have he n := (signed_density_simple ν κ g hgi hκ (f n)).2
  simp only [he] at hl
  exact tendsto_nhds_unique hl hr

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.signed_density_integral
