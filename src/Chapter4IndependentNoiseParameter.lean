import Chapter4BoundedConditionalLimit
import Chapter4MarkovSimpleInitial
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

lemma bounded_parameter_integral {E D : Type*} [MeasurableSpace E] [MeasurableSpace D]
    (ν : Measure D) [IsProbabilityMeasure ν] (g : E × D → ℝ) (hg : Measurable g)
    (B : ℝ) (hb : ∀ x z,‖g (x,z)‖≤B) :
    Measurable (fun x => ∫ z,g (x,z) ∂ν) ∧ ∀ x,‖∫ z,g (x,z) ∂ν‖≤B := by
  refine ⟨hg.stronglyMeasurable.integral_prod_right'.measurable,?_⟩
  intro x
  have hi : Integrable (fun z => g (x,z)) ν := Integrable.of_bound
    (hg.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable B (ae_of_all _ (hb x))
  calc
    _ ≤ ∫ z,‖g (x,z)‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : D,B ∂ν := integral_mono hi.norm (integrable_const _) (hb x)
    _ = B := by simp

/-- An independent noise input may be combined with any measurable initial
parameter. Finite-valued parameters are treated first, and the limit uses
bounded convergence. -/
theorem independent_noise_parameter_condExp
    {Ω D : Type*} {m : MeasurableSpace Ω} {dim : ℕ}
    [MeasurableSpace D]
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω) (hG : G≤m)
    (Z : Ω → D) (hZ : Measurable[m] Z) (ν : Measure D) [IsProbabilityMeasure ν]
    (hlaw : HasLaw Z ν P) (hind : Indep (MeasurableSpace.comap Z inferInstance) G P)
    (η : Ω → Fin dim → ℝ) (hη : Measurable[G] η)
    (g : (Fin dim → ℝ) × D → ℝ) (hg : Measurable g)
    (hc : ∀ z,Continuous (fun x => g (x,z)))
    (B : ℝ) (hb : ∀ x z,‖g (x,z)‖≤B) :
    P[(fun w => g (η w,Z w)) | G]=ᵐ[P] fun w => ∫ z,g (η w,z) ∂ν := by
  classical
  letI : MeasurableSpace Ω := m
  let a : ℕ → @SimpleFunc Ω G (Fin dim → ℝ) := by
    letI : MeasurableSpace Ω := G
    exact SimpleFunc.approxOn η hη univ 0 (mem_univ 0)
  have ham n : Measurable[G] (fun w => a n w) := by
    letI : MeasurableSpace Ω := G
    exact (a n).measurable
  have hat w : Tendsto (fun n => a n w) atTop (𝓝 (η w)) := by
    letI : MeasurableSpace Ω := G
    exact SimpleFunc.tendsto_approxOn hη (mem_univ (0:Fin dim → ℝ)) (x:=w) (by simp)
  let p := fun x => ∫ z,g (x,z) ∂ν
  obtain ⟨hpm,hpb⟩ := bounded_parameter_integral ν g hg B hb
  have he n : P[(fun w => g (a n w,Z w)) | G]=ᵐ[P] fun w => p (a n w) := by
    let R : Finset (Fin dim → ℝ) := by
      letI : MeasurableSpace Ω := G
      exact (a n).range
    have hmR w : a n w∈R := by
      letI : MeasurableSpace Ω := G
      exact (a n).mem_range_self w
    let ηn : Ω → R := fun w => ⟨a n w,hmR w⟩
    have hηn : Measurable[G] ηn := (ham n).subtype_mk
    exact independent_noise_simple_initial_condExp P G hG Z hZ ν hlaw hind ηn hηn
      (fun x z => g (x.val,z)) (fun x => hg.comp (measurable_const.prodMk measurable_id)) B
      (fun x z => hb x.val z)
  have hfm n : Measurable[m] (fun w => g (a n w,Z w)) := hg.comp (((ham n).mono hG le_rfl).prodMk hZ)
  have hgm : Measurable[m] (fun w => g (η w,Z w)) := hg.comp ((hη.mono hG le_rfl).prodMk hZ)
  have hft : Tendsto (fun n => eLpNorm (fun w => g (a n w,Z w)-g (η w,Z w)) 2 P) atTop (𝓝 0) :=
    bounded_pointwise_L2_convergence P _ _ hfm hgm B (fun n w => hb _ _) (fun w => hb _ _)
      (ae_of_all _ fun w => ((hc (Z w)).continuousAt.tendsto.comp (hat w)))
  apply conditional_L2_bounded_limit P G hG _ _ _ _
    (fun n => MemLp.of_bound (hfm n).aestronglyMeasurable B (ae_of_all _ fun w => hb _ _))
    (MemLp.of_bound hgm.aestronglyMeasurable B (ae_of_all _ fun w => hb _ _))
    (fun n => hpm.comp ((ham n).mono hG le_rfl)) (hpm.comp (hη.mono hG le_rfl))
    B (fun n w => hpb _) (fun w => hpb _) hft ?_ he
  apply ae_of_all
  intro w
  exact tendsto_integral_of_dominated_convergence (fun _ => B)
    (fun n => (hg.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (integrable_const B) (fun n => ae_of_all _ (hb (a n w)))
    (ae_of_all _ fun z => ((hc z).continuousAt.tendsto.comp (hat w)))

end Asakura.Chapter4
