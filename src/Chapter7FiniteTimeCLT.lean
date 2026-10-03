import Chapter7MartingaleCLT

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

noncomputable def pathRestriction (a : ℝ≥0) (f : C(ℝ≥0,ℝ)) : C(Icc (0:ℝ≥0) a,ℝ) :=
  f.comp ⟨Subtype.val,continuous_subtype_val⟩

/-- Finite-horizon CLT for processes already defined on the half-line.
No convergence of their brackets after the observation horizon is needed. -/
theorem finite_time_clt_of_half_line
    {Ω Γ : Type*} [m : MeasurableSpace Ω] [q : MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (M C : ℕ → HalfClosedTime → Ω → ℝ)
    (hM : ∀ n,LocalMProcessWitness P F (M n))
    (hC : ∀ n,LocalCovarianceWitness P F (M n) (M n) (C n))
    (a : ℝ≥0)
    (hp : ∀ t : ℝ≥0,t ≤ a → TendstoInMeasure P (fun n => C n (realTimeClamp t)) atTop (fun _ => (t:ℝ)))
    (B : BrownianSystem Q 1) :
    ∃ B0 : BrownianSystem (P.prod Q) 1,
      TendstoInDistribution (fun n w => pathRestriction a (localContinuousPath (M n) ((hM n).path P F) w)) atTop
        (fun z => pathRestriction a (brownianContinuousPath B0 z)) (fun _ => P) (P.prod Q) := by
  let G := independentProductFiltration P Q F B.F
  let Z := fun (n : ℕ) t (z : Ω × Γ) => M n (min (realTimeClamp a) t) z.1+
    (B.W 0 t z.2-B.W 0 (min (realTimeClamp a) t) z.2)
  let A := fun (n : ℕ) t (z : Ω × Γ) => C n (min (realTimeClamp a) t) z.1+
    (B.C 0 0 t z.2-B.C 0 0 (min (realTimeClamp a) t) z.2)
  have hh n := independent_brownian_tail P Q F hF hle (M n) (C n) (hM n) (hC n) B a a.property
  have hG : Monotone G := (hh 0).1
  have hGl : ∀ t,G t ≤ productSigma m q := (hh 0).2.1
  have hGn : ∀ t N,MeasurableSet[productSigma m q] N → (P.prod Q) N=0 → MeasurableSet[G t] N := (hh 0).2.2.1
  have hZ n : LocalMProcessWitness (P.prod Q) G (Z n) := (hh n).2.2.2.1
  have hA n : LocalCovarianceWitness (P.prod Q) G (Z n) (Z n) (A n) := (hh n).2.2.2.2.1
  have hdiv n : ∀ᵐ z ∂P.prod Q,∀ r : ℝ,∃ t,t < ⊤ ∧ r < A n t z := ae_of_all _ (hh n).2.2.2.2.2.2.2
  have hAp (t : ℝ≥0) : TendstoInMeasure (P.prod Q) (fun n => A n (realTimeClamp t)) atTop (fun _ => (t:ℝ)) := by
    apply tendstoInMeasure_iff_dist.mpr
    intro ε hε
    have hp' := tendstoInMeasure_iff_dist.mp (hp (min a t) (min_le_left _ _)) ε hε
    have he : ∀ n,
        (P.prod Q) {z | ε ≤ dist (A n (realTimeClamp t) z) (t:ℝ)} =
          P {w | ε ≤ dist (C n (realTimeClamp (min a t)) w) ((min a t:ℝ≥0):ℝ)} := by
      intro n
      have hhA (z : Ω × Γ) : A n (realTimeClamp t) z = C n (realTimeClamp (min a t)) z.1+((t:ℝ)-(min a t:ℝ≥0)) := by
        have h := (hh n).2.2.2.2.2.1 t t.property z
        convert h using 1
        simp only [NNReal.coe_min]
        congr 1
        by_cases hat : a ≤ t
        · rw [min_eq_left (show (a:ℝ) ≤ t from hat),max_eq_right (sub_nonneg.mpr (show (a:ℝ) ≤ t from hat))]
        · rw [min_eq_right (show (t:ℝ) ≤ a from (le_of_not_ge hat)),max_eq_left (sub_nonpos.mpr (show (t:ℝ) ≤ a from le_of_not_ge hat)),sub_self]
      have hd z : dist (A n (realTimeClamp t) z) (t:ℝ) = dist (C n (realTimeClamp (min a t)) z.1) ((min a t:ℝ≥0):ℝ) := by
        rw [hhA,Real.dist_eq,Real.dist_eq]
        congr 1
        ring
      simp_rw [hd]
      have hm : Measurable (fun w => C n (realTimeClamp (min a t)) w) :=
        ((hC n).adapted P F (hM n) (hM n) _ (changed_time_finite _ (min a t).property)).mono (hle _) le_rfl
      exact (measurePreserving_fst (μ := P) (ν := Q)).measure_preimage
        (measurableSet_le measurable_const (hm.dist measurable_const)).nullMeasurableSet
    simpa only [he,NNReal.coe_min] using hp'
  obtain ⟨B0,hlim⟩ := dds_functional_limit (P.prod Q) G hG hGl hGn Z A hZ hA hdiv hAp
  have hr : Continuous (pathRestriction a) := ContinuousMap.continuous_precomp _
  have hres := hlim.continuous_comp hr
  let Y := fun n w => pathRestriction a (localContinuousPath (M n) ((hM n).path P F) w)
  have hYm n : Measurable (Y n) := by
    apply hr.measurable.comp
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact ((hM n).adapted P F _ (changed_time_finite t t.property)).mono (hle _) le_rfl
  have he n (z : Ω × Γ) : pathRestriction a (localContinuousPath (Z n) ((hZ n).path (P.prod Q) G) z) = Y n z.1 := by
    apply ContinuousMap.ext
    intro t
    exact (hh n).2.2.2.2.2.2.1 t.val ⟨t.val.property,t.property.2⟩ z
  have hres' := hres.congr (fun n => ae_of_all _ (he n)) .rfl
  refine ⟨B0,⟨fun n => (hYm n).aemeasurable,hres'.aemeasurable_limit,?_⟩⟩
  have hemap n : (P.prod Q).map (fun z : Ω × Γ => Y n z.1) = P.map (Y n) := by
    change (P.prod Q).map ((Y n) ∘ Prod.fst) = _
    rw [← Measure.map_map (hYm n) measurable_fst,(measurePreserving_fst (μ := P) (ν := Q)).map_eq]
  convert hres'.tendsto using 2 with n
  · apply Subtype.ext
    exact (hemap n).symm
  · rfl

end Asakura.Chapter7
