import Chapter7BrownianTail
import Chapter8DDSVaryingFiltration
import Chapter7PrefixDistribution

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace Asakura.Chapter8
open Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

/-- The half-line martingale CLT from the manuscript's pointwise bracket
convergence alone. An independent Brownian driver is used only to construct
the divergent-bracket extensions on the product probability space. -/
theorem martingale_clt_varying_filtration_with_driver
    {Ω Γ : Type*} [m : MeasurableSpace Ω] [q : MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : ℕ → HalfClosedTime → MeasurableSpace Ω) (hF : ∀ n, Monotone (F n)) (hle : ∀ n t,F n t ≤ m)
    (M C : ℕ → HalfClosedTime → Ω → ℝ)
    (hM : ∀ n,LocalMProcessWitness P (F n) (M n))
    (hC : ∀ n,LocalCovarianceWitness P (F n) (M n) (M n) (C n))
    (hp : ∀ t : ℝ≥0,TendstoInMeasure P (fun n => C n (realTimeClamp t)) atTop (fun _ => (t:ℝ)))
    (B : BrownianSystem Q 1) :
    ∃ B0 : BrownianSystem (P.prod Q) 1,
      TendstoInDistribution (fun n => localContinuousPath (M n) ((hM n).path P (F n))) atTop
        (brownianContinuousPath B0) (fun _ => P) (P.prod Q) := by
  let G := fun n => independentProductFiltration P Q (F n) B.F
  let Z := fun (n : ℕ) t (z : Ω × Γ) => M n (min (realTimeClamp n) t) z.1+
    (B.W 0 t z.2-B.W 0 (min (realTimeClamp n) t) z.2)
  let A := fun (n : ℕ) t (z : Ω × Γ) => C n (min (realTimeClamp n) t) z.1+
    (B.C 0 0 t z.2-B.C 0 0 (min (realTimeClamp n) t) z.2)
  have hh n := independent_brownian_tail P Q (F n) (hF n) (hle n) (M n) (C n) (hM n) (hC n) B n (Nat.cast_nonneg n)
  have hG n : Monotone (G n) := (hh n).1
  have hGl n : ∀ t,G n t ≤ productSigma m q := (hh n).2.1
  have hGn n : ∀ t N,MeasurableSet[productSigma m q] N → (P.prod Q) N=0 → MeasurableSet[G n t] N := (hh n).2.2.1
  have hZ n : LocalMProcessWitness (P.prod Q) (G n) (Z n) := (hh n).2.2.2.1
  have hA n : LocalCovarianceWitness (P.prod Q) (G n) (Z n) (Z n) (A n) := (hh n).2.2.2.2.1
  have hdiv n : ∀ᵐ z ∂P.prod Q,∀ r : ℝ,∃ t,t < ⊤ ∧ r < A n t z := ae_of_all _ (hh n).2.2.2.2.2.2.2
  have hAm n (t : ℝ≥0) : Measurable (fun w => C n (realTimeClamp t) w) :=
    ((hC n).adapted P (F n) (hM n) (hM n) _ (changed_time_finite t t.property)).mono (hle n _) le_rfl
  have hAp (t : ℝ≥0) : TendstoInMeasure (P.prod Q) (fun n => A n (realTimeClamp t)) atTop (fun _ => (t:ℝ)) := by
    apply tendstoInMeasure_iff_dist.mpr
    intro ε hε
    have hp' := tendstoInMeasure_iff_dist.mp (hp t) ε hε
    have he : ∀ᶠ n : ℕ in atTop,
        (P.prod Q) {z | ε ≤ dist (A n (realTimeClamp t) z) (t:ℝ)} =
          P {w | ε ≤ dist (C n (realTimeClamp t) w) (t:ℝ)} := by
      obtain ⟨N,hN⟩ := exists_nat_ge (t:ℝ)
      apply eventually_atTop.2 ⟨N,?_⟩
      intro n hn
      have htn : (t:ℝ) ≤ n := hN.trans (by exact_mod_cast hn)
      have heq : A n (realTimeClamp t) = fun z : Ω × Γ => C n (realTimeClamp t) z.1 := by
        funext z
        have hhA := (hh n).2.2.2.2.2.1 t t.property z
        simpa only [min_eq_right htn,max_eq_left (sub_nonpos.mpr htn),add_zero] using hhA
      rw [heq]
      exact (measurePreserving_fst (μ := P) (ν := Q)).measure_preimage
        (measurableSet_le measurable_const ((hAm n t).dist measurable_const)).nullMeasurableSet
    apply hp'.congr'
    filter_upwards [he] with n hn
    exact hn.symm
  obtain ⟨B0,hlim⟩ := dds_functional_limit_varying_filtration (P.prod Q) G hG hGl hGn Z A hZ hA hdiv hAp
  let X := fun n => localContinuousPath (Z n) ((hZ n).path (P.prod Q) (G n))
  let Y := fun n (z : Ω × Γ) => localContinuousPath (M n) ((hM n).path P (F n)) z.1
  have hMm n : Measurable (localContinuousPath (M n) ((hM n).path P (F n))) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact ((hM n).adapted P (F n) _ (changed_time_finite t t.property)).mono (hle n _) le_rfl
  have hXm n : Measurable (X n) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact ((hZ n).adapted (P.prod Q) (G n) _ (changed_time_finite t t.property)).mono (hGl n _) le_rfl
  have hYm n : Measurable (Y n) := (hMm n).comp measurable_fst
  have he (n : ℕ) z (t : ℝ≥0) (ht : t ≤ (n:ℝ≥0)) : X n z t = Y n z t := by
    exact (hh n).2.2.2.2.2.2.1 t ⟨t.property,by exact_mod_cast ht⟩ z
  have hYlim := prefix_distribution (P.prod Q) (P.prod Q) X Y (brownianContinuousPath B0) hXm hYm hlim he
  refine ⟨B0,⟨fun n => (hMm n).aemeasurable,hYlim.aemeasurable_limit,?_⟩⟩
  have hemap n : (P.prod Q).map (Y n) = P.map (localContinuousPath (M n) ((hM n).path P (F n))) := by
    change (P.prod Q).map ((localContinuousPath (M n) ((hM n).path P (F n))) ∘ Prod.fst) = _
    rw [← Measure.map_map (hMm n) measurable_fst,(measurePreserving_fst (μ := P) (ν := Q)).map_eq]
  convert hYlim.tendsto using 2 with n
  apply Subtype.ext
  exact (hemap n).symm

end Asakura.Chapter8
