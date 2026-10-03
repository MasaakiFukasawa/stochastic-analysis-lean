import Chapter1WrittenSteps
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/- Forward L2 convergence by the manuscript's convex-tail / pi-lambda proof.
No martingale convergence theorem or convergence theorem for projections is used. -/
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter1Written
variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}

/-- The lambda-system step in martconv, with each of its closure properties explicit. -/
theorem set_integrals_increasing_sigma (G : ℕ → MeasurableSpace Ω)
    (hmono : Monotone G) (hle : ∀ n, G n ≤ m)
    {X Y : Ω → ℝ} (hX : Integrable X P) (hY : Integrable Y P)
    (hbase : ∀ n A, MeasurableSet[G n] A → ∫ ω in A, Y ω ∂P = ∫ ω in A, X ω ∂P) :
    ∀ A, MeasurableSet[⨆ n, G n] A → ∫ ω in A, Y ω ∂P = ∫ ω in A, X ω ∂P := by
  have htop : (⨆ n, G n) ≤ m := iSup_le hle
  have htot : ∫ ω, Y ω ∂P = ∫ ω, X ω ∂P := by simpa using hbase 0 univ .univ
  have hpi : IsPiSystem (⋃ n, {A | MeasurableSet[G n] A}) := by
    apply isPiSystem_iUnion_of_monotone _
    · intro n A hA B hB _
      exact hA.inter hB
    · intro i j hij A hA
      exact hmono hij A hA
  intro A hA
  refine MeasurableSpace.induction_on_inter
    (m := ⨆ n, G n) (C := fun A _ => ∫ ω in A, Y ω ∂P = ∫ ω in A, X ω ∂P)
    (MeasurableSpace.generateFrom_iUnion_measurableSet G).symm hpi ?_ ?_ ?_ ?_ A hA
  · simp
  · intro A hA
    obtain ⟨n, hn⟩ := mem_iUnion.mp hA
    exact hbase n A hn
  · intro A hA he
    have hy := integral_add_compl (htop A hA) hY
    have hx := integral_add_compl (htop A hA) hX
    linarith
  · intro A hd hm he
    rw [integral_iUnion (fun n => htop _ (hm n)) hd hY.integrableOn,
      integral_iUnion (fun n => htop _ (hm n)) hd hX.integrableOn]
    exact tsum_congr he

/-- The last step of martconv: a convergent forward convex combination and
best approximation yield convergence of the original projections. -/
theorem projections_from_convex_tails {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (U : ℕ → Submodule ℝ H) [∀ n, (U n).HasOrthogonalProjection]
    (hU : Monotone U) (X Y : H) (g : ℕ → H)
    (hg : ∀ n, g n ∈ convexHull ℝ ((fun k => (U k).starProjection X) '' Ici n))
    (ht : Tendsto g atTop (𝓝 Y))
    (hproj : ∀ n, (U n).starProjection Y = (U n).starProjection X) :
    Tendsto (fun n => (U n).starProjection X) atTop (𝓝 Y) := by
  have hmin (n : ℕ) (z : H) (hz : z ∈ U n) :
      ‖Y - (U n).starProjection X‖ ≤ ‖Y-z‖ := by
    rw [← hproj n, Submodule.starProjection_minimal]
    have hb : BddBelow (range (fun w : U n => ‖Y-(w : H)‖)) :=
      ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
    exact ciInf_le hb ⟨z, hz⟩
  have hmono : Antitone (fun n => ‖Y-(U n).starProjection X‖) := by
    intro i j hij
    exact hmin j _ (hU hij ((U i).starProjection_apply_mem X))
  have hgm : ∀ n, ∃ k, g n ∈ U k := by
    intro n
    apply (Submodule.mem_iSup_of_directed U hU.directed_le).mp
    apply (convexHull_min (t := (⨆ k, U k : Submodule ℝ H)) ?_ (Submodule.convex _)) (hg n)
    rintro z ⟨k, hk, rfl⟩
    exact (le_iSup U k) ((U k).starProjection_apply_mem X)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hg0 : Tendsto (fun n => ‖Y-g n‖) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := Y)).sub ht).norm
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (norm_nonneg _))
  · intro ε hε
    obtain ⟨n, hn⟩ := ((tendsto_order.mp hg0).2 ε hε).exists
    obtain ⟨k, hk⟩ := hgm n
    filter_upwards [eventually_ge_atTop k] with j hj
    rw [norm_sub_rev]
    exact (hmono hj).trans_lt ((hmin k _ hk).trans_lt hn)

/-- Full forward L2 proof following martconv: construct convex tails, identify
their limit by fixed-event integrals and pi-lambda, then use best approximation. -/
theorem conditional_upward_L2_written [IsProbabilityMeasure P]
    (G : ℕ → MeasurableSpace Ω) (hmono : Monotone G) (hle : ∀ n, G n ≤ m)
    (X : Lp ℝ 2 P) :
    Tendsto (fun n => (condExpL2 ℝ ℝ (hle n) X : Lp ℝ 2 P)) atTop
      (𝓝 (condExpL2 ℝ ℝ (iSup_le hle) X : Lp ℝ 2 P)) := by
  let U := fun n => lpMeas ℝ ℝ (G n) 2 P
  let V := lpMeas ℝ ℝ (⨆ n, G n) 2 P
  letI (n : ℕ) : Fact (G n ≤ m) := ⟨hle n⟩
  letI : Fact ((⨆ n, G n) ≤ m) := ⟨iSup_le hle⟩
  let f := fun n => (condExpL2 ℝ ℝ (hle n) X : Lp ℝ 2 P)
  have hU : Monotone U := by
    intro i j hij Z hZ
    exact (mem_lpMeas_iff_aestronglyMeasurable.mp hZ).mono (hmono hij)
  have hUV : ∀ n, U n ≤ V := by
    intro n Z hZ
    exact (mem_lpMeas_iff_aestronglyMeasurable.mp hZ).mono (le_iSup G n)
  obtain ⟨g, Y, hg, ht⟩ := convergent_convex_tails f ‖X‖ (fun n => norm_condExpL2_coe_le (hle n) X)
  have hgv : ∀ n, g n ∈ V := by
    intro n
    apply (convexHull_min (t := (V : Set (Lp ℝ 2 P))) ?_ V.convex) (hg n)
    rintro z ⟨k, hk, rfl⟩
    exact hUV k (condExpL2 ℝ ℝ (hle k) X).property
  have hYv : AEStronglyMeasurable[⨆ n, G n] Y P :=
    (isClosed_aestronglyMeasurable (iSup_le hle)).mem_of_tendsto ht (Eventually.of_forall hgv)
  have hYint : Integrable Y P := (Lp.memLp Y).integrable (by norm_num)
  have hXint : Integrable X P := (Lp.memLp X).integrable (by norm_num)
  have hbase : ∀ n A, MeasurableSet[G n] A →
      ∫ ω in A, Y ω ∂P = ∫ ω in A, X ω ∂P := by
    intro n A hA
    let Z : Lp ℝ 2 P := indicatorConstLp 2 (hle n A hA) (measure_ne_top P A) (1 : ℝ)
    have hi (W : Lp ℝ 2 P) : inner ℝ Z W = ∫ ω in A, W ω ∂P :=
      L2.inner_indicatorConstLp_one (hle n A hA) (measure_ne_top P A) W
    have htest := convex_tail_fixed_test f g Y (innerSL ℝ Z) (∫ ω in A, X ω ∂P) n hg ht (by
      intro k hk
      change inner ℝ Z (f k) = _
      rw [hi]
      exact integral_condExpL2_eq_of_fin_meas_real X (hmono hk A hA) (measure_ne_top P A))
    change inner ℝ Z Y = _ at htest
    rwa [hi] at htest
  have hchar := set_integrals_increasing_sigma G hmono hle hXint hYint hbase
  have hYce : Y =ᵐ[P] P[(X : Ω → ℝ) | ⨆ n, G n] :=
    ae_eq_condExp_of_forall_setIntegral_eq (iSup_le hle) hXint
      (fun _ _ _ => hYint.integrableOn) (fun A hA _ => hchar A hA) hYv
  have hbridge := (Lp.memLp X).condExpL2_ae_eq_condExp (𝕜 := ℝ) (iSup_le hle)
  simp only [Lp.toLp_coeFn] at hbridge
  have hYeq : Y = (condExpL2 ℝ ℝ (iSup_le hle) X : Lp ℝ 2 P) :=
    Lp.ext (hYce.trans hbridge.symm)
  have hp : ∀ n, (U n).starProjection Y = (U n).starProjection X := by
    intro n
    rw [hYeq]
    change (U n).starProjection (V.starProjection X) = (U n).starProjection X
    exact DFunLike.congr_fun (Submodule.starProjection_comp_starProjection_of_le (hUV n)) X
  have hfinish := projections_from_convex_tails U hU X Y g hg ht hp
  rw [hYeq] at hfinish
  exact hfinish

end Asakura.Chapter1Written
