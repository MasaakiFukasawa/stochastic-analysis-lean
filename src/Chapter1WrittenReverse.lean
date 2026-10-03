import Chapter1WrittenConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/- martconv2, following the printed convex combinations and closed subspaces,
not convergence of projections onto orthogonal complements. -/
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter1Written

/-- The measurable representative is constructed from the eventual tails of an
actually convergent sequence; no completeness of the sigma algebras is assumed. -/
theorem common_tail_representative {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    (G : ℕ → MeasurableSpace Ω) (hG : Antitone G)
    (f : ℕ → Ω → ℝ) (hf : ∀ n, Measurable[G n] (f n)) (Y : Ω → ℝ)
    (ht : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (Y ω))) :
    AEStronglyMeasurable[⨅ n, G n] Y P := by
  let Z := fun ω => limsup (fun n => f n ω) atTop
  have hm (k : ℕ) : Measurable[G k] Z := by
    let g := fun n ω => if k ≤ n then f n ω else 0
    have hg : ∀ n, Measurable[G k] (g n) := by
      intro n
      by_cases h : k ≤ n
      · simpa [g, h] using (hf n).mono (hG h) le_rfl
      · simpa [g, h] using (measurable_const : Measurable[G k] (fun _ : Ω => (0 : ℝ)))
    have he : (fun ω => limsup (fun n => g n ω) atTop) = Z := by
      funext ω
      apply Filter.limsup_congr
      filter_upwards [eventually_ge_atTop k] with n hn
      simp [g, hn]
    rw [← he]
    exact Measurable.limsup hg
  have hZ : Measurable[⨅ n, G n] Z := by
    intro s hs
    exact MeasurableSpace.measurableSet_iInf.mpr (fun n => hm n hs)
  refine ⟨Z, hZ.stronglyMeasurable, ?_⟩
  filter_upwards [ht] with ω hω
  exact hω.limsup_eq.symm

/-- Decreasing projections: the finite convex combination is projected onto a
sufficiently small subspace, and Pythagoras gives monotonicity of the errors. -/
theorem decreasing_projections_from_convex_tails {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U : ℕ → Submodule ℝ H) [∀ n, (U n).HasOrthogonalProjection]
    (hU : Antitone U) (X Y : H) (g : ℕ → H)
    (hg : ∀ n, g n ∈ convexHull ℝ ((fun k => (U k).starProjection X) '' Ici n))
    (ht : Tendsto g atTop (𝓝 Y)) (hY : ∀ n, Y ∈ U n) :
    Tendsto (fun n => (U n).starProjection X) atTop (𝓝 Y) := by
  let f := fun n => (U n).starProjection X
  have htower (i j : ℕ) (hij : i ≤ j) (z : H) :
      (U j).starProjection ((U i).starProjection z) = (U j).starProjection z :=
    DFunLike.congr_fun (Submodule.starProjection_comp_starProjection_of_le (hU hij)) z
  have hfix (n : ℕ) : (U n).starProjection Y = Y :=
    Submodule.starProjection_eq_self_iff.mpr (hY n)
  have hmono : Antitone (fun n => ‖f n-Y‖) := by
    intro i j hij
    have hi : inner ℝ (f i-f j) (f j-Y) = 0 := by
      have hh := (U j).starProjection_inner_eq_zero (f i) (f j-Y)
        ((U j).sub_mem ((U j).starProjection_apply_mem X) (hY j))
      simpa [f, htower i j hij] using hh
    have he : f i-Y = (f i-f j)+(f j-Y) := by abel
    have hp : ‖f i-Y‖^2 = ‖f i-f j‖^2+‖f j-Y‖^2 := by
      rw [he, norm_add_sq_real, hi]
      ring
    nlinarith [norm_nonneg (f i-Y), norm_nonneg (f j-Y), sq_nonneg ‖f i-f j‖]
  have hproject : ∀ n, ∃ k, n ≤ k ∧ (U k).starProjection (g n) = f k := by
    intro n
    let S : Set H := {z | ∃ k, n ≤ k ∧ (U k).starProjection z = f k}
    have hS : Convex ℝ S := by
      intro z hz w hw a b ha hb hab
      obtain ⟨i, hi, hzi⟩ := hz
      obtain ⟨j, hj, hwj⟩ := hw
      have hz' : (U (max i j)).starProjection z = f (max i j) := by
        rw [← htower i (max i j) (le_max_left _ _) z, hzi]
        exact htower i (max i j) (le_max_left _ _) X
      have hw' : (U (max i j)).starProjection w = f (max i j) := by
        rw [← htower j (max i j) (le_max_right _ _) w, hwj]
        exact htower j (max i j) (le_max_right _ _) X
      refine ⟨max i j, hi.trans (le_max_left _ _), ?_⟩
      rw [map_add, map_smul, map_smul, hz', hw', ← add_smul, hab, one_smul]
    apply (convexHull_min (t := S) ?_ hS) (hg n)
    rintro z ⟨k, hk, rfl⟩
    refine ⟨k, hk, ?_⟩
    exact htower k k le_rfl X
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht0 : Tendsto (fun n => ‖g n-Y‖) atTop (𝓝 0) := by
    simpa using (ht.sub_const Y).norm
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (norm_nonneg _))
  · intro ε hε
    obtain ⟨n, hn⟩ := ((tendsto_order.mp ht0).2 ε hε).exists
    obtain ⟨k, hk, hkg⟩ := hproject n
    have hbound : ‖f k-Y‖ ≤ ‖g n-Y‖ := by
      calc
        _ = ‖(U k).starProjection (g n-Y)‖ := by rw [map_sub, hkg, hfix]
        _ ≤ _ := (U k).norm_starProjection_apply_le _
    filter_upwards [eventually_ge_atTop k] with j hj
    exact (hmono hj).trans_lt (hbound.trans_lt hn)

/-- Full reverse L2 proof: convex tails, closed subspaces, a common representative,
set-integral characterization, projection of a finite convex combination. -/
theorem conditional_downward_L2_written {Ω : Type*} {m : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (G : ℕ → MeasurableSpace Ω) (hG : Antitone G) (hle : ∀ n, G n ≤ m)
    (X : Lp ℝ 2 P) :
    Tendsto (fun n => (condExpL2 ℝ ℝ (hle n) X : Lp ℝ 2 P)) atTop
      (𝓝 (condExpL2 ℝ ℝ ((iInf_le G 0).trans (hle 0)) X : Lp ℝ 2 P)) := by
  let U := fun n => lpMeas ℝ ℝ (G n) 2 P
  letI (n : ℕ) : Fact (G n ≤ m) := ⟨hle n⟩
  let f := fun n => (condExpL2 ℝ ℝ (hle n) X : Lp ℝ 2 P)
  have hU : Antitone U := by
    intro i j hij Z hZ
    exact (mem_lpMeas_iff_aestronglyMeasurable.mp hZ).mono (hG hij)
  obtain ⟨g, Y, hg, ht⟩ := convergent_convex_tails f ‖X‖ (fun n => norm_condExpL2_coe_le (hle n) X)
  have hgm : ∀ n, AEStronglyMeasurable[G n] (g n) P := by
    intro n
    apply (convexHull_min (t := (U n : Set (Lp ℝ 2 P))) ?_ (U n).convex) (hg n)
    rintro z ⟨k, hk, rfl⟩
    exact hU hk (condExpL2 ℝ ℝ (hle k) X).property
  have hYm : ∀ k, AEStronglyMeasurable[G k] Y P := by
    intro k
    apply (isClosed_aestronglyMeasurable (p := (2 : ℝ≥0∞)) (hle k)).mem_of_tendsto ht
    filter_upwards [eventually_ge_atTop k] with n hn
    exact (hgm n).mono (hG hn)
  let r := fun k => (hYm k).mk Y
  have hr : ∀ k, Measurable[G k] (r k) := by
    intro k
    exact (hYm k).stronglyMeasurable_mk.measurable
  have heq : ∀ᵐ ω ∂P, ∀ k, r k ω = Y ω :=
    ae_all_iff.mpr (fun k => (hYm k).ae_eq_mk.symm)
  have hrconv : ∀ᵐ ω ∂P, Tendsto (fun k => r k ω) atTop (𝓝 (Y ω)) := by
    filter_upwards [heq] with ω he
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => Y ω) atTop (𝓝 (Y ω)))
  have hYmeas := common_tail_representative P G hG r hr Y hrconv
  have hYint : Integrable Y P := (Lp.memLp Y).integrable (by norm_num)
  have hXint : Integrable X P := (Lp.memLp X).integrable (by norm_num)
  have hchar : ∀ A, MeasurableSet[⨅ n, G n] A →
      ∫ ω in A, Y ω ∂P = ∫ ω in A, X ω ∂P := by
    intro A hA
    have hAm := ((iInf_le G 0).trans (hle 0)) A hA
    let Z : Lp ℝ 2 P := indicatorConstLp 2 hAm (measure_ne_top P A) (1 : ℝ)
    have hi (W : Lp ℝ 2 P) : inner ℝ Z W = ∫ ω in A, W ω ∂P :=
      L2.inner_indicatorConstLp_one hAm (measure_ne_top P A) W
    have htest := convex_tail_fixed_test f g Y (innerSL ℝ Z) (∫ ω in A, X ω ∂P) 0 hg ht (by
      intro k hk
      change inner ℝ Z (f k) = _
      rw [hi]
      exact integral_condExpL2_eq_of_fin_meas_real X ((iInf_le G k) A hA) (measure_ne_top P A))
    change inner ℝ Z Y = _ at htest
    rwa [hi] at htest
  have hYce : Y =ᵐ[P] P[(X : Ω → ℝ) | ⨅ n, G n] :=
    ae_eq_condExp_of_forall_setIntegral_eq ((iInf_le G 0).trans (hle 0)) hXint
      (fun _ _ _ => hYint.integrableOn) (fun A hA _ => hchar A hA) hYmeas
  have hbridge := (Lp.memLp X).condExpL2_ae_eq_condExp (𝕜 := ℝ) ((iInf_le G 0).trans (hle 0))
  simp only [Lp.toLp_coeFn] at hbridge
  have hYeq : Y = (condExpL2 ℝ ℝ ((iInf_le G 0).trans (hle 0)) X : Lp ℝ 2 P) :=
    Lp.ext (hYce.trans hbridge.symm)
  have hfinish := decreasing_projections_from_convex_tails U hU X Y g hg ht
    (fun n => hYmeas.mono (iInf_le G n))
  rw [hYeq] at hfinish
  exact hfinish

end Asakura.Chapter1Written
