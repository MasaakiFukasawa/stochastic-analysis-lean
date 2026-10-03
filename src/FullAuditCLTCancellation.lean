import FullAuditCLTRemainders
import FullAuditIndependenceExercises
import FullAuditConditionalExercises

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- The C2/independence step used twice in the CLT proof, including the
integrability justified by the bounded derivative coefficient. -/
theorem clt_independent_bounded_product {Ω : Type*} {G H m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hG : G ≤ m) (hH : H ≤ m)
    {X U : Ω → ℝ} (hX : Integrable X P) (hmX : StronglyMeasurable[H] X)
    (hmU : StronglyMeasurable[G] U) (C : ℝ) (hU : ∀ᵐ ω ∂P, ‖U ω‖ ≤ C)
    (hind : Indep H G P) :
    (∫ ω, U ω * X ω ∂P) = (∫ ω, U ω ∂P) * (∫ ω, X ω ∂P) := by
  have hUm : AEStronglyMeasurable U P := (hmU.mono hG).aestronglyMeasurable
  have hUX : Integrable (fun ω => U ω*X ω) P := hX.bdd_mul hUm hU
  have hc := condExp_indep_eq hH hG hmX hind
  have hp := condExp_mul_of_stronglyMeasurable_left (m := G) hmU hUX hX
  calc
    _ = ∫ ω, P[U*X | G] ω ∂P := (integral_condExp hG).symm
    _ = ∫ ω, U ω*(∫ x, X x ∂P) ∂P := integral_congr_ae (by
      filter_upwards [hp,hc] with ω hp hc
      simp only [Pi.mul_apply] at hp
      rw [hp,hc])
    _ = _ := integral_mul_const _ _

/-- The heat-equation cancellation of the first and second order terms. -/
theorem clt_heat_increment_cancellation {Ω : Type*} {G H m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hG : G ≤ m) (hH : H ≤ m)
    {X U V : Ω → ℝ} (hmX : StronglyMeasurable[H] X)
    (hX : MemLp X 2 P) (hmean : ∫ ω, X ω ∂P = 0)
    (hmU : StronglyMeasurable[G] U) (hmV : StronglyMeasurable[G] V)
    (C : ℝ) (hU : ∀ᵐ ω ∂P, ‖U ω‖ ≤ C) (hV : ∀ᵐ ω ∂P, ‖V ω‖ ≤ C)
    (hind : Indep H G P) :
    ∫ ω, U ω*X ω - ((∫ x, X x ^ 2 ∂P)/2)*V ω + (1/2)*V ω*X ω ^ 2 ∂P = 0 := by
  have hiX : Integrable X P := hX.integrable (by norm_num)
  have hiX2 : Integrable (fun ω => X ω ^ 2) P := (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mp hX
  have hu := clt_independent_bounded_product P hG hH hiX hmX hmU C hU hind
  have hv := clt_independent_bounded_product P hG hH hiX2 (hmX.pow 2) hmV C hV hind
  rw [hmean,mul_zero] at hu
  have hiU : AEStronglyMeasurable U P := (hmU.mono hG).aestronglyMeasurable
  have hiV : AEStronglyMeasurable V P := (hmV.mono hG).aestronglyMeasurable
  have hvint : Integrable V P := Integrable.of_bound hiV C hV
  have hux : Integrable (fun ω => U ω*X ω) P := hiX.bdd_mul hiU hU
  have hvx : Integrable (fun ω => V ω*X ω ^ 2) P := hiX2.bdd_mul hiV hV
  have he : (fun ω => U ω*X ω - ((∫ x, X x ^ 2 ∂P)/2)*V ω + (1/2)*V ω*X ω ^ 2) =
      fun ω => (U ω*X ω - ((∫ x, X x ^ 2 ∂P)/2)*V ω) + (1/2)*(V ω*X ω ^ 2) := by
    funext ω
    ring
  have hsub : Integrable (fun ω => U ω*X ω - ((∫ x, X x ^ 2 ∂P)/2)*V ω) P := hux.sub (hvint.const_mul _)
  rw [he,integral_add hsub (hvx.const_mul _),
    integral_sub hux (hvint.const_mul _),integral_const_mul,integral_const_mul,hu,hv]
  ring

/-- Telescoping the expected increments along one triangular-array row. -/
theorem clt_expectation_telescope {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (n : ℕ) (q : Fin (n+1) → Ω → ℝ) (R : Fin n → Ω → ℝ)
    (hq : ∀ i, Integrable (q i) P)
    (hinc : ∀ i, ∫ ω, q i.succ ω - q i.castSucc ω ∂P = ∫ ω, R i ω ∂P) :
    (∫ ω, q (Fin.last n) ω ∂P) - (∫ ω, q 0 ω ∂P) = ∑ i, ∫ ω, R i ω ∂P := by
  have hh : (∑ i : Fin n, ∫ ω, q i.succ ω ∂P) - (∑ i : Fin n, ∫ ω, q i.castSucc ω ∂P) =
      ∑ i, ∫ ω, R i ω ∂P := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← integral_sub (hq i.succ) (hq i.castSucc)]
    exact hinc i
  have hs := Fin.sum_univ_succ (fun i : Fin (n+1) => ∫ ω, q i ω ∂P)
  have ht := Fin.sum_univ_castSucc (fun i : Fin (n+1) => ∫ ω, q i ω ∂P)
  linarith

/-- The last expectation limit before replacing smooth test functions by
indicators. Initial heat means and the absolute remainder sum are explicit. -/
theorem clt_smooth_test_limit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (q : (n : ℕ) → Fin (n+1) → Ω → ℝ) (R : (n : ℕ) → Fin n → Ω → ℝ)
    (hq : ∀ n i, Integrable (q n i) P)
    (hinc : ∀ n i, ∫ ω, q n i.succ ω - q n i.castSucc ω ∂P = ∫ ω, R n i ω ∂P)
    (L : ℝ) (hinit : Tendsto (fun n => ∫ ω, q n 0 ω ∂P) atTop (𝓝 L))
    (hR : Tendsto (fun n => ∑ i : Fin n, ∫ ω, |R n i ω| ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, q n (Fin.last n) ω ∂P) atTop (𝓝 L) := by
  have herr : ∀ n, |(∫ ω, q n (Fin.last n) ω ∂P)-(∫ ω, q n 0 ω ∂P)| ≤
      ∑ i : Fin n, ∫ ω, |R n i ω| ∂P := by
    intro n
    rw [clt_expectation_telescope P n (q n) (R n) (hq n) (hinc n)]
    calc
      _ ≤ ∑ i : Fin n, |∫ ω, R n i ω ∂P| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun i _ => abs_integral_le_integral_abs
  have he := squeeze_zero (fun n => abs_nonneg _) herr hR
  have hd : Tendsto (fun n => (∫ ω, q n (Fin.last n) ω ∂P)-(∫ ω, q n 0 ω ∂P)) atTop (𝓝 0) := by
    apply squeeze_zero_norm
    · intro n; exact herr n
    · exact hR
  have ht := hd.add hinit
  simpa only [sub_add_cancel,zero_add] using ht

end Asakura.FullAudit
