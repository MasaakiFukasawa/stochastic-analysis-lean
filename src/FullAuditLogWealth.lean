import FullAuditFinanceOptimization
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable def terminalLogWealth {Ω : Type*} (π : Ω → ℝ → ℝ) (M : Ω → ℝ)
    (x r μ σ T : ℝ) (ω : Ω) : ℝ :=
  x*Real.exp ((∫ t in Icc 0 T, r+π ω t*(μ-r)-σ^2*(π ω t)^2/2)+M ω)

/-- The full expectation calculation for the printed exponential wealth.
 The only stochastic-integral input is its integrability and zero mean,
 supplied by the preceding Ito construction for bounded strategies. All
 time integrals, logarithms, and their integrability are checked here. -/
theorem logarithmic_wealth_identity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (π : Ω → ℝ → ℝ) (M : Ω → ℝ)
    (x r μ σ T K : ℝ) (hx : 0 < x) (hσ : σ ≠ 0) (hT : 0 ≤ T)
    (hm : Measurable (Function.uncurry π)) (hb : ∀ ω t, ‖π ω t‖ ≤ K)
    (hMi : Integrable M P) (hM0 : (∫ ω, M ω ∂P) = 0) :
    Integrable (fun ω => Real.log (terminalLogWealth π M x r μ σ T ω)) P ∧
      (∫ ω, Real.log (terminalLogWealth π M x r μ σ T ω) ∂P) =
      Real.log x+(r+(μ-r)^2/(2*σ^2))*T-
        σ^2/2*(∫ ω, (∫ t in Icc 0 T, (π ω t-(μ-r)/σ^2)^2) ∂P) := by
  let ν : Measure ℝ := volume.restrict (Icc 0 T)
  let a := (μ-r)/σ^2
  let c := r+(μ-r)^2/(2*σ^2)
  let L := fun ω => ∫ t, (π ω t-a)^2 ∂ν
  let R := fun ω => ∫ t, r+π ω t*(μ-r)-σ^2*(π ω t)^2/2 ∂ν
  have hmass : ν.real univ = T := by
    rw [Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,sub_zero]
    exact ENNReal.toReal_ofReal hT
  have hπ2 : MemLp (Function.uncurry π) 2 (P.prod ν) :=
    MemLp.of_bound hm.aestronglyMeasurable K (Eventually.of_forall fun z => hb z.1 z.2)
  have hLs : Integrable (fun z : Ω × ℝ => (π z.1 z.2-a)^2) (P.prod ν) :=
    (memLp_two_iff_integrable_sq (hπ2.sub (memLp_const a)).aestronglyMeasurable).mp (hπ2.sub (memLp_const a))
  have hLi : Integrable L P := hLs.integral_prod_left
  have hR (ω) : R ω = c*T-σ^2/2*L ω := by
    have hmt : Measurable (π ω) := hm.comp (measurable_const.prodMk measurable_id)
    have ht2 : MemLp (π ω) 2 ν := MemLp.of_bound hmt.aestronglyMeasurable K (Eventually.of_forall (hb ω))
    have htL : Integrable (fun t => (π ω t-a)^2) ν :=
      (memLp_two_iff_integrable_sq (ht2.sub (memLp_const a)).aestronglyMeasurable).mp (ht2.sub (memLp_const a))
    change (∫ t, r+π ω t*(μ-r)-σ^2*(π ω t)^2/2 ∂ν) = _
    simp_rw [finance_log_square r μ σ _ hσ]
    rw [integral_sub (integrable_const c) (htL.const_mul (σ^2/2)),integral_const,integral_const_mul]
    change ν.real univ*c-σ^2/2*L ω = _
    rw [hmass]
    ring
  have hRi : Integrable R P := by
    have he : R = (fun _ => c*T)-(σ^2/2) • L := by funext ω; exact hR ω
    rw [he]
    exact (integrable_const _).sub (hLi.smul _)
  have hlog (ω) : Real.log (terminalLogWealth π M x r μ σ T ω) = Real.log x+R ω+M ω := by
    dsimp only [terminalLogWealth]
    rw [Real.log_mul (ne_of_gt hx) (Real.exp_ne_zero _),Real.log_exp]
    change Real.log x+(R ω+M ω) = Real.log x+R ω+M ω
    ring
  have hlogi : Integrable (fun ω => Real.log (terminalLogWealth π M x r μ σ T ω)) P := by
    simp only [hlog]
    exact ((integrable_const _).add hRi).add hMi
  refine ⟨hlogi,?_⟩
  simp only [hlog]
  have hiadd : Integrable (fun ω => Real.log x+R ω) P := (integrable_const _).add hRi
  rw [integral_add hiadd hMi,
    integral_add (integrable_const _) hRi,hM0,add_zero,integral_const,probReal_univ,one_smul]
  have hIR : (∫ ω, R ω ∂P) = c*T-σ^2/2*(∫ ω, L ω ∂P) := by
    simp only [hR]
    rw [integral_sub (integrable_const (c*T)) (hLi.const_mul (σ^2/2)),integral_const,probReal_univ,one_smul,integral_const_mul]
  rw [hIR]
  change Real.log x+(c*T-σ^2/2*(∫ ω, L ω ∂P)) = _
  dsimp only [c,L,a,ν]
  ring

/-- The optimal upper bound and its attainment by the constant strategy. -/
theorem logarithmic_wealth_optimal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (π : Ω → ℝ → ℝ) (M : Ω → ℝ)
    (x r μ σ T K : ℝ) (hx : 0 < x) (hσ : σ ≠ 0) (hT : 0 ≤ T)
    (hm : Measurable (Function.uncurry π)) (hb : ∀ ω t, ‖π ω t‖ ≤ K)
    (hMi : Integrable M P) (hM0 : (∫ ω, M ω ∂P) = 0) :
    (∫ ω, Real.log (terminalLogWealth π M x r μ σ T ω) ∂P) ≤
      Real.log x+(r+(μ-r)^2/(2*σ^2))*T ∧
    ((∀ ω t, π ω t = (μ-r)/σ^2) →
      (∫ ω, Real.log (terminalLogWealth π M x r μ σ T ω) ∂P) =
        Real.log x+(r+(μ-r)^2/(2*σ^2))*T) := by
  rw [(logarithmic_wealth_identity P π M x r μ σ T K hx hσ hT hm hb hMi hM0).2]
  constructor
  · have hn : 0 ≤ ∫ ω, (∫ t in Icc 0 T, (π ω t-(μ-r)/σ^2)^2) ∂P :=
      integral_nonneg fun ω => integral_nonneg fun t => sq_nonneg _
    have hprod : 0 ≤ σ^2/2*(∫ ω, (∫ t in Icc 0 T, (π ω t-(μ-r)/σ^2)^2) ∂P) := mul_nonneg (by positivity) hn
    linarith
  · intro hπ
    simp only [hπ,sub_self,zero_pow (by norm_num : (2:ℕ) ≠ 0),integral_zero,mul_zero,sub_zero]

end Asakura.FullAudit
