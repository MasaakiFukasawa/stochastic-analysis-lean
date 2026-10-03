import Chapter13DiscountIntegrabilityObstruction
import Chapter13ClosedBondPricing
import Chapter13MaturityCutoff

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

noncomputable def bankBump (t:ℝ):ℝ := max (t-1) 0*(t-3)^2
noncomputable def bankBumpRate (t:ℝ):ℝ := if 1≤t then (t-3)^2+2*(t-1)*(t-3) else 0
noncomputable def heavyBank (t:ℝ) (n:ℕ):ℝ := Real.exp (bankBump t*Real.log ((2:ℝ)^n))
noncomputable def revealFiltration (t:ℝ):MeasurableSpace ℕ := if t<1 then ⊥ else ⊤

theorem bank_bump_primitive (t:ℝ) (ht:0≤t) :
    ∫s in 0..t,bankBumpRate s=bankBump t := by
  have he:=maturity_cutoff_integral (fun s:ℝ => (s-3)^2+2*(s-1)*(s-3)) 0 t 1 ht
  change (∫s in 0..t,if 1≤s then (s-3)^2+2*(s-1)*(s-3) else 0)=bankBump t
  rw [he]
  norm_num
  have hd s:HasDerivAt (fun r:ℝ => (r-1)*(r-3)^2) ((s-3)^2+2*(s-1)*(s-3)) s := by
    convert (((hasDerivAt_id s).sub_const 1).mul (((hasDerivAt_id s).sub_const 3).pow 2)) using 1 <;> (try ext r) <;> simp <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    ((by fun_prop : Continuous (fun s:ℝ => (s-3)^2+2*(s-1)*(s-3))).intervalIntegrable 1 (max t 1))]
  by_cases h:t≤1
  · simp [bankBump,max_eq_right h,max_eq_right (sub_nonpos.mpr h)]
  · have h1:1≤t := le_of_not_ge h
    simp [bankBump,max_eq_left h1,max_eq_left (sub_nonneg.mpr h1)]

theorem heavy_bank_from_short_rate (t:ℝ) (ht:0≤t) (n:ℕ) :
    heavyBank t n=Real.exp (∫s in 0..t,bankBumpRate s*Real.log ((2:ℝ)^n)) := by
  rw [intervalIntegral.integral_mul_const,bank_bump_primitive t ht]
  rfl

theorem heavy_bank_positive (t:ℝ) (n:ℕ) : 0<heavyBank t n := Real.exp_pos _

theorem heavy_bank_inverse_integrable (t:ℝ) :
    Integrable (fun n => (heavyBank t n)⁻¹) halfGeometric := by
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  filter_upwards [] with n
  have hb:1≤heavyBank t n := Real.one_le_exp_iff.mpr (mul_nonneg
    (mul_nonneg (le_max_right _ _) (sq_nonneg _)) (Real.log_nonneg (positive_nonintegrable_growth.1 n)))
  simpa only [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (heavy_bank_positive t n).le)] using inv_le_one_of_one_le₀ hb

theorem reveal_filtration_monotone : Monotone revealFiltration := by
  intro s t hst
  by_cases hs:s<1
  · simp [revealFiltration,hs]
  · have ht:¬t<1 := fun ht => hs (hst.trans_lt ht)
    simp [revealFiltration,hs,ht]

theorem reveal_filtration_right_continuous (t:ℝ) :
    revealFiltration t=⨅u:Ioi t,revealFiltration u.val := by
  apply le_antisymm
  · exact le_iInf (fun u => reveal_filtration_monotone u.property.le)
  · by_cases ht:t<1
    · have hm:t<(t+1)/2 := by linarith
      have hm1:(t+1)/2<1 := by linarith
      have hh:=iInf_le (fun u:Ioi t => revealFiltration u.val) ⟨(t+1)/2,hm⟩
      simpa only [revealFiltration,if_pos hm1,if_pos ht] using hh
    · simp [revealFiltration,ht]

theorem reveal_filtration_initial_trivial : revealFiltration 0=⊥ := by norm_num [revealFiltration]

theorem heavy_bank_adapted (t:ℝ) : Measurable[revealFiltration t] (heavyBank t) := by
  by_cases ht:t<1
  · have he:heavyBank t=(fun _ :ℕ => (1:ℝ)) := by
      funext n
      simp [heavyBank,bankBump,max_eq_right (sub_nonpos.mpr ht.le)]
    rw [he]
    exact measurable_const
  · change @Measurable ℕ ℝ (revealFiltration t) _ (heavyBank t)
    rw [revealFiltration,if_neg ht]
    exact measurable_from_top

theorem heavy_short_rate_adapted (t:ℝ) :
    Measurable[revealFiltration t] (fun n:ℕ => bankBumpRate t*Real.log ((2:ℝ)^n)) := by
  by_cases ht:t<1
  · simp only [bankBumpRate,if_neg (not_le.mpr ht),zero_mul]
    exact measurable_const
  · change @Measurable ℕ ℝ (revealFiltration t) _ _
    rw [revealFiltration,if_neg ht]
    exact measurable_from_top

theorem heavy_bank_post_maturity (u t:ℝ) (hut:u≤t) :
    (fun n => heavyBank t n*halfGeometric[(fun k => (heavyBank u k)⁻¹)|revealFiltration t] n)=
      (fun n => heavyBank t n/heavyBank u n) := by
  have hm:StronglyMeasurable[revealFiltration t] (fun n => (heavyBank u n)⁻¹) :=
    ((heavy_bank_adapted u).inv.mono (reveal_filtration_monotone hut) le_rfl).stronglyMeasurable
  rw [condExp_of_stronglyMeasurable (show revealFiltration t ≤ (inferInstance : MeasurableSpace ℕ) from by change revealFiltration t≤⊤;exact le_top) hm
    (heavy_bank_inverse_integrable u)]
  rfl

theorem heavy_bank_ratio_not_integrable :
    ¬Integrable (fun n => heavyBank 2 n/heavyBank 3 n) halfGeometric := by
  have he:(fun n => heavyBank 2 n/heavyBank 3 n)=(fun n:ℕ => (2:ℝ)^n) := by
    funext n
    have h2:bankBump 2=1 := by norm_num [bankBump]
    have h3:bankBump 3=0 := by norm_num [bankBump]
    simp only [heavyBank,h2,h3,one_mul,zero_mul,Real.exp_zero,div_one]
    exact Real.exp_log (pow_pos (by norm_num : (0:ℝ)<2) n)
  rw [he]
  exact positive_nonintegrable_growth.2

theorem heavy_bank_discounted_bonds_martingale (u:ℝ) :
    let p:=fun t n => heavyBank t n*halfGeometric[(fun k => (heavyBank u k)⁻¹)|revealFiltration t] n
    (∀t,Integrable (fun n => p t n/heavyBank t n) halfGeometric) ∧
    (∀s t,s≤t → halfGeometric[(fun n => p t n/heavyBank t n)|revealFiltration s]=ᵐ[halfGeometric]
      (fun n => p s n/heavyBank s n)) := by
  intro p
  exact closed_bond_pricing_martingale halfGeometric revealFiltration reveal_filtration_monotone
    (fun t => by change revealFiltration t≤⊤;exact le_top) heavyBank p
    (fun t n => (heavy_bank_positive t n).ne') (fun n => (heavyBank u n)⁻¹)
    (heavy_bank_inverse_integrable u) (fun _ => ae_of_all _ fun _ => rfl)
end Asakura.Chapter13
#print axioms Asakura.Chapter13.bank_bump_primitive
#print axioms Asakura.Chapter13.heavy_bank_from_short_rate
#print axioms Asakura.Chapter13.heavy_bank_positive
#print axioms Asakura.Chapter13.heavy_bank_inverse_integrable
#print axioms Asakura.Chapter13.reveal_filtration_monotone
#print axioms Asakura.Chapter13.heavy_bank_ratio_not_integrable
#print axioms Asakura.Chapter13.heavy_bank_discounted_bonds_martingale

#print axioms Asakura.Chapter13.heavy_bank_adapted
#print axioms Asakura.Chapter13.heavy_short_rate_adapted
#print axioms Asakura.Chapter13.heavy_bank_post_maturity

#print axioms Asakura.Chapter13.reveal_filtration_right_continuous
#print axioms Asakura.Chapter13.reveal_filtration_initial_trivial
