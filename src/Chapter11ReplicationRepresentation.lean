import Chapter5NaturalTerminalRepresentation
import Chapter5ConditionalProcessConstructed

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter5
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- The martingale representation used in replication, including the
finite maturity identity and the conditional-price process. -/
theorem replication_representation {Ω : Type*} [m : MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → Q N=0 → MeasurableSet[F t] N)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness Q F W)
    (hA : LocalCovarianceWitness Q F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (c : ℕ → ℝ) (hc : ∀ j,0<c j) (hcm : StrictMono c) (hcT : ∀ j,(c j:EReal)<T)
    (hct : StrictMono (fun j => realTimeClamp (T := T) (c j)))
    (hcut : ∀ j,realTimeClamp (T := T) (c j)<⊤)
    (hcc : ∀ t,t<⊤ → ∃ j,t<realTimeClamp (T := T) (c j)) (hco : ∀ r,∃ j,r≤c j)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (hnat : F (realTimeClamp R)=Asakura.nullAugmentation (m := m) Q (pastSigma W (realTimeClamp R)))
    (U : Ω → ℝ) (hU : MemLp U 2 Q) (hUm : Measurable[F (realTimeClamp R)] U) :
    ∃ G : Ω × ℝ → ℝ,∃ M : ClosedTime T → Ω → ℝ,
      ContinuousM2Witness Q F M ∧ ItoCovarianceFormula Q F W G M ∧ Measurable G ∧
      MemLp G 2 (Q.prod (volume.restrict (Ioi 0))) ∧
      (∀ j,@Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c j) => F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) (c j) => G (z.1,z.2.val))) ∧
      (∀ t,(fun w => (∫ w,U w ∂Q)+M t w)=ᵐ[Q] Q[U|F t]) ∧
      ((fun w => (∫ w,U w ∂Q)+M (realTimeClamp R) w)=ᵐ[Q] U) := by
  obtain ⟨G,M,hM,hMI,hG,hG2,hGp,he⟩ := natural_terminal_brownian_representation
    Q hT F hF hle hnull W A hW hA hclock c hc hcm hcT hct hcut hcc hco R hR hRT hnat U hU hUm
  obtain ⟨_,_,_,hce⟩ := conditional_process_from_represented_terminal Q F hle U hU M hM _ he
  refine ⟨G,M,hM,hMI,hG,hG2,hGp,hce,?_⟩
  exact (hce _).trans (by rw [condExp_of_stronglyMeasurable (hle _) hUm.stronglyMeasurable (hU.integrable (by norm_num))])

/-- A square-integrable gains process has a unique initial price and value
process for a prescribed terminal payment. -/
theorem replication_value_unique {Ω : Type*} [m : MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hle : ∀ t,F t≤m)
    (M N : ClosedTime T → Ω → ℝ) (hM : ContinuousM2Witness Q F M)
    (hN : ContinuousM2Witness Q F N) (a b : ℝ) (R : ClosedTime T)
    (he : (fun w => a+M R w)=ᵐ[Q] fun w => b+N R w) :
    a=b ∧ ∀ t,t≤R → (fun w => a+M t w)=ᵐ[Q] fun w => b+N t w := by
  have hiM := (hM.moment R).integrable (by norm_num : (1:ENNReal)≤2)
  have hiN := (hN.moment R).integrable (by norm_num : (1:ENNReal)≤2)
  have hm0 := integral_congr_ae ((hM.martingale ⊥ R bot_le).trans hM.initial)
  have hn0 := integral_congr_ae ((hN.martingale ⊥ R bot_le).trans hN.initial)
  rw [integral_condExp (hle ⊥)] at hm0 hn0
  have hab := integral_congr_ae he
  simp only [integral_add (integrable_const _) hiM,integral_add (integrable_const _) hiN,
    integral_const,probReal_univ,one_smul,hm0,hn0,add_zero] at hab
  have hab' : a=b := add_right_cancel hab
  refine ⟨hab',?_⟩
  intro t ht
  have hc := condExp_congr_ae (m:=F t) he
  have hcm := condExp_add (integrable_const a) hiM (F t)
  have hcn := condExp_add (integrable_const b) hiN (F t)
  rw [condExp_of_stronglyMeasurable (hle t) stronglyMeasurable_const (integrable_const a)] at hcm
  rw [condExp_of_stronglyMeasurable (hle t) stronglyMeasurable_const (integrable_const b)] at hcn
  filter_upwards [hc,hcm,hcn,hM.martingale t R ht,hN.martingale t R ht] with w hc hm hn hm' hn'
  simpa only [Pi.add_apply,hm',hn'] using hm.symm.trans (hc.trans hn)

end Asakura.Chapter11
