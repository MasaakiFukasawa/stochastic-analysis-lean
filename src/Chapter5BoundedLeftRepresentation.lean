import Chapter5LeftItoFiniteSum
import Chapter5CoordinateDerivativeBounds

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

/-- Revised Lemma 5.1.1: the original bounded coordinate derivatives
construct bounded, adapted, left-continuous integrands, actual M² integrals,
and expectation centering at the last observation time. -/
theorem bounded_C2_grid_left_representation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    {n k : ℕ} (W : Fin (n+1) → ClosedTime T → Ω → ℝ) (A : ClosedTime T → Ω → ℝ)
    (hW : ∀ i,LocalMProcessWitness P F (W i))
    (hCOV : ∀ i j,LocalCovarianceWitness P F (W i) (W j) (fun t w => if i=j then A t w else 0))
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (c : ℕ → ℝ) (hc : ∀ j,0≤c j) (hcm : Monotone c) (hcT : ∀ j,(c j:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ j,t<realTimeClamp (T := T) (c j))
    (index : Fin k → Fin (n+1)) (q : ℕ → ℝ) (hq : StrictMono q) (hq0 : q 0=0)
    (N : ℕ) (hqNT : (q N:EReal)<T) (obs : Fin k → ℕ) (hobs : ∀ i,obs i≤N)
    (f : (Fin k → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (C K : ℝ≥0)
    (hC : ∀ x i,|fderiv ℝ f x (Pi.single i 1)|≤C)
    (hK : ∀ x i j,|fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)|≤K) :
    ∃ H : Fin (n+1) → Ω × ℝ → ℝ,∃ Z : Fin (n+1) → ClosedTime T → Ω → ℝ,∃ B : ℝ,
      (∀ i w t,ContinuousWithinAt (fun r => H i (w,r)) (Iic t) t) ∧
      (∀ i w r,|H i (w,r)|≤B) ∧
      (∀ i (r : ℝ),0≤r → (r:EReal)<T → Measurable[F (realTimeClamp r)] (fun w => H i (w,r))) ∧
      (∀ i,ContinuousM2Witness P F (Z i)) ∧
      (∀ i,ItoCovarianceFormula P F (W i) (H i) (Z i)) ∧
      (∀ i,Z i (realTimeClamp (q N))=Z i ⊤) ∧
      MemLp (fun w => f (fun i => W (index i) (realTimeClamp (q (obs i))) w)) 2 P ∧
      (fun w => f (fun i => W (index i) (realTimeClamp (q (obs i))) w)) =ᵐ[P]
        fun w => (∫ w,f (fun i => W (index i) (realTimeClamp (q (obs i))) w) ∂P)+
          ∑ i,Z i (realTimeClamp (q N)) w := by
  classical
  obtain ⟨u,hu⟩ := bounded_coordinate_C2_data k f hf C K hC hK
  obtain ⟨J,hJs,hrep⟩ := finite_grid_left_observation_representation P hT F hF hle hnull W A hW hCOV hclock
    c hc hcm hcT hcc index q hq hq0 N hqNT obs hobs u
  let s : Finset (Fin N × Fin k) := Finset.univ.filter (fun p => N-p.1.val≤obs p.2)
  let sj := fun j => s.filter (fun p => index p.2=j)
  let H := fun j z => ∑ p∈sj j,(J p.1).integrand p.2 z
  let Z := fun j t w => ∑ p∈sj j,(J p.1).integral p.2 t w
  let B := ∑ p∈s,((J p.1).bound:ℝ)
  have hIZ j := finite_M2_ito_sum P hT F hF hle hnull (W j) (hW j)
    (fun p => (J p.1).integrand p.2) (fun p => (J p.1).integral p.2) (sj j)
    (fun p _ => (J p.1).martingale p.2) (fun p hp => by
      have he : index p.2=j := (Finset.mem_filter.mp hp).2
      rw [← he]; exact (J p.1).formula p.2)
  have hstop j t w (ht : realTimeClamp (q N)≤t) : Z j t w=Z j ⊤ w :=
    Finset.sum_congr rfl (fun p _ => hJs p.1 p.2 t w ht)
  have hsum w : (∑ j,Z j ⊤ w)=
      ∑ l : Fin N,∑ i ∈ Finset.univ.filter (fun i => N-l.val≤obs i),(J l).integral i ⊤ w := by
    dsimp only [Z,sj]
    rw [Finset.sum_fiberwise_of_maps_to (fun p _ => Finset.mem_univ (index p.2))]
    simp only [s,Finset.sum_filter,Fintype.sum_prod_type]
  let payoff := fun w => f (fun i => W (index i) (realTimeClamp (q (obs i))) w)
  let b := (gaussianRecursion u n (fun l => observationNoiseMap index (fun i => N-l≤obs i))
    (fun l => q (N-l)-q (N-(l+1))) N).value 0
  have hr : payoff =ᵐ[P] fun w => b+∑ j,Z j ⊤ w := by
    simpa only [payoff,b,hsum,hu] using hrep
  have hzi j : Integrable (Z j ⊤) P := ((hIZ j).1.moment ⊤).integrable (by norm_num)
  have hmean j : (∫ w,Z j ⊤ w ∂P)=0 := by
    rw [show Z j ⊤=(fun w => ∑ p∈sj j,(J p.1).integral p.2 ⊤ w) from rfl,
      integral_finsetSum (sj j) (fun p _ => ((J p.1).martingale p.2 |>.moment ⊤).integrable (by norm_num))]
    simp only [fun (p : Fin N × Fin k) => (J p.1).mean p.2,Finset.sum_const_zero]
  have hpay : MemLp payoff 2 P :=
    ((memLp_const b).add (memLp_finsetSum _ (fun j _ => (hIZ j).1.moment ⊤))).ae_eq hr.symm
  have hmeanpay : (∫ w,payoff w ∂P)=b := by
    rw [integral_congr_ae hr,integral_add (integrable_const b) (integrable_finsetSum _ (fun j _ => hzi j)),
      integral_finsetSum _ (fun j _ => hzi j)]
    simp [hmean]
  refine ⟨H,Z,B,?_,?_,?_,(fun j => (hIZ j).1),(fun j => (hIZ j).2),?_,hpay,?_⟩
  · intro j w t
    exact tendsto_finsetSum _ (fun p _ => (J p.1).leftContinuous p.2 w t)
  · intro j w r
    calc
      |H j (w,r)| ≤ ∑ p∈sj j,|(J p.1).integrand p.2 (w,r)| := Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ p∈sj j,((J p.1).bound:ℝ) := Finset.sum_le_sum (fun p _ => (J p.1).bounded p.2 w r)
      _ ≤ B := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun p _ _ => (J p.1).bound.property)
  · intro j r hr hrT
    exact Finset.measurable_fun_sum _ (fun p _ => (J p.1).adapted p.2 r hr hrT)
  · intro j
    exact funext (fun w => hstop j _ w le_rfl)
  · filter_upwards [hr] with w hw
    change payoff w=(∫ w,payoff w ∂P)+_
    rw [hmeanpay,hw]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => (hstop j _ w le_rfl).symm)

end Asakura.Chapter5
