import Chapter5ObservationGenerator
import Chapter5ClockAugmentedFamily
import Chapter5ZeroGeneratorIncrement
import Chapter3LocalSemimartingale

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Actual Ito representation on one observation interval: random past
values are stopped adapted coordinates, and every integral is constructed. -/
theorem stopped_observation_ito_increment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    {d k : ℕ} (W : Fin d → ClosedTime T → Ω → ℝ) (A : ClosedTime T → Ω → ℝ)
    (hW : ∀ i,LocalMProcessWitness P F (W i))
    (hC : ∀ i j,LocalCovarianceWitness P F (W i) (W j) (fun t w => if i=j then A t w else 0))
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := T) (c n))
    (index : Fin k → Fin d) (active : Fin k → Prop) [DecidablePred active]
    (τ : Fin k → ℝ) (hτ : ∀ i,0≤τ i) (hτT : ∀ i,(τ i:EReal)<T)
    (a b : ℝ) (ha : 0≤a) (hab : a≤b) (hbT : (b:EReal)<T)
    (hpast : ∀ i,¬active i → τ i≤a) (hcurrent : ∀ i,active i → τ i=b)
    (g : ((Fin k → ℝ) × ℝ) → ℝ) (hg : ContDiff ℝ 2 g)
    (hzero : ∀ p : (Fin k → ℝ) × ℝ,p.2≤b →
      fderiv ℝ g p (0,1)+(1/2:ℝ)*∑ l : Fin d,
        fderiv ℝ (fderiv ℝ g) p (observationNoiseMap index active (Pi.single l 1),0)
          (observationNoiseMap index active (Pi.single l 1),0)=0) :
    let X : Fin k → ClosedTime T → Ω → ℝ := fun i t w => W (index i) (min (realTimeClamp (τ i)) t) w
    let K : ClosedTime T → Ω → ℝ := fun t (_ : Ω) => (finitePrefixTime (T := T) b (ha.trans hab) t).val
    let XX : Fin (k+1) → ClosedTime T → Ω → ℝ := Fin.cons K X
    let M : Fin (k+1) → ClosedTime T → Ω → ℝ := Fin.cons (fun _ _ => (0:ℝ)) X
    let f : (Fin (k+1) → ℝ) → ℝ := fun x => g (spaceTimeCoordinates k x)
    ∃ N : Fin (k+1) → ClosedTime T → Ω → ℝ,
      (∀ i,LocalMProcessWitness P F (N i)) ∧
      (∀ i,ItoCovarianceFormula P F (M i)
        (fun z => fderiv ℝ f (fun j => XX j (realTimeClamp z.2) z.1) (Pi.single i 1)) (N i)) ∧
      (fun w => g ((fun i => X i (realTimeClamp b) w),b)) =ᵐ[P]
        fun w => g ((fun i => X i (realTimeClamp a) w),a)+
          ∑ i : Fin (k+1),(N i (realTimeClamp b) w-N i (realTimeClamp a) w) := by
  classical
  dsimp only
  let X : Fin k → ClosedTime T → Ω → ℝ := fun i t w => W (index i) (min (realTimeClamp (τ i)) t) w
  let C : Fin k → Fin k → ClosedTime T → Ω → ℝ := fun i j t w => if index i=index j then A (min (min (realTimeClamp (τ i)) (realTimeClamp (τ j))) t) w else 0
  have hct n : realTimeClamp (T := T) (c n)<⊤ := by
    change (realTimeClamp (c n):EReal)<T
    rw [real_time_clamp_eq _ (hc n) (hcT n).le]
    exact hcT n
  obtain ⟨hX,hCX,hCG⟩ := stopped_brownian_observation_family P F hF hle hnull W A hW hC hclock
    (fun n => realTimeClamp (c n)) (real_time_clamp_mono.comp hcm) hct hcc index τ hτ hτT
  change (∀ i,LocalMProcessWitness P F (X i)) at hX
  change (∀ i j,LocalCovarianceWitness P F (X i) (X j) (C i j)) at hCX
  have hsemi i := local_martingale_semimartingale_decomposition P hT F hF (X i) (hX i)
  have hb : 0≤b := ha.trans hab
  let K : ClosedTime T → Ω → ℝ := fun t (_ : Ω) => (finitePrefixTime (T := T) b hb t).val
  let XX : Fin (k+1) → ClosedTime T → Ω → ℝ := Fin.cons K X
  let AA : Fin (k+1) → ClosedTime T → Ω → ℝ := Fin.cons K (fun _ : Fin k => fun _ : ClosedTime T => fun _ : Ω => (0:ℝ))
  let M : Fin (k+1) → ClosedTime T → Ω → ℝ := Fin.cons (fun _ : ClosedTime T => fun _ : Ω => (0:ℝ)) X
  let CC : Fin (k+1) → Fin (k+1) → ClosedTime T → Ω → ℝ := fun i j => Fin.cases (fun _ => (fun _ _ => (0:ℝ)))
    (fun l => Fin.cases (fun _ _ => (0:ℝ)) (C l)) i j
  obtain ⟨hXX,hCC⟩ := clock_augmented_family P hT F hF X (fun _ _ _ => 0) X C hsemi hCX b hb
  let B : Fin (k+1) → Ω × ℝ → ℝ := fun i (z : Ω × ℝ) => (Fin.cons ((Iio b).indicator (fun _ => (1:ℝ)) z.2) (fun _ : Fin k => 0) : Fin (k+1) → ℝ) i
  let G0 : Fin k → Fin k → Ω × ℝ → ℝ := fun i j (z : Ω × ℝ) => if index i=index j then (Iio (min (τ i) (τ j))).indicator (fun _ => (1:ℝ)) z.2 else 0
  let G : Fin (k+1) → Fin (k+1) → Ω × ℝ → ℝ := fun i j (z : Ω × ℝ) =>
    (Fin.cases (motive := fun _ => Fin (k+1) → ℝ) (fun _ => (0:ℝ)) (fun l => Fin.cases (0:ℝ) (fun h => G0 l h z)) i) j
  have hBm i w : Measurable (fun r => B i (w,r)) := by
    refine Fin.cases ?_ (fun _ => ?_) i
    · exact measurable_const.indicator measurableSet_Iio
    · exact measurable_const
  have hBi i n : ∀ᵐ w ∂P,IntervalIntegrable (fun r => B i (w,r)) volume 0 (c n) := by
    apply ae_of_all
    intro w
    refine Fin.cases ?_ (fun _ => ?_) i
    · exact clipped_clock_density_integrable b (c n)
    · exact intervalIntegrable_const
  have hGm i j w : Measurable (fun r => G i j (w,r)) := by
    refine Fin.cases measurable_const (fun l => ?_) i
    refine Fin.cases measurable_const (fun h => ?_) j
    by_cases he : index l=index h <;> simp only [G,G0,Fin.cases_succ,he,ite_true,ite_false]
    · exact measurable_const.indicator measurableSet_Iio
    · exact measurable_const
  have hGi i j n : ∀ᵐ w ∂P,IntervalIntegrable (fun r => G i j (w,r)) volume 0 (c n) := by
    apply ae_of_all
    intro w
    refine Fin.cases intervalIntegrable_const (fun l => ?_) i
    refine Fin.cases intervalIntegrable_const (fun h => ?_) j
    by_cases he : index l=index h <;> simp only [G,G0,Fin.cases_succ,he,ite_true,ite_false]
    · exact clipped_clock_density_integrable _ _
    · exact intervalIntegrable_const
  have hAB i n : ∀ᵐ w ∂P,∀ r∈Icc 0 (c n),AA i (realTimeClamp r) w=AA i ⊥ w+∫ s in 0..r,B i (w,s) := by
    apply ae_of_all
    intro w r hr
    refine Fin.cases ?_ (fun _ => ?_) i
    · change (finitePrefixTime b hb (realTimeClamp r)).val=(finitePrefixTime b hb ⊥).val+_
      rw [clipped_clock_time_density b hb r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))]
      simp [finitePrefixTime,B,min_eq_left (show (0:EReal)≤(b:EReal) by exact_mod_cast hb)]
    · simp [AA,B]
  have hCG' i j n : ∀ᵐ w ∂P,∀ r∈Icc 0 (c n),CC i j (realTimeClamp r) w=∫ s in 0..r,G i j (w,s) := by
    apply ae_of_all
    intro w r hr
    refine Fin.cases ?_ (fun l => ?_) i
    · simp [CC,G]
    · refine Fin.cases ?_ (fun h => ?_) j
      · simp [CC,G]
      · exact hCG l h w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))
  have hf : ContDiff ℝ 2 (fun x => g (spaceTimeCoordinates k x)) := hg.comp (spaceTimeCoordinates k).contDiff
  have hk r (hr : r∈Icc a b) w : XX 0 (realTimeClamp r) w=r := by
    change (finitePrefixTime b hb (realTimeClamp r)).val=r
    rw [clipped_clock_time_density b hb r (ha.trans hr.1) ((EReal.coe_le_coe hr.2).trans_lt hbT),
      clipped_clock_density_integral b r hb (ha.trans hr.1),min_eq_right hr.2]
  have hz w r (hr : r∈Icc a b) := stopped_observation_generator_zero index active τ a b r hab hr hpast hcurrent
    g hg hzero (fun j => XX j (realTimeClamp r) w) (hk r hr w)
  have hGram i j z : G i j z=∑ l : Fin d,
      (Fin.cons 0 (fun h : Fin k => if z.2<τ h ∧ index h=l then (1:ℝ) else 0) : Fin (k+1) → ℝ) i*
      (Fin.cons 0 (fun h : Fin k => if z.2<τ h ∧ index h=l then (1:ℝ) else 0) : Fin (k+1) → ℝ) j := by
    rw [augmented_noise_gram]
    refine Fin.cases rfl (fun l => ?_) i
    refine Fin.cases rfl (fun h => ?_) j
    exact stopped_covariance_density_gram index τ z.2 l h
  obtain ⟨N,hN,hNI,he⟩ := multivariate_zero_generator_increment P hT F hF hle hnull XX AA M CC hXX hCC
    (fun x => g (spaceTimeCoordinates k x)) hf c hc hcm hcT hcc B G hBm hBi hAB hGm hGi hCG'
    a b ha hab hbT (by intro w r hr; simp_rw [hGram]; exact hz w r hr)
  refine ⟨N,hN,hNI,?_⟩
  filter_upwards [he] with w hw
  have hvec r : (fun j => XX j (realTimeClamp r) w)=Fin.cons (XX 0 (realTimeClamp r) w)
      (fun i => X i (realTimeClamp r) w) := by ext j; exact Fin.cases rfl (fun _ => rfl) j
  simpa only [hvec,spaceTimeCoordinates_cons,hk b ⟨hab,le_rfl⟩ w,hk a ⟨le_rfl,hab⟩ w] using hw

end Asakura.Chapter5
