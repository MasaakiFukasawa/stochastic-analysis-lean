import Chapter11ControlClock
import Chapter11GridEndpointConvention
import Chapter4FiniteStepDomain

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem real_two_clock_step_density
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (b : ℝ) (hb : 0<b) [Fact (0≤b)] (A B : Ω → ℝ → ℝ)
    (hA : ∀ w,MonotoneOn (A w) (Icc 0 b)) (hB : ∀ w,MonotoneOn (B w) (Icc 0 b))
    (hAc : ∀ w,ContinuousOn (A w) (Icc 0 b)) (hBc : ∀ w,ContinuousOn (B w) (Icc 0 b))
    (hAm : ∀ t,Measurable (fun w => A w t)) (hBm : ∀ t,Measurable (fun w => B w t))
    {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤‹MeasurableSpace Ω›)
    (hAa : ∀ t : Icc (0:ℝ) b,Measurable[F (realTimeClamp t.val)] (fun w => A w t.val))
    (hBa : ∀ t : Icc (0:ℝ) b,Measurable[F (realTimeClamp t.val)] (fun w => B w t.val))
    (hnull : ∀ t N,MeasurableSet N → P N=0 → MeasurableSet[F t] N)
    (H : Ω × ℝ → ℝ)
    (hH : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) b => F (realTimeClamp t.val))) inferInstance (fun z : Ω × Icc (0:ℝ) b => H (z.1,z.2.val))) :
    let α := fun w => (intervalStieltjes 0 b hb.le (A w) (hA w) (fun r hr => (hAc w r hr).mono inter_subset_left)).measure
    let β := fun w => (intervalStieltjes 0 b hb.le (B w) (hB w) (fun r hr => (hBc w r hr).mono inter_subset_left)).measure
    (∀ᵐ w ∂P,Integrable (fun r => (H (w,r))^2) (α w)) →
    (∀ᵐ w ∂P,Integrable (fun r => |H (w,r)|) (β w)) →
    ∃ (N : ℕ → ℕ) (u : ℕ → ℕ → ℝ) (V : ℕ → ℕ → Ω → ℝ),
      (∀ n,StrictMonoOn (u n) (Iic (N n))) ∧
      (∀ n i,u n i∈Icc 0 b) ∧
      (∀ n j,j<N n → Measurable[F (realTimeClamp (u n j))] (V n j) ∧ MemLp (V n j) ∞ P) ∧
      let J := fun n (z : Ω × ℝ) => ∑ j∈Finset.range (N n),(Ioc (u n j) (u n (j+1))).indicator (fun _ => V n j z.1) z.2
      (∀ n,Measurable (J n)) ∧
      (∀ n (d : ℝ),@Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) d => F (realTimeClamp t.val))) inferInstance (fun z : Ω × Icc (0:ℝ) d => J n (z.1,z.2.val))) ∧
      (∀ n,∀ᵐ w ∂P,Integrable (fun r => (J n (w,r)-H (w,r))^2) (α w)) ∧
      (∀ n,∀ᵐ w ∂P,Integrable (fun r => |J n (w,r)-H (w,r)|) (β w)) ∧
      (∀ ε>0,Tendsto (fun n => P {w | ε≤∫ r,(J n (w,r)-H (w,r))^2 ∂α w}) atTop (𝓝 0)) ∧
      (∀ ε>0,Tendsto (fun n => P {w | ε≤∫ r,|J n (w,r)-H (w,r)| ∂β w}) atTop (𝓝 0)) := by
  intro α β hiA hiB
  have hαs w : ∀ᵐ r ∂α w,r∈Icc 0 b := (interval_stieltjes_ae_mem_Ioc 0 b hb.le (A w) (hA w) _).mono (fun r hr => ⟨hr.1.le,hr.2⟩)
  have hβs w : ∀ᵐ r ∂β w,r∈Icc 0 b := (interval_stieltjes_ae_mem_Ioc 0 b hb.le (B w) (hB w) _).mono (fun r hr => ⟨hr.1.le,hr.2⟩)
  letI (w : Ω) : NullSingletonClass (α w) := interval_stieltjes_no_atoms_on 0 b hb.le (A w) (hA w) _ (hAc w)
  letI (w : Ω) : NullSingletonClass (β w) := interval_stieltjes_no_atoms_on 0 b hb.le (B w) (hB w) _ (hBc w)
  have hproj (ν : Measure ℝ) (hs : ∀ᵐ r ∂ν,r∈Icc 0 b) (w : Ω) :
      (fun r => H (w,(projIcc 0 b hb.le r).val))=ᵐ[ν] fun r => H (w,r) :=
    hs.mono (fun r hr => by dsimp only; rw [projIcc_of_mem hb.le hr])
  have hiA' : ∀ᵐ w ∂P,Integrable (fun r => (H (w,(projIcc 0 b hb.le r).val))^2) (α w) :=
    hiA.mono (fun w hw => hw.congr ((hproj (α w) (hαs w) w).fun_comp (fun x => x^2)).symm)
  have hiB' : ∀ᵐ w ∂P,Integrable (fun r => |H (w,(projIcc 0 b hb.le r).val)|) (β w) :=
    hiB.mono (fun w hw => hw.congr ((hproj (β w) (hβs w) w).fun_comp abs).symm)
  obtain ⟨N,u,V,hum,hVm,hJm,hJiA,hJiB,hpA,hpB⟩ := two_clock_step_density P b hb A B hA hB hAc hBc hAm hBm
    (fun t : Icc (0:ℝ) b => F (realTimeClamp t.val))
    (fun s t hst => hF (real_time_clamp_mono hst)) (fun t => hle _) hAa hBa (fun t => hnull _)
    (fun z : Ω × Icc (0:ℝ) b => H (z.1,z.2.val)) hH hiA' hiB'
  let v := fun n i => (u n i).val
  let J := fun n (z : Ω × ℝ) => ∑ i∈Finset.range (N n),(Ioc (v n i) (v n (i+1))).indicator (fun _ => V n i z.1) z.2
  let J0 := fun n (z : Ω × ℝ) => ∑ i∈Finset.range (N n),(Ico (u n i) (u n (i+1))).indicator (fun _ => V n i z.1) (projIcc 0 b hb.le z.2)
  have he (ν : Measure ℝ) [NullSingletonClass ν] (hs : ∀ᵐ r ∂ν,r∈Icc 0 b) (n : ℕ) (w : Ω) :
      (fun r => J0 n (w,r)-H (w,(projIcc 0 b hb.le r).val))=ᵐ[ν] fun r => J n (w,r)-H (w,r) := by
    exact (finite_grid_projection_Ioc_ae ν b hb.le hs (N n) (u n) (fun i => V n i w)).sub (hproj ν hs w)
  have hreg n := finite_step_integrand_domain F hF hle (Finset.range (N n)) (v n) (fun i => v n (i+1)) (V n)
    (fun i hi => (hVm n i (Finset.mem_range.mp hi)).1)
  refine ⟨N,v,V,(fun n i hi j hj hij => hum n hi hj hij),(fun n i => (u n i).property),hVm,(fun n => (hreg n).1),(fun n => (hreg n).2.1),?_,?_,?_,?_⟩
  · intro n
    exact (hJiA n).mono (fun w hw => hw.congr ((he (α w) (hαs w) n w).fun_comp (fun x => x^2)))
  · intro n
    exact (hJiB n).mono (fun w hw => hw.congr ((he (β w) (hβs w) n w).fun_comp abs))
  · intro ε hε
    have hh := hpA ε hε
    convert hh using 1
    ext n
    congr 1
    ext w
    exact congrArg (fun z : ℝ => ε≤z) (integral_congr_ae ((he (α w) (hαs w) n w).fun_comp (fun x => x^2))).symm |> Eq.to_iff
  · intro ε hε
    have hh := hpB ε hε
    convert hh using 1
    ext n
    congr 1
    ext w
    exact congrArg (fun z : ℝ => ε≤z) (integral_congr_ae ((he (β w) (hβs w) n w).fun_comp abs)).symm |> Eq.to_iff

end Asakura.Chapter11
