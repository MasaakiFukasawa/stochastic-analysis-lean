import Chapter4FiniteCovarianceSum
import Chapter4LevyConstructed

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The multivariate characteristic-function exercise, obtained from the
actual covariance of each normalized scalar projection and scalar Ito. -/
theorem vector_levy_conditional_characteristic
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W : Fin dim → ClosedTime T → Ω → ℝ)
    (C : Fin dim → Fin dim → ClosedTime T → Ω → ℝ)
    (hW : ∀ i,LocalMProcessWitness P F (W i))
    (hC : ∀ i j,LocalCovarianceWitness P F (W i) (W j) (C i j))
    (hclock : ∀ i j w (r : ℝ),0≤r → (r:EReal)<T → C i j (realTimeClamp r) w=if i=j then r else 0)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) (s : ℝ) (hs : s∈Icc 0 R) (u : Fin dim → ℝ) :
    P[(fun w => Complex.exp (((∑ i,u i*(W i (realTimeClamp R) w-W i (realTimeClamp s) w)):ℝ)*Complex.I)) |
      F (realTimeClamp s)] =ᵐ[P] fun _ => Complex.exp (-((R-s:ℝ):ℂ)*((∑ i,(u i)^2:ℝ):ℂ)/2) := by
  classical
  let q := ∑ i,(u i)^2
  have hq : 0≤q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hz : q=0
  · have hu i : u i=0 := by
      have hh : (u i)^2≤q := Finset.single_le_sum (f := fun i => (u i)^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      rw [hz] at hh
      exact sq_eq_zero_iff.mp (le_antisymm hh (sq_nonneg _))
    simp only [hu,zero_mul,Finset.sum_const_zero,Complex.ofReal_zero,mul_zero,Complex.exp_zero,zero_pow (by decide : (2:ℕ)≠0),neg_mul,zero_div]
    simp only [condExp_const (hle _) (1:ℂ)]
    exact Filter.Eventually.of_forall (fun _ => rfl)
  · let ρ := Real.sqrt q
    have hρ : 0<ρ := Real.sqrt_pos.2 (lt_of_le_of_ne hq (Ne.symm hz))
    have hρsq : ρ^2=q := Real.sq_sqrt hq
    let v := fun i => u i/ρ
    have hv : (∑ i,(v i)^2)=1 := by
      simp only [v,div_pow,← Finset.sum_div]
      change q/ρ^2=1
      rw [← hρsq,div_self (pow_ne_zero _ hρ.ne')]
    let X := fun t w => ∑ i,v i*W i t w
    let A := fun t w => ∑ j,v j*(∑ i,v i*C i j t w)
    have hX : LocalMProcessWitness P F X := local_martingale_finset_sum P hT F hF hle Finset.univ
      (fun i t w => v i*W i t w) (fun i _ => (hW i).smul P F (v i))
    have hA : LocalCovarianceWitness P F X X A := weighted_covariance_sum P hT F hF hle W C v v hC
    have hAt w (r : ℝ) (hr : 0≤r) (hrT : (r:EReal)<T) : A (realTimeClamp r) w=r := by
      dsimp only [A]
      simp_rw [hclock _ _ w r hr hrT,mul_ite,mul_zero]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
      calc
        (∑ j,v j*(v j*r)) = (∑ j,(v j)^2)*r := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring
        _ = r := by rw [hv,one_mul]
    have he w : ρ*(X (realTimeClamp R) w-X (realTimeClamp s) w)=
        ∑ i,u i*(W i (realTimeClamp R) w-W i (realTimeClamp s) w) := by
      dsimp only [X]
      rw [← Finset.sum_sub_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [v]
      field_simp
      <;> ring
    have hh := levy_conditional_characteristic_constructed P hT F hF hle hnull X A hX hA hAt R hR hRT s hs ρ
    have hl : (fun w => Complex.exp ((ρ:ℂ)*((X (realTimeClamp R) w-X (realTimeClamp s) w):ℂ)*Complex.I))=
        (fun w => Complex.exp (((∑ i,u i*(W i (realTimeClamp R) w-W i (realTimeClamp s) w)):ℝ)*Complex.I)) := by
      funext w
      rw [← Complex.ofReal_sub,← Complex.ofReal_mul,he w]
    rw [hl] at hh
    simpa only [← Complex.ofReal_pow,hρsq,q] using hh

end Asakura.Chapter4
