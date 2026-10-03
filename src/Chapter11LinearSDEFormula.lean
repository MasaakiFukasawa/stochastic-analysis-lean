import Chapter11InverseFactorConstruction
import Chapter11InverseFactor

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Every solution, without a positivity assumption, equals the stochastic
 exponential. The positive integrating factor is constructed, not assumed. -/
theorem linear_sde_exponential_formula
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (D Q K : ClosedTime T → Ω → ℝ)
    (hD : LocalMProcessWitness P F D) (hQ : LocalCovarianceWitness P F D D Q)
    (hK : AdaptedLocalVariationWitness F K)
    (hKc : ∀ w t,t<⊤ → ContinuousAt (fun s => K s w) t)
    (X A M : ClosedTime T → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X A M)
    (hMI : ItoCovarianceFormula P F D (fun z => X (realTimeClamp z.2) z.1) M)
    (hK0 : K ⊥=ᵐ[P] fun _ => 0)
    (c : ℕ → ℝ) (hc : ∀ n,0<c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n))
    (b q : Ω × ℝ → ℝ) (hbm : ∀ w,Measurable (fun r => b (w,r)))
    (hqm : ∀ w,Measurable (fun r => q (w,r)))
    (hbi : ∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => b (w,r)) volume 0 (c n))
    (hqi : ∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => q (w,r)) volume 0 (c n))
    (hKe : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),K (realTimeClamp r) w=K ⊥ w+∫ s in 0..r,b (w,s))
    (hQe : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),Q (realTimeClamp r) w=∫ s in 0..r,q (w,s))
    (hAe : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),A (realTimeClamp r) w=A ⊥ w+
      ∫ s in 0..r,X (realTimeClamp s) w*b (w,s)) :
    ∀ r : ℝ,0≤r → (r:EReal)<T → X (realTimeClamp r)=ᵐ[P]
      fun w => X ⊥ w*Real.exp (K (realTimeClamp r) w-Q (realTimeClamp r) w/2+D (realTimeClamp r) w) := by
  obtain ⟨Y,B,N,hY,hNI,hYe,hYpos,hBe⟩ := inverse_factor_constructed P hT F hF hle hnull
    D Q K hD hQ hK hKc c hc hcm hcT hcc b q hbm hqm hbi hqi hKe hQe
  have hp := inverse_factor_product_constant P hT F hF hle hnull D Q X Y A B M N hD hQ hX hY
    hMI hNI c (fun n => (hc n).le) hcm hcT hcc b q hbm hqm hbi hqi hQe hAe hBe
  have hY0 : Y ⊥=ᵐ[P] fun _ => 1 := by
    filter_upwards [hD.initial P F,hQ.defect.initial P F,hK0] with w hd hq hk
    change D ⊥ w*D ⊥ w-Q ⊥ w=0 at hq
    have hd' : D ⊥ w=0 := hd
    have hq' : Q ⊥ w=0 := by rw [hd'] at hq;linarith
    simp only [hYe,hk,hq',hd',neg_zero,zero_div,add_zero,sub_zero,Real.exp_zero]
  intro r hr hrT
  filter_upwards [hp r hr hrT,hY0] with w hpw h0
  apply mul_right_cancel₀ (ne_of_gt (hYpos _ w))
  rw [hpw,h0,mul_one,hYe]
  have he : Real.exp (K (realTimeClamp r) w-Q (realTimeClamp r) w/2+D (realTimeClamp r) w)*
      Real.exp (-K (realTimeClamp r) w+Q (realTimeClamp r) w/2-D (realTimeClamp r) w)=1 := by
    rw [←Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  rw [mul_assoc,he,mul_one]

end Asakura.Chapter11
