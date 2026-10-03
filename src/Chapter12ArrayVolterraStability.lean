import Chapter12ArrayVolterraBound

open MeasureTheory Set
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem array_volterra_stability {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (U V Q Q' R S : ℝ → I → E) (A B : ℝ → E →L[ℝ] E)
    (hU : ∀i,Continuous (fun t => U t i)) (hV : ∀i,Continuous (fun t => V t i))
    (hR : ∀i,Continuous (fun t => R t i)) (hS : ∀i,Continuous (fun t => S t i))
    (hA : Continuous A) (hB : Continuous B)
    (T L dQ dA dR C : ℝ) (hT : 0≤T) (hL : 0≤L)
    (hdQ : 0≤dQ) (hdA : 0≤dA) (hdR : 0≤dR) (hC : 0≤C)
    (hAb : ∀t,t∈Icc 0 T → ‖A t‖≤L)
    (hAB : ∀t,t∈Icc 0 T → ‖A t-B t‖≤dA)
    (hQb : ∀t,t∈Icc 0 T → Real.sqrt (∑i,‖Q t i-Q' t i‖^2)≤dQ)
    (hRb : ∀t,t∈Icc 0 T → Real.sqrt (∑i,‖R t i-S t i‖^2)≤dR)
    (hVb : ∀t,t∈Icc 0 T → Real.sqrt (∑i,‖V t i‖^2)≤C)
    (heU : ∀t,t∈Icc 0 T → ∀i,U t i=Q t i+∫s in 0..t,A s (U s i)+R s i)
    (heV : ∀t,t∈Icc 0 T → ∀i,V t i=Q' t i+∫s in 0..t,B s (V s i)+S s i) :
    ∀t,t∈Icc 0 T → Real.sqrt (∑i,‖U t i-V t i‖^2)≤
      (dQ+T*(dA*C+dR))*Real.exp ((L+1)*T) := by
  let F := fun t i => (A t-B t) (V t i)+(R t i-S t i)
  have hF i : Continuous (fun t => F t i) := ((hA.sub hB).clm_apply (hV i)).add ((hR i).sub (hS i))
  have hFb t (ht : t∈Icc 0 T) : Real.sqrt (∑i,‖F t i‖^2)≤dA*C+dR := by
    exact (array_add_norm_bound (fun i => (A t-B t) (V t i)) (fun i => R t i-S t i)).trans
      (add_le_add ((array_linear_bound (A t-B t) (V t)).trans
        (mul_le_mul (hAB t ht) (hVb t ht) (Real.sqrt_nonneg _) hdA)) (hRb t ht))
  have he t (ht : t∈Icc 0 T) i : U t i-V t i=(Q t i-Q' t i)+
      ∫s in 0..t,A s (U s i-V s i)+F s i := by
    rw [heU t ht i,heV t ht i]
    rw [add_sub_add_comm]
    rw [←intervalIntegral.integral_sub (f:=fun s => A s (U s i)+R s i) (g:=fun s => B s (V s i)+S s i)
      (((hA.clm_apply (hU i)).add (hR i)).intervalIntegrable (μ:=volume) 0 t)
      (((hB.clm_apply (hV i)).add (hS i)).intervalIntegrable (μ:=volume) 0 t)]
    have hh : (fun s => A s (U s i)+R s i-(B s (V s i)+S s i))=
        fun s => A s (U s i-V s i)+F s i := by
      funext s
      simp only [F,map_sub,ContinuousLinearMap.sub_apply]
      abel
    rw [hh]
  exact array_volterra_bound (fun t i => U t i-V t i) (fun t i => Q t i-Q' t i) F A
    (fun i => (hU i).sub (hV i)) hF hA T L dQ (dA*C+dR) hT hL hdQ (by positivity)
    hAb hQb hFb he
end Asakura.Chapter12
#print axioms Asakura.Chapter12.array_volterra_stability
