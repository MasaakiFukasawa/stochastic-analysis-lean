import Chapter12ArrayVolterraBound
import Chapter12VolterraVariations
import Chapter12RemainderHilbertArray

open MeasureTheory Set
open scoped Topology ContDiff NNReal BigOperators
namespace Asakura.Chapter12
universe u
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem volterra_derivative_array_bound {E G : Type u} {N : Type*} [Fintype N]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (T : ℝ) (hT : 0≤T)
    (Q X : G → C(Icc (0:ℝ) T,E)) (hQ : ContDiff ℝ ∞ Q) (hX : ContDiff ℝ ∞ X)
    (heq : ∀z t,X z t=Q z t+∫s in 0..t.val,b (X z (projIcc 0 T hT s)))
    (n : ℕ) (z : G) (e : N → G) (L B : ℝ) (hL : 0≤L) (hB : 0≤B)
    (hDb : ∀x,‖fderiv ℝ b x‖≤L)
    (D C : ℕ → ℝ) (hD : ∀j,0≤D j) (hC : ∀j,0≤C j)
    (hbD : ∀j,2≤j → j≤n+1 → ∀x,‖iteratedFDeriv ℝ j b x‖≤D j)
    (hQB : ∀t,Real.sqrt (∑a : Fin (n+1) → N,‖(iteratedFDeriv ℝ (n+1) Q z (e ∘ a)) t‖^2)≤B)
    (hXC : ∀j,0<j → j<n+1 → ∀t,Real.sqrt (∑a : Fin j → N,‖(iteratedFDeriv ℝ j X z (e ∘ a)) t‖^2)≤C j) :
    ∀t,Real.sqrt (∑a : Fin (n+1) → N,‖(iteratedFDeriv ℝ (n+1) X z (e ∘ a)) t‖^2)≤
      (B+T*(∑c : OrderedFinpartition (n+1) with 2≤c.length,D c.length*∏i,C (c.partSize i)))*Real.exp ((L+1)*T) := by
  classical
  let p := projIcc 0 T hT
  let U := fun t (a : Fin (n+1) → N) => (iteratedFDeriv ℝ (n+1) X z (e ∘ a)) (p t)
  let V := fun t (a : Fin (n+1) → N) => (iteratedFDeriv ℝ (n+1) Q z (e ∘ a)) (p t)
  let A := fun t => fderiv ℝ b (X z (p t))
  let S := continuousMapSuperposition (K:=Icc (0:ℝ) T) b hb.continuous
  have hS : ContDiff ℝ ∞ S := continuousMap_superposition_smooth b hb hbound
  let R := fun t (a : Fin (n+1) → N) =>
    (iteratedFDeriv ℝ (n+1) (S ∘ X) z (e ∘ a)) (p t)-A t (U t a)
  have hcu a : Continuous (fun t => U t a) :=
    (iteratedFDeriv ℝ (n+1) X z (e ∘ a)).continuous.comp continuous_projIcc
  have hcA : Continuous A :=
    (hb.continuous_fderiv (by simp)).comp ((X z).continuous.comp continuous_projIcc)
  have hcR a : Continuous (fun t => R t a) :=
    ((iteratedFDeriv ℝ (n+1) (S ∘ X) z (e ∘ a)).continuous.comp continuous_projIcc).sub (hcA.clm_apply (hcu a))
  have heval j a t : iteratedFDeriv ℝ j (fun y => X y (p t)) z (e ∘ a)=
      (iteratedFDeriv ℝ j X z (e ∘ a)) (p t) := by
    let ev : C(Icc (0:ℝ) T,E) →L[ℝ] E := ContinuousMap.evalCLM ℝ (p t)
    exact congrArg (fun D => D (e ∘ a)) (ev.iteratedFDeriv_comp_left hX.contDiffAt (by simp))
  have hRformula t a : R t a=higherChainRemainder (fun y => X y (p t)) b (n+1) z (e ∘ a) := by
    dsimp only [R,S]
    rw [path_composition_derivative b hb.continuous X (hS.comp hX)]
    let ev : C(Icc (0:ℝ) T,E) →L[ℝ] E := ContinuousMap.evalCLM ℝ (p t)
    have hXt : ContDiff ℝ ∞ (fun y => X y (p t)) := ev.contDiff.comp hX
    rw [higher_chain_linear_split _ b hXt hb,heval]
    exact add_sub_cancel_left _ _
  let K := ∑c : OrderedFinpartition (n+1) with 2≤c.length,D c.length*∏i,C (c.partSize i)
  have hK : 0≤K := Finset.sum_nonneg (fun c _ => mul_nonneg (hD _) (Finset.prod_nonneg (fun i _ => hC _)))
  have hRb t : Real.sqrt (∑a,‖R t a‖^2)≤K := by
    simp_rw [hRformula]
    apply remainder_hilbert_array_bound _ b (n+1) z e D C hD hC (fun j hj hlt => hbD j hj hlt _)
    intro j hj hlt
    simpa only [heval] using hXC j hj hlt (p t)
  have hEq t (ht : t∈Icc 0 T) a : U t a=V t a+∫s in 0..t,A s (U s a)+R s a := by
    have hh := volterra_parameter_variations b hb hbound T hT Q X hQ hX heq n z (e ∘ a) (p t)
    have hpt : (p t).val=t := congrArg Subtype.val (projIcc_of_mem hT ht)
    rw [hpt] at hh
    simpa only [U,V,A,hRformula,p] using hh
  have hh := array_volterra_bound U V R A hcu hcR hcA T L B K hT hL hB hK
    (fun t _ => hDb _) (fun t _ => hQB (p t)) (fun t _ => hRb t) hEq
  intro t
  have hpt : p t.val=t := projIcc_of_mem hT t.property
  simpa only [U,hpt,K] using hh t.val t.property
end Asakura.Chapter12
#print axioms Asakura.Chapter12.volterra_derivative_array_bound
