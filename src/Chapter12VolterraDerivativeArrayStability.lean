import Chapter12PathRemainderContinuity
import Chapter12ArrayVolterraStability
import Chapter12RemainderHilbertStability
import Chapter12HigherDerivativeLipschitz

open MeasureTheory Set
open scoped Topology ContDiff NNReal BigOperators
namespace Asakura.Chapter12
universe u
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem volterra_derivative_array_stability {E G : Type u} {N : Type*} [Fintype N]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (T : ℝ) (hT : 0≤T)
    (Q Q' X Y : G → C(Icc (0:ℝ) T,E))
    (hQ : ContDiff ℝ ∞ Q) (hQ' : ContDiff ℝ ∞ Q') (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y)
    (heX : ∀z t,X z t=Q z t+∫s in 0..t.val,b (X z (projIcc 0 T hT s)))
    (heY : ∀z t,Y z t=Q' z t+∫s in 0..t.val,b (Y z (projIcc 0 T hT s)))
    (n : ℕ) (z : G) (e : N → G)
    (D C J : ℕ → ℝ) (hD : ∀j,0≤D j) (hC : ∀j,0≤C j) (hJ : ∀j,0≤J j)
    (hbD : ∀j,1≤j → ∀x,‖iteratedFDeriv ℝ j b x‖≤D j)
    (B ε : ℝ) (hB : 0≤B) (hε : 0≤ε)
    (hXY : ∀t,‖X z t-Y z t‖≤ε)
    (hQD : ∀t,Real.sqrt (∑a : Fin (n+1) → N,
      ‖(iteratedFDeriv ℝ (n+1) Q z (e ∘ a)) t-(iteratedFDeriv ℝ (n+1) Q' z (e ∘ a)) t‖^2)≤B*ε)
    (hXC : ∀j,0<j → j<n+1 → ∀t,Real.sqrt (∑a : Fin j → N,‖(iteratedFDeriv ℝ j X z (e ∘ a)) t‖^2)≤C j)
    (hYC : ∀j,0<j → j≤n+1 → ∀t,Real.sqrt (∑a : Fin j → N,‖(iteratedFDeriv ℝ j Y z (e ∘ a)) t‖^2)≤C j)
    (hJD : ∀j,0<j → j<n+1 → ∀t,Real.sqrt (∑a : Fin j → N,
      ‖(iteratedFDeriv ℝ j X z (e ∘ a)) t-(iteratedFDeriv ℝ j Y z (e ∘ a)) t‖^2)≤J j*ε) :
    ∀t,Real.sqrt (∑a : Fin (n+1) → N,
      ‖(iteratedFDeriv ℝ (n+1) X z (e ∘ a)) t-(iteratedFDeriv ℝ (n+1) Y z (e ∘ a)) t‖^2)≤
      ε*(B+T*(D 2*C (n+1)+∑c : OrderedFinpartition (n+1) with 2≤c.length,
        (D (c.length+1)*(∏i,C (c.partSize i))+
          ∑i,D c.length*(J (c.partSize i)*∏j∈Finset.univ.erase i,C (c.partSize j)))))*Real.exp ((D 1+1)*T) := by
  classical
  let p := projIcc 0 T hT
  let U := fun (Z : G → C(Icc (0:ℝ) T,E)) t (a : Fin (n+1) → N) =>
    (iteratedFDeriv ℝ (n+1) Z z (e ∘ a)) (p t)
  let A := fun (Z : G → C(Icc (0:ℝ) T,E)) t => fderiv ℝ b (Z z (p t))
  let R := fun (Z : G → C(Icc (0:ℝ) T,E)) t (a : Fin (n+1) → N) =>
    higherChainRemainder (fun y => Z y (p t)) b (n+1) z (e ∘ a)
  let K := ∑c : OrderedFinpartition (n+1) with 2≤c.length,
    (D (c.length+1)*(∏i,C (c.partSize i))+
      ∑i,D c.length*(J (c.partSize i)*∏j∈Finset.univ.erase i,C (c.partSize j)))
  have hK : 0≤K := Finset.sum_nonneg (fun c _ => add_nonneg
    (mul_nonneg (hD _) (Finset.prod_nonneg (fun i _ => hC _)))
    (Finset.sum_nonneg (fun i _ => mul_nonneg (hD _) (mul_nonneg (hJ _) (Finset.prod_nonneg (fun j _ => hC _))))))
  have hcU Z a : Continuous (fun t => U Z t a) := (iteratedFDeriv ℝ (n+1) Z z (e ∘ a)).continuous.comp continuous_projIcc
  have hcA Z : Continuous (A Z) := (hb.continuous_fderiv (by simp)).comp ((Z z).continuous.comp continuous_projIcc)
  have hcRX a : Continuous (fun t => R X t a) := (path_remainder_continuous b hb hbound X hX n z (e ∘ a)).comp continuous_projIcc
  have hcRY a : Continuous (fun t => R Y t a) := (path_remainder_continuous b hb hbound Y hY n z (e ∘ a)).comp continuous_projIcc
  have hAb t : ‖A X t‖≤D 1 := by simpa only [norm_iteratedFDeriv_one] using hbD 1 le_rfl (X z (p t))
  have hAB t : ‖A X t-A Y t‖≤D 2*ε := by
    have hl := bounded_second_derivative_lipschitz b hb ⟨D 2,hD 2⟩ (hbD 2 (by omega))
    have hh := hl.norm_sub_le (X z (p t)) (Y z (p t))
    change ‖A X t-A Y t‖≤D 2*‖X z (p t)-Y z (p t)‖ at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hXY _) (hD 2))
  have hRb t : Real.sqrt (∑a,‖R X t a-R Y t a‖^2)≤K*ε := by
    have hh := remainder_hilbert_stability (fun y => X y (p t)) (fun y => Y y (p t)) b (n+1) z e
      (fun j => D (j+1)) D C J (fun j => hD _) hD hC hJ ε hε
      (fun j hj _ => hbD j (by omega) _)
      (fun j hj _ => ?_)
      (fun j hj hlt => ?_) (fun j hj hlt => ?_) (fun j hj hlt => ?_)
    · simpa only [R,K,mul_comm] using hh
    · have hl := bounded_next_derivative_lipschitz b hb j ⟨D (j+1),hD _⟩ (hbD (j+1) (by omega))
      have hh := hl.norm_sub_le (X z (p t)) (Y z (p t))
      change _≤D (j+1)*‖X z (p t)-Y z (p t)‖ at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (hXY _) (hD _))
    · simpa only [path_derivative_evaluation X hX] using hXC j hj hlt (p t)
    · simpa only [path_derivative_evaluation Y hY] using hYC j hj hlt.le (p t)
    · simpa only [path_derivative_evaluation X hX,path_derivative_evaluation Y hY] using hJD j hj hlt (p t)
  have hEq (Z QZ : G → C(Icc (0:ℝ) T,E)) (hZ : ContDiff ℝ ∞ Z) (hQZ : ContDiff ℝ ∞ QZ)
      (heZ : ∀y s,Z y s=QZ y s+∫r in 0..s.val,b (Z y (projIcc 0 T hT r))) t (ht : t∈Icc 0 T) a :
      U Z t a=U QZ t a+∫s in 0..t,A Z s (U Z s a)+R Z s a := by
    have hh := volterra_parameter_variations b hb hbound T hT QZ Z hQZ hZ heZ n z (e ∘ a) (p t)
    have hpt : (p t).val=t := congrArg Subtype.val (projIcc_of_mem hT ht)
    rw [hpt] at hh
    exact hh
  have hh := array_volterra_stability (U X) (U Y) (U Q) (U Q') (R X) (R Y) (A X) (A Y)
    (hcU X) (hcU Y) hcRX hcRY (hcA X) (hcA Y) T (D 1) (B*ε) (D 2*ε) (K*ε) (C (n+1))
    hT (hD 1) (mul_nonneg hB hε) (mul_nonneg (hD 2) hε) (mul_nonneg hK hε) (hC _)
    (fun t _ => hAb t) (fun t _ => hAB t) (fun t _ => hQD (p t)) (fun t _ => hRb t)
    (fun t _ => hYC (n+1) (by omega) le_rfl (p t)) (hEq X Q hX hQ heX) (hEq Y Q' hY hQ' heY)
  intro t
  have hpt : p t.val=t := projIcc_of_mem hT t.property
  have ht := hh t.val t.property
  simp only [U,hpt] at ht
  convert ht using 1 <;> dsimp only [K] <;> ring
end Asakura.Chapter12
#print axioms Asakura.Chapter12.volterra_derivative_array_stability
