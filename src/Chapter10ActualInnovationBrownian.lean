import Chapter10ActualInnovationCovariation

open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter9
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- Apply the previously proved vector Levy theorem to the actual innovation
and its actual covariation in completed innovation information. -/
theorem actual_innovation_brownian_characteristic {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d r n : ℕ} (B : BrownianSystem P n)
    (F : ℝ → Matrix (Fin d) (Fin d) ℝ) (L : ℝ → Matrix (Fin r) (Fin d) ℝ)
    (hF : Continuous F) (hL : Continuous L)
    (E : Fin (d+r) → Fin n → ℝ → ℝ) (hE : ∀ i j,Continuous (E i j))
    (ξ : Ω → Fin (d+r) → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξg : HasGaussianLaw ξ P)
    (hξ0 : ∫ w,ξ w ∂P=0)
    (T : ℝ) (hT : 0<T) [Fact (0≤(T:EReal))] (N : Fin (d+r) → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin (d+r) → ℝ))
    (h : LinearStateWitness P B
      (fun t => matrixOperatorMap (finiteBlocks (F t) 0 (L t) (0 : Matrix (Fin r) (Fin r) ℝ))) E ξ T hT.le N X)
    (hind : ∀ t : Icc (0:ℝ) T,IndepFun (fun w i => X w t (headIndex i))
      (fun w (z : {u : Icc (0:ℝ) T // u.val≤t.val} × Fin r) => X w z.1.val (tailIndex z.2)) P)
    (hξI : ∀ j,(fun w => ξ w (tailIndex j))=ᵐ[P] 0)
    (hclock : ∀ u i j,(∑ k,E (tailIndex i) k u*E (tailIndex j) k u)=if i=j then 1 else 0)
    (R s : ℝ) (hR : 0≤R) (hRT : R<T) (hs : s∈Icc 0 R) (v : Fin r → ℝ) :
    P[(fun w => Complex.exp (((∑ i,v i*(X w (projIcc 0 T hT.le R) (tailIndex i)-
      X w (projIcc 0 T hT.le s) (tailIndex i))):ℝ)*Complex.I))|
      nullAugmentedInformation (m := m) P (pathInformation T X tailIndex (projIcc 0 T hT.le s))]=ᵐ[P]
      fun _ => Complex.exp (-((R-s:ℝ):ℂ)*((∑ i,(v i)^2:ℝ):ℂ)/2) := by
  letI : MeasurableSpace Ω := m
  let ρ := finitePrefixTime (T := (T:EReal)) T hT.le
  let H := fun s => nullAugmentedInformation (m := m) P (pathInformation T X tailIndex s)
  letI : MeasurableSpace Ω := m
  have hHm : Monotone H := fun s t hst =>
    null_augmented_mono P _ _ (path_information_mono T X tailIndex s t hst)
  have hHl u : H u≤m := (h.path_information_le P B _ E ξ T hT.le N X tailIndex u).trans (B.le _)
  have hnull u Q (hQ : MeasurableSet[m] Q) (hPQ : P Q=0) : MeasurableSet[H u] Q :=
    MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨hQ,hPQ⟩)
  obtain ⟨hI,hC⟩ := actual_innovation_covariation P B F L hF hL E hE ξ hξ hξg hξ0
    T hT N X h hind hξI hclock
  have hTe : (0:EReal)<T := by exact_mod_cast hT
  have hRTe : (R:EReal)<T := by exact_mod_cast hRT
  have hreal u (hu : u∈Icc (0:ℝ) T) : ρ (realTimeClamp u)=projIcc 0 T hT.le u := by
    apply Subtype.ext
    rw [finite_prefix_time_of_real T u hT.le hu le_rfl]
    simp [projIcc,hu.1,hu.2]
  have hc (i j : Fin r) (w : Ω) (u : ℝ) (hu : 0≤u) (huT : (u:EReal)<T) :
      (if i=j then (ρ (realTimeClamp u)).val else 0)=(if i=j then u else 0) := by
    have hut : u<T := by exact_mod_cast huT
    rw [finite_prefix_time_of_real T u hT.le ⟨hu,hut.le⟩ le_rfl]
  have hh := vector_levy_conditional_characteristic P hTe (fun t => H (ρ t))
    (hHm.comp (finite_prefix_time_mono T hT.le)) (fun t => hHl _) (fun t => hnull _)
    (fun i t w => X w (ρ t) (tailIndex i)) (fun i j t (_ : Ω) => if i=j then (ρ t).val else 0)
    hI hC hc R hR hRTe s hs v
  simpa only [hreal R ⟨hR,hRT.le⟩,hreal s ⟨hs.1,hs.2.trans hRT.le⟩,H] using hh

end Asakura.Chapter10
