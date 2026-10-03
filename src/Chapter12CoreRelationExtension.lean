import Chapter12BoundedRelationClosure

open Set
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- A finite core estimate constructs the output over the input completion;
the same closed relation identifies the limit. -/
theorem core_relation_extension {E F U Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (V : Submodule ℝ E) (A : Submodule ℝ F)
    (L : E →L[ℝ] U) (M : F →L[ℝ] Z)
    (G : Submodule ℝ (U×Z)) (hG : IsClosed (G : Set (U×Z)))
    (C : ℝ) (hC : 0≤C)
    (hex : ∀ x∈V,∃ y∈A,(L x,M y)∈G)
    (hb : ∀ x∈V,∀ y∈A,(L x,M y)∈G → ‖y‖≤C*‖x‖)
    (x : E) (hx : x∈V.topologicalClosure) :
    ∃ y : F,y∈A.topologicalClosure ∧ (L x,M y)∈G ∧ ‖y‖≤C*‖x‖ := by
  let K : E×F →L[ℝ] U×Z := L.prodMap M
  let R : Submodule ℝ (E×F) := (V.prod A) ⊓ G.comap K.toLinearMap
  have hR (a : E×F) : a∈R ↔ a.1∈V ∧ a.2∈A ∧ (L a.1,M a.2)∈G := by
    simp only [R,Submodule.mem_inf,Submodule.mem_prod,Submodule.mem_comap]
    tauto
  have hproj : (Prod.fst : E×F → E) '' (R : Set (E×F))=(V : Set E) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨a,ha,rfl⟩
      exact (hR a).mp ha |>.1
    · intro a ha
      obtain ⟨b,hb,hg⟩ := hex a ha
      exact ⟨(a,b),(hR _).mpr ⟨ha,hb,hg⟩,rfl⟩
  have hxR : x∈closure ((Prod.fst : E×F → E) '' (R : Set (E×F))) := by
    rw [hproj]
    exact hx
  obtain ⟨y,hy,hbound⟩ := bounded_relation_extends_closure R C hC
    (fun a ha => hb a.1 ((hR a).mp ha).1 a.2 ((hR a).mp ha).2.1 ((hR a).mp ha).2.2) x hxR
  have hAclosed : IsClosed {a : E×F | a.2∈A.topologicalClosure} :=
    A.isClosed_topologicalClosure.preimage continuous_snd
  have hGclosed : IsClosed {a : E×F | (L a.1,M a.2)∈G} := hG.preimage K.continuous
  have hincA : (R : Set (E×F)) ⊆ {a : E×F | a.2∈A.topologicalClosure} :=
    fun a ha => A.le_topologicalClosure ((hR a).mp ha).2.1
  have hyA : y∈A.topologicalClosure := (closure_minimal hincA hAclosed) hy
  have hyG : (L x,M y)∈G :=
    closure_minimal (fun a ha => ((hR a).mp ha).2.2) hGclosed hy
  exact ⟨y,hyA,hyG,hbound⟩

end Asakura.Chapter12
