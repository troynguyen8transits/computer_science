import Downstream.ProviderTables
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

set_option autoImplicit false

/-! Exact weight/interaction semantics of the finite-input polynomial-time
provider. The proofs relate the concrete Boolean scans to the actual network.
-/

namespace CSPConsequence.TableRefinement

open Finset Groundwork DomainCodec FiniteInput ProviderParameters NodeRefinement ProviderTables

theorem all_range_fin (n : ℕ) (f : ℕ → Bool) :
    (List.range n).all f = true ↔ ∀ a : Fin n, f a.val = true := by
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h a
    exact h a.val a.isLt
  · intro h a ha
    exact h ⟨a,ha⟩

theorem relationBit_of {k D : ℕ} (I : Instance k D) (a v : Fin k) (x y : Fin D) :
    relationBit (tabulate I,a.val,v.val,x.val,y.val) =
      if I.edge a v then I.accepts a v x y else true := by
  by_cases hav : a < v <;>
    simp [relationBit, edgeAt_tabulate, relationAt_tabulate, Instance.accepts, hav]

theorem relationValue_of {k D : ℕ} (I : Instance k D) (a v : Fin k) (x y : Fin D) :
    BitNetwork.relationValue I a v x y =
      if relationBit (tabulate I,a.val,v.val,x.val,y.val) then (1 : ℤ) else 0 := by
  rw [relationBit_of]
  by_cases he : I.edge a v = true
  · simp [BitNetwork.relationValue, he]
  · simp [BitNetwork.relationValue, he]

variable {k D g : ℕ} (I : Instance k D) (b : ℕ) (hg : 0 < g) (hD : 0 < D)

theorem weightValue_of (G : Fin g) (w : List Bool) :
    weightValue (paramsOf I g b,G.val,w) =
      (BitNetwork.data I ⟨0,hD⟩ b (balanced hg)).W G w := by
  let χ := balanced (k := k) hg
  let x := decode ⟨0,hD⟩ b (EncodedSettings.members χ G) w
  have hv : vertexList (paramsOf I g b) = List.range k := by
    simp [vertexList, paramsOf, vertices_tabulate]
  have hc : groupCount (paramsOf I g b) = g := by simp [groupCount, paramsOf]
  have hbit : weightBit (paramsOf I g b,G.val,w) = true ↔
      ∀ p ∈ (pairs (Fin k)).filter (fun p => χ p.1 = G ∧ χ p.2 = G),
        relationBit (tabulate I,p.1.val,p.2.val,(x p.1).val,(x p.2).val) = true := by
    unfold weightBit
    simp only [hv, hc, all_range_fin]
    simp only [nodeValue_of I b hg hD G w, ite_eq_right_iff]
    simp [pairs, Prod.forall, χ, x, balanced, Fin.ext_iff, and_imp, paramsOf]
  rw [← BitNetwork.fastWeight_eq I ⟨0,hD⟩ b χ G w]
  unfold weightValue BitNetwork.fastWeight
  simp_rw [relationValue_of]
  rw [Finset.prod_boole]
  simp only [hbit]
  split_ifs <;> rfl

theorem interactionValue_of (G H : Fin g) (hne : G ≠ H) (w w' : List Bool) :
    interactionValue (paramsOf I g b,(G.val,H.val),(w,w')) =
      (BitNetwork.data I ⟨0,hD⟩ b (balanced hg)).Ψ G H w w' := by
  let χ := balanced (k := k) hg
  let x := decode ⟨0,hD⟩ b (EncodedSettings.members χ G) w
  let y := decode ⟨0,hD⟩ b (EncodedSettings.members χ H) w'
  have hv : vertexList (paramsOf I g b) = List.range k := by
    simp [vertexList, paramsOf, vertices_tabulate]
  have hc : groupCount (paramsOf I g b) = g := by simp [groupCount, paramsOf]
  have hbit : interactionBit (paramsOf I g b,(G.val,H.val),(w,w')) = true ↔
      ∀ p ∈ univ.filter (fun p : Fin k × Fin k => χ p.1 = G ∧ χ p.2 = H),
        relationBit (tabulate I,p.1.val,p.2.val,(x p.1).val,(y p.2).val) = true := by
    unfold interactionBit
    simp only [hv, hc, all_range_fin]
    simp only [nodeValue_of I b hg hD G w, nodeValue_of I b hg hD H w', ite_eq_right_iff]
    simp [Prod.forall, χ, x, y, balanced, Fin.ext_iff, and_imp, paramsOf]
  rw [← BitNetwork.fastInteraction_eq I ⟨0,hD⟩ b χ G H hne w w']
  unfold interactionValue BitNetwork.fastInteraction
  simp_rw [relationValue_of]
  rw [Finset.prod_boole]
  simp only [hbit]
  split_ifs <;> rfl

def weightMachine : Stepped WeightInput ℤ := Stepped.ofFun weightValue
def interactionMachine : Stepped InteractionInput ℤ := Stepped.ofFun interactionValue

@[instance_reducible] def weightMachine_polyT : IsPolyT weightMachine :=
  IsPolyT.ofFun weightValue_polyT

@[instance_reducible] def interactionMachine_polyT : IsPolyT interactionMachine :=
  IsPolyT.ofFun interactionValue_polyT

theorem weightMachine_correct (G : Fin g) (w : List Bool) :
    weightMachine.Runs (paramsOf I g b,G.val,w) 1
      (max (size (paramsOf I g b,G.val,w))
        (size ((BitNetwork.data I ⟨0,hD⟩ b (balanced hg)).W G w)) + 1)
      ((BitNetwork.data I ⟨0,hD⟩ b (balanced hg)).W G w) := by
  simpa only [weightMachine, weightValue_of I b hg hD G w] using
    Stepped.ofFun_runs weightValue (paramsOf I g b,G.val,w)

theorem interactionMachine_correct (G H : Fin g) (hne : G ≠ H) (w w' : List Bool) :
    interactionMachine.Runs (paramsOf I g b,(G.val,H.val),(w,w')) 1
      (max (size (paramsOf I g b,(G.val,H.val),(w,w')))
        (size ((BitNetwork.data I ⟨0,hD⟩ b (balanced hg)).Ψ G H w w')) + 1)
      ((BitNetwork.data I ⟨0,hD⟩ b (balanced hg)).Ψ G H w w') := by
  simpa only [interactionMachine, interactionValue_of I b hg hD G H hne w w'] using
    Stepped.ofFun_runs interactionValue (paramsOf I g b,(G.val,H.val),(w,w'))

#print axioms weightValue_of
#print axioms interactionValue_of
#print axioms weightMachine_polyT
#print axioms interactionMachine_polyT
#print axioms weightMachine_correct
#print axioms interactionMachine_correct

end CSPConsequence.TableRefinement
