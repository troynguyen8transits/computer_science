import Downstream.ProviderLabels
import Downstream.TableRefinement

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! All metadata of the concrete query provider, including unary writability.
These functions and procedures are uniform on the finite encoded Params input.
Semantic Give certificates are supplied separately.
-/

namespace CSPConsequence.ProviderMetadata

open Groundwork FiniteInput ProviderParameters NodeRefinement ProviderTables
  TableRefinement ProviderLabels

def scale (p : Params) : ℕ := vertices p.1 / groupCount p + 1
def boundP (Δ : ℕ) (p : Params) : ℕ := Δ*blockWidth p*scale p
def boundB (p : Params) : ℕ := scale p + scale p*scale p + 1
def nodeLength (p : Params × ℕ) : ℕ := blockWidth p.1*(nodeMembers p).length
def edgeCapacity (p : CrossingInput) : ℕ := blockWidth p.1*(crossingPairs p).length

theorem scale_unary : Unary scale := by
  have hv : Unary (fun p : Params => vertices p.1) := by
    unfold vertices
    exact Unary.of_length (by fun_prop)
  have hp : PolyT scale := by unfold scale vertices groupCount; fun_prop
  refine Unary.of_le (g := fun p : Params => vertices p.1 + 1)
    (Unary.add hv (Unary.const 1)) hp ?_
  intro p
  exact Nat.add_le_add_right (Nat.div_le_self _ _) 1

theorem boundP_unary (Δ : ℕ) : Unary (boundP Δ) :=
  Unary.mul (Unary.mul (Unary.const Δ) (Unary.of_length (by fun_prop))) scale_unary

theorem boundB_unary : Unary boundB :=
  Unary.add (Unary.add scale_unary (Unary.mul scale_unary scale_unary)) (Unary.const 1)

theorem nodeLength_unary : Unary nodeLength :=
  Unary.mul (Unary.of_length (by fun_prop)) (Unary.of_length nodeMembers_polyT)

theorem edgeCapacity_unary : Unary edgeCapacity :=
  Unary.mul (Unary.of_length (by fun_prop)) (Unary.of_length crossingPairs_polyT)

def procs (Δ : ℕ) : Eight.SecNetworks.Procs Params where
  P := boundP Δ
  B := boundB
  len c a := nodeLength (c,a)
  cap c a v := edgeCapacity (c,(a,v))
  mem := NodeRefinement.memMachine
  W := weightMachine
  Ψ := interactionMachine
  f := Stepped.ofFun factorValue

theorem procs_keeps (Δ : ℕ) : (procs Δ).Keeps :=
  ⟨nodeLength_unary, edgeCapacity_unary, ⟨NodeRefinement.memMachine_polyT⟩,
    ⟨weightMachine_polyT⟩, ⟨interactionMachine_polyT⟩, ⟨IsPolyT.ofFun factorValue_polyT⟩⟩

variable {k D g : ℕ} (I : Instance k D) (d : Fin D) (b Δ : ℕ) (hg : 0 < g)

theorem P_of : (procs Δ).P (paramsOf I g b) = Δ*b*(k/g+1) := by
  simp [procs, boundP, scale, blockWidth, groupCount, paramsOf, vertices_tabulate]

theorem B_of : (procs Δ).B (paramsOf I g b) = (k/g+1)+(k/g+1)*(k/g+1)+1 := by
  simp [procs, boundB, scale, groupCount, paramsOf, vertices_tabulate]

theorem len_of (G : Fin g) : (procs Δ).len (paramsOf I g b) G.val =
    (BitNetwork.data I d b (balanced hg)).len G := by
  change blockWidth (paramsOf I g b)*(nodeMembers (paramsOf I g b,G.val)).length = _
  rw [nodeMembers_of I b hg G]
  simp [paramsOf, blockWidth, BitNetwork.data]

#print axioms boundP_unary
#print axioms boundB_unary
#print axioms procs_keeps
#print axioms len_of

end CSPConsequence.ProviderMetadata
