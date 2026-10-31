import Downstream.ProviderParameters
import Downstream.DecoderRefinement
import ToTuring.Poly.IsPoly

set_option autoImplicit false

/-! The actual encoded input/node computations match the semantic bit network.
Preparation complexity is not claimed by this source-to-input tabulation.
-/

namespace CSPConsequence.NodeRefinement

open Groundwork DomainCodec ProviderBasics ProviderParameters FiniteInput

def paramsOf {k D : ℕ} (I : Instance k D) (g b : ℕ) : Params :=
  (tabulate I, List.replicate g (), List.replicate b ())

theorem map_finRange_val (k : ℕ) : (List.finRange k).map Fin.val = List.range k := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [List.finRange]

theorem nodeMembers_of {k D g : ℕ} (I : Instance k D) (b : ℕ)
    (hg : 0 < g) (G : Fin g) :
    nodeMembers (paramsOf I g b,G.val) =
      (EncodedSettings.members (balanced (k := k) hg) G).map Fin.val := by
  unfold nodeMembers paramsOf groupCount
  simp only [vertices_tabulate, List.length_replicate]
  rw [← map_finRange_val k, List.filter_map]
  unfold EncodedSettings.members
  apply congrArg (List.map Fin.val)
  apply List.filter_congr
  intro a _
  apply Bool.eq_iff_iff.mpr
  simp [balanced, Fin.ext_iff]

theorem nodeValue_of {k D g : ℕ} (I : Instance k D) (b : ℕ)
    (hg : 0 < g) (hD : 0 < D) (G : Fin g) (w : List Bool) (a : Fin k) :
    nodeValue (paramsOf I g b,G.val,w,a.val) =
      (decode ⟨0,hD⟩ b (EncodedSettings.members (balanced hg) G) w a).val := by
  unfold nodeValue
  rw [nodeMembers_of I b hg G]
  simpa [paramsOf, blockWidth, domain_tabulate] using
    DecoderRefinement.decoder_eq hD b (EncodedSettings.members (balanced hg) G) w a

theorem nodeLegal_of {k D g : ℕ} (I : Instance k D) (b : ℕ)
    (hg : 0 < g) (hD : 0 < D) (G : Fin g) (w : List Bool) :
    nodeLegal (paramsOf I g b,G.val,w) = true ↔
      w ∈ (BitNetwork.data I ⟨0,hD⟩ b (balanced hg)).S G := by
  unfold nodeLegal
  rw [nodeMembers_of I b hg G]
  change _ ↔ w ∈ encodedStates D b (EncodedSettings.members (balanced hg) G)
  rw [mem_encodedStates]
  simp [paramsOf, blockWidth, domain_tabulate, List.all_map, List.all_eq_true,
    DecoderRefinement.readBlock_fin, legal]

def memMachine : Stepped (Params × (ℕ × List Bool)) Bool := Stepped.ofFun nodeLegal

def memMachine_polyT : IsPolyT memMachine := IsPolyT.ofFun nodeLegal_polyT

/-- One abstract step, with its separately proved polynomial-time native implementation. -/
theorem memMachine_correct {k D g : ℕ} (I : Instance k D) (b : ℕ)
    (hg : 0 < g) (hD : 0 < D) (G : Fin g) (w : List Bool) :
    memMachine.Runs (paramsOf I g b,G.val,w) 1
      (max (size (paramsOf I g b,G.val,w))
        (size (decide (w ∈ (BitNetwork.data I ⟨0,hD⟩ b (balanced hg)).S G))) + 1)
      (decide (w ∈ (BitNetwork.data I ⟨0,hD⟩ b (balanced hg)).S G)) := by
  have he : nodeLegal (paramsOf I g b,G.val,w) =
      decide (w ∈ (BitNetwork.data I ⟨0,hD⟩ b (balanced hg)).S G) := by
    apply Bool.eq_iff_iff.mpr
    simpa using nodeLegal_of I b hg hD G w
  simpa only [memMachine, he] using Stepped.ofFun_runs nodeLegal (paramsOf I g b,G.val,w)

#print axioms nodeMembers_of
#print axioms nodeValue_of
#print axioms nodeLegal_of
#print axioms memMachine_polyT
#print axioms memMachine_correct

end CSPConsequence.NodeRefinement
