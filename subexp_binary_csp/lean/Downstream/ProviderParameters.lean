import Downstream.ProviderBasics
import ToTuring.Lib.Unary

set_option autoImplicit false

/-! Raw provider parameters and polynomial-time node decoding. The group count
and block width are stored in unary; the eventual preparation theorem must
construct them and bound that preparation. No finite-type function is encoded.
-/

namespace CSPConsequence.ProviderParameters

open Groundwork FiniteInput ProviderBasics

abbrev Params := Input × (List Unit × List Unit)

def groupCount (p : Params) : ℕ := p.2.1.length
def blockWidth (p : Params) : ℕ := p.2.2.length

def nodeMembers (p : Params × ℕ) : List ℕ :=
  (List.range (vertices p.1.1)).filter fun a => decide (a % groupCount p.1 = p.2)

@[fun_prop] theorem nodeMembers_polyT : PolyT nodeMembers := by
  have hrange : PolyT (fun p : Params × ℕ => List.range (vertices p.1.1)) :=
    PolyT.range (Unary.of_length (by fun_prop))
  unfold nodeMembers groupCount
  fun_prop (disch := assumption)

abbrev NodeValueInput := Params × (ℕ × (List Bool × ℕ))

def nodeValue (p : NodeValueInput) : ℕ :=
  decodeNat (domain p.1.1, blockWidth p.1, nodeMembers (p.1,p.2.1), p.2.2.1, p.2.2.2)

@[fun_prop] theorem nodeValue_polyT : PolyT nodeValue := by
  apply ProviderBasics.decodeNat_polyT.comp
  unfold domain blockWidth
  fun_prop

def nodeLegal (p : Params × (ℕ × List Bool)) : Bool :=
  let e := nodeMembers (p.1,p.2.1)
  decide (p.2.2.length = blockWidth p.1 * e.length) &&
    e.all (fun a => decide (ofWord (readBlock (blockWidth p.1,e,p.2.2,a)) < domain p.1.1))

@[fun_prop] theorem nodeLegal_polyT : PolyT nodeLegal := by
  unfold nodeLegal domain blockWidth
  dsimp only
  have hread : PolyT (fun p : (Params × (ℕ × List Bool)) × ℕ =>
      readBlock (p.1.1.2.2.length, nodeMembers (p.1.1,p.1.2.1), p.1.2.2, p.2)) := by
    apply ProviderBasics.readBlock_polyT.comp
    fun_prop
  fun_prop (disch := assumption)

#print axioms nodeMembers_polyT
#print axioms nodeValue_polyT
#print axioms nodeLegal_polyT

end CSPConsequence.ProviderParameters
