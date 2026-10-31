import Downstream.FiniteInput
import ToTuring.Lib.List3

set_option autoImplicit false

/-! Polynomial-time raw block reading on encoded data. Parameters are lists and
natural numbers with the library's standard encodings. These certificates are
uniform in the input sizes. The full network provider is not asserted here.
-/

namespace CSPConsequence.ProviderBasics

open Groundwork

abbrev BlockInput := ℕ × (List ℕ × (List Bool × ℕ))

def readBlock (p : BlockInput) : List Bool :=
  (chunks (p.2.1.map fun _ => p.1) p.2.2.1).getD (p.2.1.idxOf p.2.2.2) []

theorem readBlock_eq_cut (b : ℕ) (e : List ℕ) (w : List Bool) (a : ℕ) :
    readBlock (b,e,w,a) = cut (fun _ => b) [] e w a := by
  exact (cut_eq_getD (fun _ => b) [] e w a).symm

theorem readBlock_polyT : PolyT readBlock := by
  unfold readBlock
  fun_prop

abbrev DecodeInput := ℕ × BlockInput

def decodeNat (p : DecodeInput) : ℕ :=
  if p.2.2.2.2 ∈ p.2.2.1 then
    let n := ofWord (readBlock p.2)
    if n < p.1 then n else 0
  else 0

theorem decodeNat_polyT : PolyT decodeNat := by
  unfold decodeNat
  have hread : PolyT (fun p : DecodeInput => readBlock p.2) := readBlock_polyT.comp (by fun_prop)
  fun_prop (disch := assumption)

theorem decodeNat_eq (D b : ℕ) (e : List ℕ) (w : List Bool) (a : ℕ) :
    decodeNat (D,b,e,w,a) =
      if a ∈ e then
        if ofWord (cut (fun _ => b) [] e w a) < D then
          ofWord (cut (fun _ => b) [] e w a) else 0
      else 0 := by
  simp only [decodeNat, readBlock_eq_cut]

#print axioms readBlock_eq_cut
#print axioms readBlock_polyT
#print axioms decodeNat_polyT
#print axioms decodeNat_eq

end CSPConsequence.ProviderBasics
