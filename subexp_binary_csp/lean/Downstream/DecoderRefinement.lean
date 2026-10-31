import Downstream.ProviderBasics

set_option autoImplicit false

/-! The polynomial-time raw decoder equals the actual typed semantic decoder.
This relates integer list indices to Fin indices on every string, including
invalid domain encodings and absent indices. The default value is zero.
-/

namespace CSPConsequence.DecoderRefinement

open Groundwork DomainCodec ProviderBasics

theorem idxOf_map_val {k : ℕ} (e : List (Fin k)) (a : Fin k) :
    (e.map Fin.val).idxOf a.val = e.idxOf a := by
  induction e with
  | nil => rfl
  | cons v e ih =>
    by_cases h : v = a
    · subst v
      simp
    · have hv : v.val ≠ a.val := fun hv => h (Fin.ext hv)
      simp [List.idxOf_cons, h, hv, ih]

theorem mem_map_val {k : ℕ} (e : List (Fin k)) (a : Fin k) :
    a.val ∈ e.map Fin.val ↔ a ∈ e := by
  constructor
  · intro ha
    obtain ⟨v,hv,heq⟩ := List.mem_map.mp ha
    have h : v = a := Fin.ext heq
    simpa [h] using hv
  · intro ha
    exact List.mem_map.mpr ⟨a,ha,rfl⟩

theorem readBlock_fin {k : ℕ} (b : ℕ) (e : List (Fin k)) (w : List Bool) (a : Fin k) :
    readBlock (b,e.map Fin.val,w,a.val) = cut (fun _ => b) [] e w a := by
  rw [readBlock, cut_eq_getD, idxOf_map_val]
  simp [List.map_map, Function.comp_def]

theorem decoder_eq {k D : ℕ} (hD : 0 < D) (b : ℕ)
    (e : List (Fin k)) (w : List Bool) (a : Fin k) :
    decodeNat (D,b,e.map Fin.val,w,a.val) =
      (DomainCodec.decode ⟨0,hD⟩ b e w a).val := by
  unfold decodeNat DomainCodec.decode
  simp only [mem_map_val, readBlock_fin]
  by_cases ha : a ∈ e
  · simp only [if_pos ha]
    unfold decodeValue
    split_ifs <;> rfl
  · simp [ha]

#print axioms readBlock_fin
#print axioms decoder_eq

end CSPConsequence.DecoderRefinement
