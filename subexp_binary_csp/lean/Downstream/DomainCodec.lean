import StepMachines.Prog.Chunks
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-! Concrete bit encodings for the actual coarsened CSP domains.

Reuses Anthropic's toWord/ofWord and glue/cut inverse theorems directly.
The encoding is concatenation over the supplied vertex list; it never lists
the exponentially many domain assignments. Runtime bounds are separate.
-/

namespace CSPConsequence.DomainCodec

open Groundwork

def encodeValue {D : ℕ} (b : ℕ) (x : Fin D) : List Bool := toWord b x.val

def decodeValue {D : ℕ} (d : Fin D) (w : List Bool) : Fin D :=
  if h : ofWord w < D then ⟨ofWord w, h⟩ else d

theorem value_roundtrip {D b : ℕ} (d x : Fin D) (hD : D ≤ 2^b) :
    decodeValue d (encodeValue b x) = x := by
  have hw : ofWord (encodeValue b x) = x.val := ofWord_toWord (x.isLt.trans_le hD)
  apply Fin.ext
  simp [decodeValue, hw, x.isLt]

theorem value_reencode {D b : ℕ} (d : Fin D) (w : List Bool)
    (hlen : w.length = b) (hval : ofWord w < D) :
    encodeValue b (decodeValue d w) = w := by
  simp only [decodeValue, dif_pos hval, encodeValue]
  rw [← hlen, toWord_ofWord]

variable {ι : Type} [DecidableEq ι] {D : ℕ}

def encode (b : ℕ) (e : List ι) (z : ι → Fin D) : List Bool :=
  glue e (fun i => if i ∈ e then encodeValue b (z i) else [])

def decode (d : Fin D) (b : ℕ) (e : List ι) (w : List Bool) : ι → Fin D :=
  fun i => if i ∈ e then decodeValue d (cut (fun _ => b) [] e w i) else d

def legal (b : ℕ) (e : List ι) (w : List Bool) : Prop :=
  w.length = b*e.length ∧ ∀ i ∈ e, ofWord (cut (fun _ => b) [] e w i) < D

theorem encode_length (b : ℕ) (e : List ι) (z : ι → Fin D) :
    (encode b e z).length = b*e.length := by
  rw [encode, length_glue (fun _ => b) e _ (by intro i hi; simp [hi, encodeValue])]
  simp [mul_comm]

theorem cut_encode (b : ℕ) (e : List ι) (he : e.Nodup) (z : ι → Fin D) :
    cut (fun _ => b) [] e (encode b e z) =
      fun i => if i ∈ e then encodeValue b (z i) else [] :=
  cut_glue _ _ e he _ (by intro i hi; simp [hi, encodeValue])
    (by intro i hi; simp [hi])

theorem decode_encode {b : ℕ} (d : Fin D) (e : List ι) (he : e.Nodup)
    (z : ι → Fin D) (hD : D ≤ 2^b) :
    decode d b e (encode b e z) = fun i => if i ∈ e then z i else d := by
  funext i
  rw [decode, cut_encode b e he z]
  by_cases hi : i ∈ e
  · simp [hi, value_roundtrip d (z i) hD]
  · simp [hi]

theorem encode_legal {b : ℕ} (e : List ι) (he : e.Nodup)
    (z : ι → Fin D) (hD : D ≤ 2^b) : legal (D := D) b e (encode b e z) := by
  refine ⟨encode_length b e z, ?_⟩
  intro i hi
  rw [cut_encode b e he z]
  simp only [if_pos hi, encodeValue, ofWord_toWord ((z i).isLt.trans_le hD)]
  exact (z i).isLt

theorem encode_decode {b : ℕ} (d : Fin D) (e : List ι) (he : e.Nodup)
    (w : List Bool) (hw : legal (D := D) b e w) :
    encode b e (decode d b e w) = w := by
  have hlen : w.length = (e.map (fun _ => b)).sum := by simpa [mul_comm] using hw.1
  calc
    _ = glue e (cut (fun _ => b) [] e w) := by
      apply glue_congr
      intro i hi
      simp only [if_pos hi, decode]
      exact value_reencode d _ (length_cut _ _ e w hlen hi) (hw.2 i hi)
    _ = w := glue_cut _ _ e he w hlen

#print axioms value_roundtrip
#print axioms encode_length
#print axioms decode_encode
#print axioms encode_legal
#print axioms encode_decode

end CSPConsequence.DomainCodec
