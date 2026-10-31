import Downstream.DomainCodec
import Groundwork.Net.Calculus

set_option autoImplicit false

/-! Finite-sum transport for the concrete block encoding.
This is the interface used for group settings and cross-group labels. All
encoders/decoders come from DomainCodec; the finite sets specify semantics.
-/

namespace CSPConsequence.DomainCodec

open Finset Groundwork

variable {ι : Type} [Fintype ι] [DecidableEq ι] {D : ℕ}

def assignments (d : Fin D) (e : List ι) : Finset (ι → Fin D) :=
  tuples (fun i => i ∈ e) (fun _ => univ) d

def encodedStates (D b : ℕ) (e : List ι) : Finset (List Bool) :=
  (words (b*e.length)).filter fun w => ∀ i ∈ e,
    ofWord (cut (fun _ => b) [] e w i) < D

theorem mem_assignments (d : Fin D) (e : List ι) (z : ι → Fin D) :
    z ∈ assignments d e ↔ ∀ i, i ∉ e → z i = d := by
  simp [assignments, mem_tuples]

theorem mem_encodedStates (b : ℕ) (e : List ι) (w : List Bool) :
    w ∈ encodedStates D b e ↔ legal (D := D) b e w := by
  simp [encodedStates, legal, mem_words]

theorem decode_mem (d : Fin D) (b : ℕ) (e : List ι) (w : List Bool) :
    decode d b e w ∈ assignments d e := by
  rw [mem_assignments]
  intro i hi
  simp [decode, hi]

theorem decode_encode_assignment {b : ℕ} (d : Fin D) (e : List ι)
    (he : e.Nodup) (hD : D ≤ 2^b) (z : ι → Fin D)
    (hz : z ∈ assignments d e) : decode d b e (encode b e z) = z := by
  rw [decode_encode d e he z hD]
  funext i
  by_cases hi : i ∈ e
  · simp [hi]
  · simp [hi, (mem_assignments d e z).mp hz i hi]

theorem encode_bijOn {b : ℕ} (d : Fin D) (e : List ι) (he : e.Nodup)
    (hD : D ≤ 2^b) :
    Set.BijOn (encode b e) (assignments d e : Set (ι → Fin D))
      (encodedStates D b e : Set (List Bool)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z _
    exact (mem_encodedStates b e _).mpr (encode_legal e he z hD)
  · intro z hz z' hz' h
    have h' := congrArg (decode d b e) h
    rwa [decode_encode_assignment d e he hD z hz,
      decode_encode_assignment d e he hD z' hz'] at h'
  · intro w hw
    exact ⟨decode d b e w, decode_mem d b e w,
      encode_decode d e he w ((mem_encodedStates b e w).mp hw)⟩

theorem sum_encoded {b : ℕ} (d : Fin D) (e : List ι) (he : e.Nodup)
    (hD : D ≤ 2^b) (F : List Bool → ℤ) :
    ∑ w ∈ encodedStates D b e, F w =
      ∑ z ∈ assignments d e, F (encode b e z) := by
  obtain ⟨hm, hi, hs⟩ := encode_bijOn d e he hD
  exact (Finset.sum_nbij (encode b e) hm hi hs (fun _ _ => rfl)).symm

#print axioms encode_bijOn
#print axioms sum_encoded

end CSPConsequence.DomainCodec
