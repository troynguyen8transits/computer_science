import Downstream.SparseSupport
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false

/-! Actual finite-domain relabelling through the computed global support list.
Decision equivalence needs no nonisolation. Counting equivalence below is only
claimed when every satisfying assignment already lies in the support. -/
namespace CSPConsequence.SparseSupportDomain
open SparseNormalization SparseSupport

def domainEquiv (D : ℕ) (cs : SparseInput) :
    Fin (support D cs).length ≃ {x : Fin D // x.val ∈ support D cs} :=
  (List.Nodup.getEquiv (support D cs) (support_nodup D cs)).trans
    { toFun := fun x => ⟨⟨x.val,((mem_support D cs x.val).mp x.property).2⟩,x.property⟩
      invFun := fun x => ⟨x.val.val,x.property⟩
      left_inv := fun x => by apply Subtype.ext; rfl
      right_inv := fun x => by apply Subtype.ext; apply Fin.ext; rfl }

def decode (D : ℕ) (cs : SparseInput) (x : Fin (support D cs).length) : Fin D :=
  (domainEquiv D cs x).val

theorem decode_supported (D : ℕ) (cs : SparseInput) (x : Fin (support D cs).length) :
    (decode D cs x).val ∈ support D cs := (domainEquiv D cs x).property

theorem decode_injective (D : ℕ) (cs : SparseInput) : Function.Injective (decode D cs) := by
  intro a b h
  apply (domainEquiv D cs).injective
  exact Subtype.ext h

def encode (D : ℕ) (cs : SparseInput) (x : Fin D) (hx : x.val ∈ support D cs) :
    Fin (support D cs).length := (domainEquiv D cs).symm ⟨x,hx⟩

theorem decode_encode (D : ℕ) (cs : SparseInput) (x : Fin D) (hx : x.val ∈ support D cs) :
    decode D cs (encode D cs x hx) = x := by
  exact congrArg Subtype.val ((domainEquiv D cs).apply_symm_apply ⟨x,hx⟩)

theorem encode_decode (D : ℕ) (cs : SparseInput) (x : Fin (support D cs).length) :
    encode D cs (decode D cs x) (decode_supported D cs x) = x := by
  exact (domainEquiv D cs).symm_apply_apply x

theorem exists_relabelled_iff {k D : ℕ} (cs : SparseInput) (hs : ScopeBounded k cs)
    (hne : cs ≠ []) :
    (∃ z : Fin k → Fin D, RawValid cs z) ↔
      ∃ w : Fin k → Fin (support D cs).length, RawValid cs (fun a => decode D cs (w a)) := by
  rw [exists_supported_iff cs hs hne]
  constructor
  · rintro ⟨z,hz,hmem⟩
    let w : Fin k → Fin (support D cs).length := fun a => encode D cs (z a) (hmem a)
    refine ⟨w,?_⟩
    have he : (fun a => decode D cs (w a)) = z := by
      funext a
      exact decode_encode D cs (z a) (hmem a)
    rw [he]
    exact hz
  · rintro ⟨w,hw⟩
    exact ⟨(fun a => decode D cs (w a)),hw,fun a => decode_supported D cs (w a)⟩

def restricted {k D : ℕ} (cs : SparseInput) (I : Instance k D) :
    Instance k (support D cs).length where
  edge := I.edge
  symmetric := I.symmetric
  relation a b x y := I.relation a b (decode D cs x) (decode D cs y)

theorem restricted_valid_iff {k D : ℕ} (cs : SparseInput) (I : Instance k D)
    (w : Fin k → Fin (support D cs).length) :
    (restricted cs I).valid w ↔ I.valid (fun a => decode D cs (w a)) := Iff.rfl

def solutionEquiv {k D : ℕ} (cs : SparseInput) (I : Instance k D)
    (hs : ∀ z, I.valid z → ∀ a, (z a).val ∈ support D cs) :
    {w // (restricted cs I).valid w} ≃ {z // I.valid z} where
  toFun w := ⟨(fun a => decode D cs (w.val a)),w.property⟩
  invFun z := ⟨(fun a => encode D cs (z.val a) (hs z.val z.property a)),by
    change I.valid (fun a => decode D cs (encode D cs (z.val a) (hs z.val z.property a)))
    simpa only [decode_encode] using z.property⟩
  left_inv w := by
    apply Subtype.ext
    funext a
    exact encode_decode D cs (w.val a)
  right_inv z := by
    apply Subtype.ext
    funext a
    exact decode_encode D cs (z.val a) (hs z.val z.property a)

theorem restricted_count {k D : ℕ} (cs : SparseInput) (I : Instance k D)
    (hs : ∀ z, I.valid z → ∀ a, (z a).val ∈ support D cs) :
    (restricted cs I).count = I.count := by
  classical
  have h := Fintype.card_congr (solutionEquiv cs I hs)
  simpa only [Fintype.card_subtype,Instance.count] using h

theorem normalized_count {k D : ℕ} (cs : SparseInput) (hs : ScopeBounded k cs)
    (hni : Nonisolated k cs) :
    (restricted cs (normalized k D cs)).count = rawCount (k:=k) (D:=D) cs := by
  rw [restricted_count]
  · exact count_eq cs hs hni
  · intro z hz a
    exact all_supported_of_nonisolated cs hs hni z
      ((valid_iff cs hs hni z).mp hz) a

#print axioms exists_relabelled_iff
#print axioms restricted_count
#print axioms normalized_count
end CSPConsequence.SparseSupportDomain
