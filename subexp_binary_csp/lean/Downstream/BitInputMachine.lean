import Downstream.BitInputRoundtrip
import Downstream.CounterExistence
import CountKSat.Host
import ToTuring.Lib.Int

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-! Explicit bit-input/bit-output composition and the imported native host.
The algorithmic backend and native simulation are Anthropic's checked sources.
The native polynomial q is selected once before all input/level parameters.
The explicit bound below is not yet its asymptotic absorption or a sparse-input
normalization theorem, and it does not imply polynomial space. -/
namespace CSPConsequence.BitInputMachine
open Groundwork Printed Turing NodeRefinement QuerySizes DynamicPreparation

def outputBits (z : Int) : List Bool := Nat.bits z.toNat
@[fun_prop] theorem outputBits_polyT : PolyT outputBits := by unfold outputBits; fun_prop

def machine (M : Stepped PreparedInput Int) : Stepped (List Bool) (List Bool) :=
  Stepped.mapOut (Stepped.mapIn BitInputCodec.decode M) outputBits

theorem machine_poly (M : Stepped PreparedInput Int) (hM : Nonempty (IsPolyT M)) :
    Nonempty (IsPolyT (machine M)) := by
  obtain ⟨h⟩ := hM
  letI : IsPolyT M := h
  letI : IsPolyT (Stepped.mapIn BitInputCodec.decode M) :=
    IsPolyT.mapIn BitInputCodec.decode_polyT
  exact ⟨IsPolyT.mapOut outputBits_polyT⟩

theorem machine_runs {M : Stepped PreparedInput Int} {p : PreparedInput} {T S n : Nat}
    (hp : BitInputCodec.Rectangular p) (h : M.Runs p T S (n : Int)) :
    (machine M).Runs (BitInputCodec.encode p) T S (Nat.bits n) := by
  have hd : M.Runs (BitInputCodec.decode (BitInputCodec.encode p)) T S (n : Int) := by
    simpa only [BitInputCodec.decode_encode p hp] using h
  have hb := Stepped.mapOut_runs (f := outputBits)
    (Stepped.mapIn_runs (f := BitInputCodec.decode) hd)
  simpa only [machine,outputBits,Int.toNat_natCast] using hb

/-- One host polynomial, chosen before every input, state bound, and result. -/
theorem exists_native (M : Stepped PreparedInput Int) (hM : Nonempty (IsPolyT M)) :
    ∃ (N : TM2ComputableAux Bool Bool) (q : Nat), (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ (p : PreparedInput) (T S n : Nat), BitInputCodec.Rectangular p → M.Runs p T S (n : Int) →
        Nonempty (TM2OutputsInTime N.tm ((BitInputCodec.encode p).map N.inputAlphabet.invFun)
          (some ((Nat.bits n).map N.outputAlphabet.invFun))
          (q*(T+1)*((BitInputCodec.encode p).length+S+1)^q)) := by
  obtain ⟨hpoly⟩ := machine_poly M hM
  letI : IsPolyT (machine M) := hpoly
  obtain ⟨N,q,hfin,hhost⟩ := CountKSat.exists_tmW (machine M)
  exact ⟨N,q,hfin,fun p T S n hp hr => hhost _ _ _ _ (machine_runs hp hr)⟩

/-- Native version of the existing concrete RunBound, with precisely the same
T and state expression. Native initialization/output are charged by q. -/
def NativeRunBound {k D g : Nat} (I : Instance k D) (b Δ K C₁ 𝒯 : Nat)
    (N : TM2ComputableAux Bool Bool) (q : Nat) : Prop :=
  let P := Δ*b*(k/g+1)
  let B := (k/g+1)+(k/g+1)*(k/g+1)+1
  let p := (paramsOf I g b,unary K)
  let S := size (paramsOf I g b)+(𝒯+(g*(P+B)+size (1,2*K))^C₁)+
    room (paramsOf I g b) g P B+4
  ∃ T : Nat, Nonempty (TM2OutputsInTime N.tm ((BitInputCodec.encode p).map N.inputAlphabet.invFun)
    (some ((Nat.bits I.count).map N.outputAlphabet.invFun))
    (q*(3*T+1)*((BitInputCodec.encode p).length+S+1)^q)) ∧
    (T : Real) ≤ ((K : Real)^g+𝒯*(2 : Real)^(2*(g : Real)*P/K))*((g : Real)*(P+B))^C₁

/-- The imported algorithm supplies the counter; no counter or clique oracle is
assumed. N and q are fixed for Δ, before k,D,g,b,l or the CSP are supplied. -/
theorem exists_native_counter (Δ : Nat) :
    ∃ (c : CounterExistence.Counter Δ) (N : TM2ComputableAux Bool Bool) (q : Nat),
      (∀ i, Finite (N.tm.Γ i)) ∧
      ∀ {k D g : Nat} (I : Instance k D) (b l : Nat) (hg : 0 < g) (hpos : 0 < D),
        1 ≤ b → D ≤ 2^b → 1 ≤ Δ → (∀ a, I.degree a ≤ Δ) → 2 ≤ g → g = 3*(c.K l)^8 →
        NativeRunBound (g := g) I b Δ (c.K l) c.C₁
          (LevelCounter.budget (c.e l) c.C₀ (c.K l) g (Δ*b*(k/g+1))
            ((k/g+1)+(k/g+1)*(k/g+1)+1)
            (BitNetwork.data I ⟨0,hpos⟩ b (balanced hg)).U) N q := by
  obtain ⟨c⟩ := CounterExistence.exists_counter Δ
  obtain ⟨N,q,hfin,hhost⟩ := exists_native c.machine c.poly
  refine ⟨c,N,q,hfin,?_⟩
  intro k D g I b l hg hpos hb hD hΔ hdeg hg2 hgK
  obtain ⟨T,hr,ht⟩ := c.correct I b l hg hpos hb hD hΔ hdeg hg2 hgK
  exact ⟨T,hhost _ _ _ _ (BitInputCodec.rectangular_paramsOf I g b (c.K l)) hr,ht⟩

#print axioms outputBits_polyT
#print axioms machine_poly
#print axioms machine_runs
#print axioms exists_native
#print axioms exists_native_counter
end CSPConsequence.BitInputMachine
