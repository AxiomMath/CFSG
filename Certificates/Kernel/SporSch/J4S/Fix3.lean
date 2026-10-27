module

public import Certificates.Kernel.SporSch.J4S.RankP
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4FixedData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J4Fix3

open CFSG.KC.Enum CFSG.KS CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B
open CFSG.Sporadic.J4Schreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4Eta
open CertificateChecks.KernelSporSch.J4Rank

@[expose] noncomputable def fixK (P : Nat) (vs : Array Nat) : Bool :=
  let a := vs[0]!
  let b := vs[1]!
  let c := vs[2]!
  decide (a < 2 ^ 112) && decide (b < 2 ^ 112) && decide (c < 2 ^ 112) &&
    decide (vecJ rm a P = a) && decide (vecJ rm b P = b) && decide (vecJ rm c P = c) &&
    (List.range 8).all fun i => (List.range 8).all fun j =>
      i == j || comb3 a b c i != comb3 a b c j

theorem get!_eq (X : Array Nat) (i : Nat) : X[i]! = X[i]?.getD 0 := by
  by_cases h : i < X.size
  · rw [getElem!_pos X i h, getElem?_pos X i h, Option.getD_some]
  · rw [getElem!_neg X i h, getElem?_neg X i h, Option.getD_none]
    rfl

theorem vecMulRows_eq (X : Array Nat) (v : Nat) : ∀ n, vecMulRows X v n =
    (List.range n).foldl (fun acc j => if v.testBit j then acc ^^^ (X[j]?.getD 0) else acc) 0
  | 0 => rfl
  | n + 1 => by
    rw [vecMulRows, vecMulRows_eq X v n, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil, get!_eq]
    by_cases h : v.testBit n <;> simp [h]

theorem fix3_of {X : Array Nat} (hX : WfN X) (vs : Array Nat) :
    fix3OK X vs = fixK (encN X) vs := by
  have h : ∀ v, vecMulRows X v 112 = vecJ rm v (encN X) := fun v => by
    rw [vecMulRows_eq]
    exact vec_enc J4Real.hK hX v
  simp only [fix3OK, fixK, h]

theorem fixQ : allN 26 (fun k => fixK (QF (Nat.succ k)) q3FixVecs[k]!) = true := by quickRfl

theorem q3FixOK_true : q3FixOK Q3GenPairs = true := by
  rw [q3FixOK, List.all_eq_true]
  intro k hk
  have hk' : k < 26 := List.mem_range.1 hk
  have h := elt_ok (k + 1) (by omega)
  rw [fix3_of h.1.1, h.1.2]
  exact allN_spec fixQ k hk'

end CertificateChecks.KernelSporSch.J4Fix3

end
