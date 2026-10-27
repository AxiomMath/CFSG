module

public import Certificates.Kernel.Sporadic.Co2Inv.Data
public import Certificates.Kernel.Sporadic.Co2Inv.Mats
public import CFSG.Certificates.Kernel.Co2InvS.Check
public import Certificates.Kernel.Sporadic.Co2.FRows
public import CFSG.Certificates.Kernel.Spor.Loops
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Cover
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

public section

namespace CertificateChecks.KernelSpor.Co2Inv

open CFSG.KC.Co2InvS CFSG.KC.Co1F2 CFSG.Sporadic.Co2Inv CFSG.Sporadic.SmallF2.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Cert

theorem gens_size : co2InvGens.size = 5 := rfl

theorem gen0 : co2InvGens[0]! = unpackR 22 (G 0) := by decide +kernel
theorem gen1 : co2InvGens[1]! = unpackR 22 (G 1) := by decide +kernel
theorem gen2 : co2InvGens[2]! = unpackR 22 (G 2) := by decide +kernel
theorem gen3 : co2InvGens[3]! = unpackR 22 (G 3) := by decide +kernel
theorem gen4 : co2InvGens[4]! = unpackR 22 (G 4) := by decide +kernel

theorem gens_eq : ∀ j < 5, co2InvGens[j]! = unpackR 22 (G j) := by
  intro j hj
  interval_cases j
  exacts [gen0, gen1, gen2, gen3, gen4]

theorem rep0 : co2InvReps[0]! = unpackR 22 (WT 113) := by decide +kernel
theorem rep1 : co2InvReps[1]! = unpackR 22 (WT 114) := by decide +kernel
theorem rep2 : co2InvReps[2]! = unpackR 22 (WT 115) := by decide +kernel

theorem reps_eq : ∀ r < 3, co2InvReps[r]! = unpackR 22 (WT (113 + r)) := by
  intro r hr
  interval_cases r
  exacts [rep0, rep1, rep2]

@[expose] def RI (r : Nat) : Nat := if r = 0 then 12 else if r = 1 then 30 else 152

theorem repAt0 : Nat.beq (elemAt E.CF 12) (WT 113) = true := by quickRfl
theorem repAt1 : Nat.beq (elemAt E.CF 30) (WT 114) = true := by quickRfl
theorem repAt2 : Nat.beq (elemAt E.CF 152) (WT 115) = true := by quickRfl

theorem reps_at : ∀ r < 3, RI r < sOrder ∧ co2InvReps[r]! = Lf E.CF (RI r) := by
  intro r hr
  have e0 : RI 0 = 12 := rfl
  have e1 : RI 1 = 30 := rfl
  have e2 : RI 2 = 152 := rfl
  interval_cases r
  · rw [e0, rep0, Lf, Nat.eq_of_beq_eq_true repAt0]
    exact ⟨by decide, rfl⟩
  · rw [e1, rep1, Lf, Nat.eq_of_beq_eq_true repAt1]
    exact ⟨by decide, rfl⟩
  · rw [e2, rep2, Lf, Nat.eq_of_beq_eq_true repAt2]
    exact ⟨by decide, rfl⟩

@[expose] noncomputable def seedK (l : Nat) : Nat := selN (Nat.beq l 0) (WT 116) (WT 117)

@[expose] noncomputable def wordK (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) IDP (fun l _ acc => mulV (seedK l) acc) w

theorem seedA : co2RowsA = unpackR 22 (WT 116) := by
  rw [Co2Faith.rowsA_eq]
  decide +kernel

theorem seedB : co2RowsB = unpackR 22 (WT 117) := by
  rw [Co2Faith.rowsB_eq]
  decide +kernel

theorem seedRows_eq (l : Nat) : seedRows l = unpackR 22 (seedK l) := by
  unfold seedRows seedK
  rw [selN_eq]
  by_cases h : l = 0
  · rw [iteT h, h, Nat.beq_refl, iteT rfl, seedA]
  · rw [iteF h, beq_false h, iteF Bool.false_ne_true, seedB]

theorem wordRowsSeed_eq : ∀ w : List Nat, wordRowsSeed w = unpackR 22 (wordK w)
  | [] => idRows_eq
  | l :: w => by
    have e : wordK (l :: w) = mulV (seedK l) (wordK w) := rfl
    rw [wordRowsSeed, e, ← mulRows_unpack, ← wordRowsSeed_eq w, seedRows_eq]

@[expose] noncomputable def candK (c : Nat) : Bool :=
  andK (Nat.blt (co2InvCands[c]!).1 (nat_lit 3)) (
  andK (Nat.beq (wordK (co2InvCands[c]!).2) (WT c)) (
  andK (Nat.beq (mulV (WT c) (WT (Nat.add (nat_lit 54) c))) IDP)
    (Nat.beq (mulV (mulV (WT c) (WT (Nat.add (nat_lit 113) (co2InvCands[c]!).1)))
      (WT (Nat.add (nat_lit 54) c))) (YT c))))

theorem cands_ok : CFSG.KC.Enum.allN 54 candK = true := by quickRfl

theorem inv_ok : ∀ c < 54, (CFSG.Monster.B.Max2.Native.inv22 (unpackR 22 (WT c)) ==
    unpackR 22 (WT (Nat.add 54 c))) = true := by
  kc_cover 2

theorem cand_facts {c : Nat} (hc : c < 54) : (co2InvCands[c]!).1 < 3 ∧
    candW c = unpackR 22 (WT c) ∧
    CFSG.Monster.B.Max2.Native.inv22 (candW c) = unpackR 22 (WT (54 + c)) ∧
    mulV (WT c) (WT (54 + c)) = IDP ∧
    mulV (mulV (WT c) (WT (113 + (co2InvCands[c]!).1))) (WT (54 + c)) = YT c := by
  have h := CFSG.KS.allN_spec cands_ok c hc
  unfold candK at h
  simp only [andK_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hw : candW c = unpackR 22 (WT c) := by
    rw [candW, wordRowsSeed_eq, Nat.eq_of_beq_eq_true h2]
  refine ⟨blt_iff.1 h1, hw, ?_, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4⟩
  rw [hw]
  exact beq_iff_eq.1 (inv_ok c hc)

theorem ybind : YBind YT := by
  refine ⟨Array.size_ofFn, fun c hc => ?_⟩
  obtain ⟨h1, hw, hi, -, hy⟩ := cand_facts hc
  rw [candYs, getElem!_pos _ c (by simp [hc]), Array.getElem_ofFn, candY, hi, hw,
    reps_eq _ h1, mulRows_unpack, mulRows_unpack, hy]

theorem cand_check : candCheck = true := by
  unfold candCheck
  simp only [Bool.and_eq_true, beq_iff_eq, allLt_iff, decide_eq_true_eq]
  refine ⟨rfl, fun c hc => ?_⟩
  obtain ⟨h1, hw, hi, hm, -⟩ := cand_facts hc
  refine ⟨h1, ?_⟩
  rw [hi, hw, mulRows_unpack, hm, idRows_eq]

theorem rank0 : (wfRows co2InvReps[0]! && isInvolRows co2InvReps[0]! &&
    mulRows 22 co2InvRankP[0]! (CFSG.Monster.B.Max2.Native.inv22 co2InvRankP[0]!) == idRows 22 &&
    mulRows 22 co2InvRankQ[0]! (CFSG.Monster.B.Max2.Native.inv22 co2InvRankQ[0]!) == idRows 22 &&
    mulRows 22 (mulRows 22 co2InvRankP[0]! (addId co2InvReps[0]!)) co2InvRankQ[0]! ==
      truncId (6 + 2 * 0)) = true := by decide +kernel

theorem rank1 : (wfRows co2InvReps[1]! && isInvolRows co2InvReps[1]! &&
    mulRows 22 co2InvRankP[1]! (CFSG.Monster.B.Max2.Native.inv22 co2InvRankP[1]!) == idRows 22 &&
    mulRows 22 co2InvRankQ[1]! (CFSG.Monster.B.Max2.Native.inv22 co2InvRankQ[1]!) == idRows 22 &&
    mulRows 22 (mulRows 22 co2InvRankP[1]! (addId co2InvReps[1]!)) co2InvRankQ[1]! ==
      truncId (6 + 2 * 1)) = true := by decide +kernel

theorem rank2 : (wfRows co2InvReps[2]! && isInvolRows co2InvReps[2]! &&
    mulRows 22 co2InvRankP[2]! (CFSG.Monster.B.Max2.Native.inv22 co2InvRankP[2]!) == idRows 22 &&
    mulRows 22 co2InvRankQ[2]! (CFSG.Monster.B.Max2.Native.inv22 co2InvRankQ[2]!) == idRows 22 &&
    mulRows 22 (mulRows 22 co2InvRankP[2]! (addId co2InvReps[2]!)) co2InvRankQ[2]! ==
      truncId (6 + 2 * 2)) = true := by decide +kernel

theorem rank_check : rankCheck = true := by
  unfold rankCheck
  rw [Bool.and_eq_true, allLt_iff]
  refine ⟨rfl, fun r hr => ?_⟩
  interval_cases r
  exacts [rank0, rank1, rank2]

end CertificateChecks.KernelSpor.Co2Inv

end
