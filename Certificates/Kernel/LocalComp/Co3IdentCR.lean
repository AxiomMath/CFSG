module

public import Certificates.Kernel.LocalComp.Co3IdentWords
public import Certificates.Kernel.LocalComp.Co3BfsLemmas
public import Certificates.Kernel.LocalComp.Co3BfsGen
public import Certificates.Kernel.LocalComp.Co3IdentModelArrs
meta import Certificates.Kernel.LocalComp.Co3IdentModelArrs
meta import CFSG.Sporadic.Schreier.Co3Arrays
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Co3BfsSound

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelLC.CR CertificateChecks.KernelLC.Co3Id.cList
  CertificateChecks.KernelLC.Co3Id.cPar CertificateChecks.KernelLC.Co3Id.cLab
  CFSG.Sporadic.Schreier.Co3.co3MArrs 1

namespace CertificateChecks.KernelLC.Co3Id

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fendel CFSG.KC.Co3Bfs
open CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.SympSix.Co3Ident CFSG.Sporadic.Schreier.Co3
open CertificateChecks.KernelLC CertificateChecks.KernelSpor

theorem mS_eq (i : Nat) (hi : i < 7) : co3MArrs[i]! = unpack 276 9 (Co3M.S i) :=
  Co3M.arr_eq i (by omega)

theorem mSI_eq (i : Nat) (hi : i < 7) : invCand 276 co3MArrs[i]! = unpack 276 9 (Co3M.SI i) := by
  rw [mS_eq i hi]
  exact (invEqK_sound (allN_spec Co3M.perm i (by omega))).1

theorem kMc : allN 7 (fun i => bAnd(canonK 276 9 (mask 9) (276 * 9) (Co3M.S i),
    canonK 276 9 (mask 9) (276 * 9) (Co3M.SI i))) = true := by quickRfl

@[expose] noncomputable def cAll (k : Nat) : Bool :=
  bAnd(canonE CR.E k,
  bAnd(bIf(Nat.beq k 0, true, stepC Co3M.S Co3M.SI CR.E CR.P CR.L k),
  bAnd(bIf(Nat.beq k 0, true, bIf(Nat.blt (Nat.succ k) CR.c, lexOK CR.P CR.L k, true)),
  bAnd(sortK key4 CR.E CR.S CR.SI CR.c k,
    allN 7 (fun i => cloC Co3M.S Co3M.SI CR.E CR.P CR.L CR.K CR.c k i)))))

theorem kC0 : allFrom (315 * 0) 315 cAll = true := by quickRfl
theorem kC1 : allFrom (315 * 1) 315 cAll = true := by quickRfl

theorem cc : CR.c = 630 := rfl

theorem kCRootE : Nat.beq (CR.E 0) P0 = true := by quickRfl
theorem kCRootP : Nat.beq (CR.P 0) 0 = true := by quickRfl
theorem kCRootL : Nat.beq (CR.L 0) 0 = true := by quickRfl

theorem cAll_spec (k : Nat) (hk : k < CR.c) : canonE CR.E k = true ∧
    (0 < k → stepC Co3M.S Co3M.SI CR.E CR.P CR.L k = true) ∧
    (0 < k → k + 1 < CR.c → lexOK CR.P CR.L k = true) ∧
    sortK key4 CR.E CR.S CR.SI CR.c k = true ∧
    (∀ i < 7, cloC Co3M.S Co3M.SI CR.E CR.P CR.L CR.K CR.c k i = true) := by
  have h : cAll k = true := by
    refine blocks (B := 315) (nb := 2) (by omega) (fun j hj => ?_) k (by rw [cc] at hk; omega)
    interval_cases j
    · exact kC0
    · exact kC1
  unfold cAll at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h
  refine ⟨h1, fun hk' => ?_, fun hk' hk1 => ?_, h4, fun i hi => allN_spec h5 i hi⟩
  · rw [beq_zero_false hk'] at h2
    exact h2
  · have hb : Nat.blt (Nat.succ k) CR.c = true := Nat.ble_eq_true_of_le hk1
    rw [beq_zero_false hk', hb] at h3
    exact h3

theorem cBFS_eq : cBFS = bfsC 630 co3MArrs (genArr 0) := rfl

theorem crec_eq : cBFS.1 = Array.ofFn (n := CR.c) (fun k => unpack 276 9 (CR.E k.val)) ∧
    cBFS.2.1 = Array.ofFn (n := CR.c) (fun k => CR.P k.val) ∧
    cBFS.2.2 = Array.ofFn (n := CR.c) (fun k => CR.L k.val) := by
  rw [cBFS_eq]
  refine bfsC_sound mS_eq mSI_eq (fun i hi => (bAnd_iff _ _).1 (allN_spec kMc i hi))
    (by rw [cc]; omega) (by rw [cc]) ?_ (Nat.eq_of_beq_eq_true kCRootP)
    (Nat.eq_of_beq_eq_true kCRootL)
    (fun k hk => (cAll_spec k hk).1) (fun k h0 hk => (cAll_spec k hk).2.1 h0)
    (fun k h0 hk => (cAll_spec k (by omega)).2.2.1 h0 hk) (fun m hm => (cAll_spec m hm).2.2.2.1)
    (fun q hq i hi => (cAll_spec q hq).2.2.2.2 i hi)
  rw [Nat.eq_of_beq_eq_true kCRootE]
  exact bind0

theorem cList_get (j : Nat) (hj : j < 630) : cBFS.1[j]! = unpack 276 9 (CR.E j) := by
  rw [crec_eq.1]
  exact ofFn_get (fun k => unpack 276 9 (CR.E k)) (by rw [cc]; exact hj)

theorem cPar_get (j : Nat) (hj : j < 630) : cBFS.2.1[j]! = CR.P j := by
  rw [crec_eq.2.1]
  exact ofFn_get (fun k => CR.P k) (by rw [cc]; exact hj)

theorem cLab_get (j : Nat) (hj : j < 630) : cBFS.2.2[j]! = CR.L j := by
  rw [crec_eq.2.2]
  exact ofFn_get (fun k => CR.L k) (by rw [cc]; exact hj)

end CertificateChecks.KernelLC.Co3Id

end
