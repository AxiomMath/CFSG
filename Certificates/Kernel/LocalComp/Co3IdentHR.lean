module

public import Certificates.Kernel.LocalComp.Co3IdentWords
public import Certificates.Kernel.LocalComp.Co3BfsLemmas
public import Certificates.Kernel.LocalComp.Co3BfsGen
meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentModelInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Co3BfsSound

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelLC.HR CFSG.EvenSmallLie.SympSix.Co3Ident.hList
  CFSG.EvenSmallLie.SympSix.Co3Ident.hPar CFSG.EvenSmallLie.SympSix.Co3Ident.hLab
  CFSG.EvenSmallLie.SympSix.Co3Ident.gArrs 0

namespace CertificateChecks.KernelLC.Co3Id

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fendel CFSG.KC.Co3Bfs
open CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.SympSix.Co3Ident CFSG.Sporadic.Schreier.Co3
open CertificateChecks.KernelLC

theorem kGw : allN 3 (fun i => bAnd(wordOK (pos (gLetters i)),
    Nat.beq (wordP (pos (gLetters i))) (HR.G i))) = true := by quickRfl

theorem kGc : allN 3 (fun i => canonK 276 9 (mask 9) (276 * 9) (HR.G i)) = true := by quickRfl

theorem g_eq (i : Nat) (hi : i < 3) : gArrs[i]! = unpack 276 9 (HR.G i) := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec kGw i hi)
  have e : gArrs[i]! = posArr (gLetters i) := by
    unfold gArrs
    exact ofFn_get (c := 3) (fun j => posArr (gLetters j)) hi
  rw [e, posArr, wordArr_eq _ h1, Nat.eq_of_beq_eq_true h2]

@[expose] noncomputable def hAll (k : Nat) : Bool :=
  bAnd(canonE HR.E k,
  bAnd(bIf(Nat.beq k 0, true, stepR HR.G HR.E HR.P HR.L k),
  bAnd(bIf(Nat.beq k 0, true, bIf(Nat.blt (Nat.succ k) HR.c, lexOK HR.P HR.L k, true)),
  bAnd(sortK keyR HR.E HR.S HR.SI HR.c k,
    allN 3 (fun i => cloR HR.G HR.E HR.P HR.L HR.K HR.c k i)))))

theorem kB0 : allFrom (512 * 0) 512 hAll = true := by quickRfl
theorem kB1 : allFrom (512 * 1) 512 hAll = true := by quickRfl
theorem kB2 : allFrom (512 * 2) 512 hAll = true := by quickRfl
theorem kB3 : allFrom (512 * 3) 512 hAll = true := by quickRfl
theorem kB4 : allFrom (512 * 4) 512 hAll = true := by quickRfl
theorem kB5 : allFrom (512 * 5) 512 hAll = true := by quickRfl
theorem kB6 : allFrom (512 * 6) 512 hAll = true := by quickRfl
theorem kB7 : allFrom (512 * 7) 512 hAll = true := by quickRfl
theorem kB8 : allFrom (512 * 8) 512 hAll = true := by quickRfl

theorem hc : HR.c = 4608 := rfl

theorem kRootE : Nat.beq (HR.E 0) (pidn 276 9) = true := by quickRfl
theorem kRootP : Nat.beq (HR.P 0) 0 = true := by quickRfl
theorem kRootL : Nat.beq (HR.L 0) 0 = true := by quickRfl
theorem hAll_all (k : Nat) (hk : k < HR.c) : hAll k = true := by
  refine blocks (B := 512) (nb := 9) (by omega) (fun j hj => ?_) k (by rw [hc] at hk; omega)
  interval_cases j
  · exact kB0
  · exact kB1
  · exact kB2
  · exact kB3
  · exact kB4
  · exact kB5
  · exact kB6
  · exact kB7
  · exact kB8

theorem hAll_spec (k : Nat) (hk : k < HR.c) : canonE HR.E k = true ∧
    (0 < k → stepR HR.G HR.E HR.P HR.L k = true) ∧
    (0 < k → k + 1 < HR.c → lexOK HR.P HR.L k = true) ∧
    sortK keyR HR.E HR.S HR.SI HR.c k = true ∧
    (∀ i < 3, cloR HR.G HR.E HR.P HR.L HR.K HR.c k i = true) := by
  have h := hAll_all k hk
  unfold hAll at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h
  refine ⟨h1, fun hk' => ?_, fun hk' hk1 => ?_, h4, fun i hi => allN_spec h5 i hi⟩
  · rw [beq_zero_false hk'] at h2
    exact h2
  · have hb : Nat.blt (Nat.succ k) HR.c = true := Nat.ble_eq_true_of_le hk1
    rw [beq_zero_false hk', hb] at h3
    exact h3

theorem hBFS_eq : hBFS = bfsR 4608 gArrs := by
  rw [hBFS_def]
  rfl

theorem rec_eq : hBFS.1 = Array.ofFn (n := HR.c) (fun k => unpack 276 9 (HR.E k.val)) ∧
    hBFS.2.1 = Array.ofFn (n := HR.c) (fun k => HR.P k.val) ∧
    hBFS.2.2.1 = Array.ofFn (n := HR.c) (fun k => HR.L k.val) := by
  rw [hBFS_eq]
  exact bfsR_sound g_eq (fun i hi => allN_spec kGc i hi) (by rw [hc]; omega) (by rw [hc])
    (Nat.eq_of_beq_eq_true kRootE) (Nat.eq_of_beq_eq_true kRootP) (Nat.eq_of_beq_eq_true kRootL)
    (fun k hk => (hAll_spec k hk).1) (fun k h0 hk => (hAll_spec k hk).2.1 h0)
    (fun k h0 hk => (hAll_spec k (by omega)).2.2.1 h0 hk) (fun m hm => (hAll_spec m hm).2.2.2.1)
    (fun q hq i hi => (hAll_spec q hq).2.2.2.2 i hi)

theorem hList_get (j : Nat) (hj : j < 4608) : hList[j]! = unpack 276 9 (HR.E j) := by
  unfold hList
  rw [rec_eq.1]
  exact ofFn_get (fun k => unpack 276 9 (HR.E k)) (by rw [hc]; exact hj)

theorem hPar_get (j : Nat) (hj : j < 4608) : hPar[j]! = HR.P j := by
  unfold hPar
  rw [rec_eq.2.1]
  exact ofFn_get (fun k => HR.P k) (by rw [hc]; exact hj)

theorem hLab_get (j : Nat) (hj : j < 4608) : hLab[j]! = HR.L j := by
  unfold hLab
  rw [rec_eq.2.2]
  exact ofFn_get (fun k => HR.L k) (by rw [hc]; exact hj)

end CertificateChecks.KernelLC.Co3Id

end
