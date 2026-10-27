module

public import Certificates.Kernel.Sporadic.SuzInv.Text0
public import Certificates.Kernel.Sporadic.SuzInv.Text1
public import Certificates.Kernel.Sporadic.SuzInv.Text2
public import Certificates.Kernel.Sporadic.SuzInv.Text3
public import CFSG.Certificates.Kernel.Spor.HexAtSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.Loops
meta import CFSG.Sporadic.SuzOddCore.InvArrays
import all CFSG.Sporadic.SuzOddCore.InvArrays
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
meta import CFSG.Sporadic.SuzOddCore.Arrays

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore

meta def oddRunsM : Array (Array Nat) :=
  ((List.range 4).toArray.map fun i =>
    ((List.range (invRunCount i - invOddStart i)).toArray.map fun k =>
      invRun i (invOddStart i + k))).flatten

meta def allInvM : Array (Array Nat) :=
  ((List.range 4).toArray.map fun i =>
    ((List.range (invRunCount i)).toArray.map fun k =>
      CFSG.Monster.B.Co2.Native.invCand 1782 (invRun i k))).flatten

end CertificateChecks.KernelSpor.OddCore

#kmisc_packarrs CertificateChecks.KernelSpor.SuzInvO CertificateChecks.KernelSpor.OddCore.oddRunsM 11

#kmisc_packarrs CertificateChecks.KernelSpor.SuzInvI CertificateChecks.KernelSpor.OddCore.allInvM 11

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.HexAt

@[expose] noncomputable def runP (i k : Nat) : Nat :=
  nIf(Nat.beq i 0, nIf(Nat.blt k 82, SuzInvT0.F k, SuzInvO (Nat.add 0 (Nat.sub k 82))),
  nIf(Nat.beq i 1, nIf(Nat.blt k 44, SuzInvT1.F k, SuzInvO (Nat.add 10 (Nat.sub k 44))),
  nIf(Nat.beq i 2, nIf(Nat.blt k 20, SuzInvT2.F k, SuzInvO (Nat.add 37 (Nat.sub k 20))),
    nIf(Nat.blt k 36, SuzInvT3.F k, SuzInvO (Nat.add 57 (Nat.sub k 36))))))

theorem odd0 : hexAtK SuzInvT0.chars (Nat.mul 5346 82) 3 1782 11 10 (offF SuzInvO 0) = true := by
  quickRfl

theorem odd1 : hexAtK SuzInvT1.chars (Nat.mul 5346 44) 3 1782 11 27 (offF SuzInvO 10) = true := by
  quickRfl

theorem odd2 : hexAtK SuzInvT2.chars (Nat.mul 5346 20) 3 1782 11 20 (offF SuzInvO 37) = true := by
  quickRfl

theorem odd3 : hexAtK SuzInvT3.chars (Nat.mul 5346 36) 3 1782 11 26 (offF SuzInvO 57) = true := by
  quickRfl

theorem perms0 : allN 92 (fun k =>
    invEqK 1782 11 (mask 11) (1782 * 11) (runP 0 k) (SuzInvI k)) = true := by
  quickRfl

theorem perms1 : allN 71 (fun k =>
    invEqK 1782 11 (mask 11) (1782 * 11) (runP 1 k) (SuzInvI (Nat.add 92 k))) = true := by
  quickRfl

theorem perms2 : allN 40 (fun k =>
    invEqK 1782 11 (mask 11) (1782 * 11) (runP 2 k) (SuzInvI (Nat.add 163 k))) = true := by
  quickRfl

theorem perms3 : allN 62 (fun k =>
    invEqK 1782 11 (mask 11) (1782 * 11) (runP 3 k) (SuzInvI (Nat.add 203 k))) = true := by
  quickRfl

theorem odd_run {i os cnt ob k : Nat} {cs : List Char} (hs : invText i = String.ofList cs)
    (h : hexAtK cs (Nat.mul 5346 os) 3 1782 11 cnt (offF SuzInvO ob) = true)
    (hk1 : os ≤ k) (hk2 : k < os + cnt) :
    invRun i k = unpack 1782 11 (SuzInvO (Nat.add ob (Nat.sub k os))) := by
  have e := hexAt_unpack h (j := k - os) (by omega)
  refine Eq.trans ?_ e
  unfold invRun
  rw [hs]
  apply Array.ext
  · simp [CFSG.Monster.B.Co2.Native.hexTable]
  · intro x h1 _
    simp only [CFSG.Monster.B.Co2.Native.hexTable, Array.getElem_ofFn]
    have ex : 3 * (1782 * k + x) = Nat.mul 5346 os + 3 * (1782 * (k - os) + x) := by
      simp only [Nat.mul_eq]
      omega
    rw [ex]

theorem blt_false {a b : Nat} (h : b ≤ a) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (Eq.mp Nat.blt_eq hb) (by omega)

theorem run_all {i k : Nat} (hi : i < 4) (hk : k < invRunCount i) :
    invRun i k = unpack 1782 11 (runP i k) := by
  interval_cases i
  · change k < 92 at hk
    change _ = unpack 1782 11 (nIf(Nat.blt k 82, SuzInvT0.F k, SuzInvO (Nat.add 0 (Nat.sub k 82))))
    rcases Nat.lt_or_ge k 82 with h | h
    · rw [SuzInv.run_eq0 h, Eq.mpr Nat.blt_eq h]
    · rw [odd_run (i := 0) (os := 82) (cnt := 10) (ob := 0) SuzInvT0.eq odd0 h (by omega), blt_false h]
  · change k < 71 at hk
    change _ = unpack 1782 11
      (nIf(Nat.blt k 44, SuzInvT1.F k, SuzInvO (Nat.add 10 (Nat.sub k 44))))
    rcases Nat.lt_or_ge k 44 with h | h
    · rw [SuzInv.run_eq1 h, Eq.mpr Nat.blt_eq h]
    · rw [odd_run (i := 1) (os := 44) (cnt := 27) (ob := 10) SuzInvT1.eq odd1 h (by omega), blt_false h]
  · change k < 40 at hk
    change _ = unpack 1782 11
      (nIf(Nat.blt k 20, SuzInvT2.F k, SuzInvO (Nat.add 37 (Nat.sub k 20))))
    rcases Nat.lt_or_ge k 20 with h | h
    · rw [SuzInv.run_eq2 h, Eq.mpr Nat.blt_eq h]
    · rw [odd_run (i := 2) (os := 20) (cnt := 20) (ob := 37) SuzInvT2.eq odd2 h (by omega), blt_false h]
  · change k < 62 at hk
    change _ = unpack 1782 11
      (nIf(Nat.blt k 36, SuzInvT3.F k, SuzInvO (Nat.add 57 (Nat.sub k 36))))
    rcases Nat.lt_or_ge k 36 with h | h
    · rw [SuzInv.run_eq3 h, Eq.mpr Nat.blt_eq h]
    · rw [odd_run (i := 3) (os := 36) (cnt := 26) (ob := 57) SuzInvT3.eq odd3 h (by omega), blt_false h]

theorem perm_all {i k : Nat} (hi : i < 4) (hk : k < invRunCount i) :
    ∃ r, invEqK 1782 11 (mask 11) (1782 * 11) (runP i k) r = true := by
  interval_cases i
  · exact ⟨_, allN_spec perms0 k hk⟩
  · exact ⟨_, allN_spec perms1 k hk⟩
  · exact ⟨_, allN_spec perms2 k hk⟩
  · exact ⟨_, allN_spec perms3 k hk⟩

end CertificateChecks.KernelSpor.OddCore

end
