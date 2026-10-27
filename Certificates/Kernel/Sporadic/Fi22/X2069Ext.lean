
module

public import Certificates.Kernel.Sporadic.Fi22.Ext2073
public import Certificates.Kernel.Sporadic.ON.Gen
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckBase
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheckBase
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22X

meta def extRowsM : Array (Array Nat) := (Array.range 21).map CFSG.Sporadic.FischerOddCore.fi22ExtArr

meta def outT4M : Array (Array Nat) := CFSG.Monster.B.Fischer.fi22OuterStrong3510 4

end CertificateChecks.KernelSpor.Fi22X

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22X.EX CertificateChecks.KernelSpor.Fi22X.extRowsM 12

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22X.TS CertificateChecks.KernelSpor.Fi22X.outT4M 12

namespace CertificateChecks.KernelSpor.Fi22X

open CFSG.KC.Enum CFSG.KS CFSG.KS.Text CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native

@[expose] noncomputable def extLineOK (L : Nat) : Bool :=
  lineK 3 3510 12 (EX L) (Fi22ExtT.chars.drop (Nat.mul L (nat_lit 10531)))

@[expose] noncomputable def outLineOK (j : Nat) : Bool :=
  lineK 3 3510 12 (TS j) (Fi22OutT.chars.drop (Nat.mul (Nat.add (nat_lit 20) j) (nat_lit 10531)))

theorem extAscii : asciiK (Fi22ExtT.chars.take (Nat.mul (nat_lit 21) (nat_lit 10531))) = true := by
  quickRfl

theorem outAscii : asciiK (Fi22OutT.chars.take (Nat.mul (nat_lit 33) (nat_lit 10531))) = true := by
  quickRfl

theorem asciiK_iff (l : List Char) : asciiK l = true ↔ ∀ c ∈ l, c.toNat < 128 := by
  induction l with
  | nil => simp [asciiK]
  | cons c l ih =>
    have e : asciiK (c :: l) = bAnd(Nat.blt (Char.toNat c) (nat_lit 128), asciiK l) := rfl
    rw [e, bAnd_iff, ih, List.forall_mem_cons, Nat.blt_eq]

theorem asciiK_take {cs : List Char} {k m : Nat} (h : asciiK (cs.take m) = true) (hk : k ≤ m) :
    asciiK (cs.take k) = true := by
  rw [asciiK_iff] at h ⊢
  intro c hc
  apply h c
  have e : (cs.take m).take k = cs.take k := by
    rw [List.take_take, Nat.min_eq_left hk]
  rw [← e] at hc
  exact List.mem_of_mem_take hc

end CertificateChecks.KernelSpor.Fi22X

#kon_slices CertificateChecks.KernelSpor.Fi22X.extLineOK 0 21

#kon_join CertificateChecks.KernelSpor.Fi22X.extAll CertificateChecks.KernelSpor.Fi22X.extLineOK 21

#kon_slices CertificateChecks.KernelSpor.Fi22X.outLineOK 0 13

#kon_join CertificateChecks.KernelSpor.Fi22X.outAll CertificateChecks.KernelSpor.Fi22X.outLineOK 13

namespace CertificateChecks.KernelSpor.Fi22X

open CFSG.KC.Enum CFSG.KS CFSG.KS.Text CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native

theorem line_of {s : String} {cs : List Char} (hs : s = String.ofList cs) {L P : Nat}
    (ha : asciiK (cs.take ((L + 1) * (3 * 3510 + 1))) = true)
    (h : lineK 3 3510 12 P (cs.drop (L * (3 * 3510 + 1))) = true) :
    hexLine s.toUTF8 3 3510 L = unpack 3510 12 P := by
  subst hs
  have hl := lineK_sound ha h
  apply Array.ext
  · simp [hexLine, CFSG.KS.Raw.unpack]
  · intro i h1 h2
    simp only [hexLine, CFSG.KS.Raw.unpack, Array.getElem_ofFn]
    exact hl i (by simpa [hexLine] using h1)

theorem ext_eq {L : Nat} (hL : L < 21) : fi22ExtArr L = unpack 3510 12 (EX L) := by
  exact line_of Fi22ExtT.eq (asciiK_take extAscii (by simp only [Nat.mul_eq]; omega)) (extAll L hL)

theorem outT_eq {j : Nat} (hj : j < 13) : (fi22OuterStrong3510 4)[j]! = unpack 3510 12 (TS j) := by
  have hl : fi22OuterLine3510 4 j = 20 + j := by
    unfold fi22OuterLine3510
    simp [fi22OuterLines3510]
  unfold fi22OuterStrong3510
  rw [getElem!_pos _ j (by simpa [fi22OuterLines3510] using hj), Array.getElem_ofFn]
  change fi22OuterArr3510 (fi22OuterLine3510 4 j) = _
  rw [hl]
  exact line_of Fi22OutT.eq (asciiK_take outAscii (by simp only [Nat.mul_eq]; omega)) (outAll j hj)

end CertificateChecks.KernelSpor.Fi22X

end
