module

public import CFSG.Certificates.Kernel.OpsFpKSound
public import CFSG.Sporadic.GLQ.HNTwoRankInputs
public import Certificates.Kernel.Sporadic.RawGen
import all CFSG.Blueprint.NativeSporadic
meta import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelGLQ.HNTwo.HS1 CFSG.Blueprint.NativeSporadic.HNSeed1

#ks_chars CertificateChecks.KernelGLQ.HNTwo.HS2 CFSG.Blueprint.NativeSporadic.HNSeed2

namespace CertificateChecks.KernelGLQ.HNTwo

open CFSG.KC.Ord CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.Sporadic.GLQ
open CFSG.Sporadic.GLQ.HNTwoRank CFSG.KS.SporSch.LyM

@[expose] noncomputable def cL : Nat := rep1 13 17689

@[expose] noncomputable def cH : Nat := Nat.shiftLeft cL 12

@[expose] noncomputable def cCM : Nat := Nat.mul (Nat.sub (Nat.shiftLeft 1 13) 1) (rep1 1729 133)

@[expose] noncomputable def cRM : Nat := Nat.sub (Nat.shiftLeft 1 1729) 1

@[expose] noncomputable def cONE : Nat := rep1 1742 133

@[expose] noncomputable def cLV : Nat := rep1 13 133

@[expose] noncomputable def cHV : Nat := Nat.shiftLeft cLV 12

noncomputable abbrev O5 : Ops Nat Nat := opsFpK 5 13 1729 133 9 cL cH cCM cRM cONE

@[expose] noncomputable def pay (cs : List Char) : Nat := payRunP 5 133 13 1729 cs 0 0 0

@[expose] noncomputable def vld (X : Nat) : Bool := validM 5 (133 * 1729) cL cH X

@[expose] noncomputable def checkHN (A B : Nat) : Bool :=
  vld A && vld B && O5.eq (powN O5 3 A 2) O5.one && O5.eq (powN O5 4 B 3) O5.one &&
    forceB (powN O5 3 B 2) fun B2 => runK O5 hnProg (initRegsN O5 11 (A, A) (B, B2)) fun R =>
      forceL (List.ofFn fun j => signedWordN O5 R[1]! R[2]! (hnWords j)) fun xs =>
        elem2OK O5 xs [0]

theorem kConsts : constsOK 5 13 1729 133 9 cL cH cCM cRM cONE cLV cHV = true := by quickRfl

theorem kLt : hnProg.all (Instr.lt 11) = true := by decide +kernel

theorem kHN : forceB (pay HS1.chars) (fun A => forceB (pay HS2.chars) fun B => checkHN A B) =
    true := by
  quickRfl

end CertificateChecks.KernelGLQ.HNTwo

end
