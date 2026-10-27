module

public import Certificates.Kernel.Sporadic.Co3.Bind
public import Certificates.Kernel.Sporadic.Co3.Bind36
public import CFSG.Sporadic.Schreier.Co3FirstCheckInputs
meta import CFSG.Sporadic.Schreier.Co3FirstCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelSpor.Co3MComm 276 9 16
  CFSG.Sporadic.Schreier.Co3.co3MCommArrs CFSG.Sporadic.Schreier.Co3.co3MCommBaseArr 4
  CFSG.Sporadic.Schreier.Co3.co3MCommDerivations

#ks_rawchain CertificateChecks.KernelSpor.Co3M36 36 6 36 CFSG.Sporadic.Schreier.Co3.co3M36Arrs
  CFSG.Sporadic.Schreier.Co3.co3M36BaseArr 6 CFSG.Sporadic.Schreier.Co3.co3M36Derivations

namespace CertificateChecks.KernelSpor.Co3MComm

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Co3

theorem lines : allN 8 (fun j => Nat.beq (S j) (Co3Text.L (Nat.add 70 j))) = true := by
  quickRfl

theorem perm : allN 8 (fun j => permOK 276 9 (mask 9) (276 * 9) (S j) (SI j)) = true := by
  quickRfl

theorem binds : Binds 276 9 S 8 4 BP co3MCommArrs co3MCommBaseArr := by
  obtain ⟨hs, he⟩ := Co3Text.field_of (f := 8) rfl (by norm_num) lines
  exact ⟨by norm_num, by norm_num, by norm_num, hs, he, by decide, by decide⟩

theorem arr_eq (k : Nat) (hk : k < 8) : co3MCommArrs[k]! = unpack 276 9 (S k) :=
  binds.2.2.2.2.1 k hk

end CertificateChecks.KernelSpor.Co3MComm

namespace CertificateChecks.KernelSpor.Co3M36

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Co3

theorem lines : allN 16 (fun j => Nat.beq (S j) (Co3Text36.L (Nat.add 66 j))) = true := by
  quickRfl

theorem perm : allN 16 (fun j => permOK 36 6 (mask 6) (36 * 6) (S j) (SI j)) = true := by
  quickRfl

theorem binds : Binds 36 6 S 16 6 BP co3M36Arrs co3M36BaseArr := by
  obtain ⟨hs, he⟩ := Co3Text36.field_of (f := 1) rfl (by norm_num) lines
  exact ⟨by norm_num, by norm_num, by norm_num, hs, he, by decide, by decide⟩

theorem arr_eq (k : Nat) (hk : k < 16) : co3M36Arrs[k]! = unpack 36 6 (S k) :=
  binds.2.2.2.2.1 k hk

end CertificateChecks.KernelSpor.Co3M36

end
