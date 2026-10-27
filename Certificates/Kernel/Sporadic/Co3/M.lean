module

public import Certificates.Kernel.Sporadic.Co3.Bind
public import CFSG.Sporadic.Schreier.Co3CentralizerCheckInputs
meta import CFSG.Sporadic.Schreier.Co3CentralizerCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelSpor.Co3M 276 9 16 CFSG.Sporadic.Schreier.Co3.co3MArrs
  CFSG.Sporadic.Schreier.Co3.co3MBaseArr 7 CFSG.Sporadic.Schreier.Co3.co3MDerivations

#ks_rawchain CertificateChecks.KernelSpor.Co3M1 276 9 16 CFSG.Sporadic.Schreier.Co3.co3M1Arrs
  CFSG.Sporadic.Schreier.Co3.co3M1BaseArr 6 CFSG.Sporadic.Schreier.Co3.co3M1Derivations

namespace CertificateChecks.KernelSpor.Co3M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Co3

theorem lines : allN 14 (fun j => Nat.beq (S j) (Co3Text.L (Nat.add 45 j))) = true := by
  quickRfl

theorem perm : allN 14 (fun j => permOK 276 9 (mask 9) (276 * 9) (S j) (SI j)) = true := by
  quickRfl

theorem binds : Binds 276 9 S 14 4 BP co3MArrs co3MBaseArr := by
  obtain ⟨hs, he⟩ := Co3Text.field_of (f := 6) rfl (by norm_num) lines
  exact ⟨by norm_num, by norm_num, by norm_num, hs, he, by decide, by decide⟩

theorem arr_eq (k : Nat) (hk : k < 14) : co3MArrs[k]! = unpack 276 9 (S k) := binds.2.2.2.2.1 k hk

@[expose] noncomputable def sift (G : Nat) : Bool :=
  siftK 276 9 (mask 9) (276 * 9) (pidn 276 9) LR TRI BP 4 0 G

end CertificateChecks.KernelSpor.Co3M

namespace CertificateChecks.KernelSpor.Co3M1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Co3

theorem lines : allN 11 (fun j => Nat.beq (S j) (Co3Text.L (Nat.add 59 j))) = true := by
  quickRfl

theorem perm : allN 11 (fun j => permOK 276 9 (mask 9) (276 * 9) (S j) (SI j)) = true := by
  quickRfl

theorem binds : Binds 276 9 S 11 4 BP co3M1Arrs co3M1BaseArr := by
  obtain ⟨hs, he⟩ := Co3Text.field_of (f := 7) rfl (by norm_num) lines
  exact ⟨by norm_num, by norm_num, by norm_num, hs, he, by decide, by decide⟩

theorem arr_eq (k : Nat) (hk : k < 11) : co3M1Arrs[k]! = unpack 276 9 (S k) :=
  binds.2.2.2.2.1 k hk

end CertificateChecks.KernelSpor.Co3M1

end
