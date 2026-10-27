module

public import Certificates.Kernel.Sporadic.Co3.Bind36
public import CFSG.Sporadic.Schreier.Co3Sp6CheckInputs
meta import CFSG.Sporadic.Schreier.Co3Sp6CheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelSpor.Co3Sp36 36 6 36 CFSG.Sporadic.Schreier.Co3.co3Sp36Arrs
  CFSG.Sporadic.Schreier.Co3.co3Sp36BaseArr 63 CFSG.Sporadic.Schreier.Co3.co3Sp36Derivations

namespace CertificateChecks.KernelSpor.Co3Sp36

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Co3

theorem lines : allN 66 (fun j => Nat.beq (S j) (Co3Text36.L (Nat.add 0 j))) = true := by
  quickRfl

theorem perm : allN 66 (fun j => permOK 36 6 (mask 6) (36 * 6) (S j) (SI j)) = true := by
  quickRfl

theorem binds : Binds 36 6 S 66 6 BP co3Sp36Arrs co3Sp36BaseArr := by
  obtain ⟨hs, he⟩ := Co3Text36.field_of (f := 0) rfl (by norm_num) lines
  exact ⟨by norm_num, by norm_num, by norm_num, hs, he, by decide, by decide⟩

theorem arr_eq (k : Nat) (hk : k < 66) : co3Sp36Arrs[k]! = unpack 36 6 (S k) :=
  binds.2.2.2.2.1 k hk

@[expose] noncomputable def sift (G : Nat) : Bool :=
  siftK 36 6 (mask 6) (36 * 6) (pidn 36 6) LR TRI BP 6 0 G

end CertificateChecks.KernelSpor.Co3Sp36

end
