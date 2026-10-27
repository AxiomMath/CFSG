module

public import Certificates.Kernel.Sporadic.Co3.Bind
public import CFSG.Sporadic.Schreier.Co3OrderCheckInputs
meta import CFSG.Sporadic.Schreier.Co3OrderCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelSpor.Co3CP 276 9 16 CFSG.Sporadic.Schreier.Co3.co3CoprimeArrs
  CFSG.Sporadic.Schreier.Co3.co3CoprimeBaseArr 2 CFSG.Sporadic.Schreier.Co3.co3CoprimeDerivations

namespace CertificateChecks.KernelSpor.Co3CP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Co3

theorem lines : allN 14 (fun j => Nat.beq (S j) (Co3Text.L (Nat.add 14 j))) = true := by
  quickRfl

theorem perm : allN 14 (fun j => permOK 276 9 (mask 9) (276 * 9) (S j) (SI j)) = true := by
  quickRfl

theorem binds : Binds 276 9 S 14 7 BP co3CoprimeArrs co3CoprimeBaseArr := by
  obtain ⟨hs, he⟩ := Co3Text.field_of (f := 1) rfl (by norm_num) lines
  exact ⟨by norm_num, by norm_num, by norm_num, hs, he, by decide, by decide⟩

theorem arr_eq (k : Nat) (hk : k < 14) : co3CoprimeArrs[k]! = unpack 276 9 (S k) :=
  binds.2.2.2.2.1 k hk

end CertificateChecks.KernelSpor.Co3CP

end
