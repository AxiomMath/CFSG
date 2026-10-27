module

public import Certificates.Kernel.Sporadic.Co3.Bind
public import CFSG.Sporadic.Schreier.Co3GenerationCheckInputs
meta import CFSG.Sporadic.Schreier.Co3GenerationCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelSporSch.Co3J 276 9 16 CFSG.Sporadic.Schreier.Co3.co3JointArrs
  CFSG.Sporadic.Schreier.Co3.co3JointBaseArr 13 CFSG.Sporadic.Schreier.Co3.co3JointDerivations

namespace CertificateChecks.KernelSporSch.Co3J

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Co3 CertificateChecks.KernelSpor

theorem lines : allN 25 (fun j => Nat.beq (S j) (Co3Text.L (Nat.add 86 j))) = true := by
  quickRfl

theorem perm : allN 25 (fun j => permOK 276 9 (mask 9) (276 * 9) (S j) (SI j)) = true := by
  quickRfl

theorem binds : Binds 276 9 S 25 7 BP co3JointArrs co3JointBaseArr := by
  obtain ⟨hs, he⟩ := Co3Text.field_of (f := 10) rfl (by norm_num) lines
  exact ⟨by norm_num, by norm_num, by norm_num, hs, he, by decide, by decide⟩

theorem arr_eq (k : Nat) (hk : k < 25) : co3JointArrs[k]! = unpack 276 9 (S k) :=
  binds.2.2.2.2.1 k hk

end CertificateChecks.KernelSporSch.Co3J

end
