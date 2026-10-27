module

public import Certificates.Kernel.Sporadic.Co3.Bind
public import CFSG.Sporadic.Schreier.Co3SylowCheckInputs
meta import CFSG.Sporadic.Schreier.Co3SylowCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelSpor.Co3T 276 9 16 CFSG.Sporadic.Schreier.Co3.co3TArrs
  CFSG.Sporadic.Schreier.Co3.co3TBaseArr 8 CFSG.Sporadic.Schreier.Co3.co3TDerivations

namespace CertificateChecks.KernelSpor.Co3T

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Text CFSG.Sporadic.Schreier.Co3

theorem lines : allN 10 (fun j => Nat.beq (S j) (Co3Text.L (Nat.add 35 j))) = true := by
  quickRfl

theorem perm : allN 10 (fun j => permOK 276 9 (mask 9) (276 * 9) (S j) (SI j)) = true := by
  quickRfl

theorem binds : Binds 276 9 S 10 3 BP co3TArrs co3TBaseArr := by
  obtain ⟨hs, he⟩ := Co3Text.field_of (f := 5) rfl (by norm_num) lines
  exact ⟨by norm_num, by norm_num, by norm_num, hs, he, by decide, by decide⟩

theorem arr_eq (k : Nat) (hk : k < 10) : co3TArrs[k]! = unpack 276 9 (S k) := binds.2.2.2.2.1 k hk

@[expose] noncomputable def sift (G : Nat) : Bool :=
  siftK 276 9 (mask 9) (276 * 9) (pidn 276 9) LR TRI BP 3 0 G

end CertificateChecks.KernelSpor.Co3T

end
