module

public import Certificates.Kernel.Sporadic.Co3.Bind
public import CFSG.Sporadic.Schreier.Co3OrderCheckInputs
meta import CFSG.Sporadic.Schreier.Co3OrderCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelSpor.Co3C 276 9 16 CFSG.Sporadic.Schreier.Co3.co3ChainArrs
  CFSG.Sporadic.Schreier.Co3.co3ChainBaseArr 2 CFSG.Sporadic.Schreier.Co3.co3ChainDerivations

namespace CertificateChecks.KernelSpor.Co3C

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Text CFSG.Sporadic.Schreier.Co3

theorem lines : allN 14 (fun j => Nat.beq (S j) (Co3Text.L (Nat.add 0 j))) = true := by quickRfl

theorem perm : allN 14 (fun j => permOK 276 9 (mask 9) (276 * 9) (S j) (SI j)) = true := by
  quickRfl

theorem binds : Binds 276 9 S 14 7 BP co3ChainArrs co3ChainBaseArr := by
  obtain ⟨hs, he⟩ := Co3Text.field_of (f := 0) rfl (by norm_num) lines
  exact ⟨by norm_num, by norm_num, by norm_num, hs, he, by decide, by decide⟩

@[expose] noncomputable def sift (G : Nat) : Bool :=
  siftK 276 9 (mask 9) (276 * 9) (pidn 276 9) LR TRI BP 7 0 G

end CertificateChecks.KernelSpor.Co3C

end
