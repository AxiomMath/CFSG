module

public import Certificates.Kernel.J4Q.Mat
public import Certificates.Kernel.J4Q.FormInvData
public import CFSG.Certificates.Kernel.J4Q.RepQT2B
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.J4.QTRankWitNative

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop CFSG.Sporadic.J4.Native

theorem form_pack : andB (packOK F formRows.toList) (andB (canonJ pad F)
    (andB (canonJ pad FI) (Nat.beq (mulJ c rm F FI) one))) = true := by quickRfl

theorem form_inverse_check : eqRows (mulRows formRows (invRows formRows)) idRows = true := by
  have h := form_pack
  simp only [andB_eq, Bool.and_eq_true] at h
  have hF := packOK_sound hK h.1 h.2.1
  have hFI := invRows_enc hK hF.1 h.2.2.1 (by rw [hF.2]; exact h.2.2.2)
  rw [eqRows_of (mul_enc hK hF hFI) (id_enc hK)]
  exact h.2.2.2

end CertificateChecks.KernelJ4Q

end
