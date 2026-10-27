module

public import Certificates.Kernel.LyGlue.TabData
public import CFSG.Certificates.Kernel.Common.SliceRange

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

#kc_slice_range CertificateChecks.KernelLy.conjK CertificateChecks.KernelLy.cj 0 13

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS

theorem cj_neg : allN 66825 (fun a => Nat.beq (tl (tIdx 11) (tl (tIdx 3) a))
    (tl (tIdx 3) (tl (tIdx 11) a))) = false := by
  decide +kernel

end CertificateChecks.KernelLy

end
