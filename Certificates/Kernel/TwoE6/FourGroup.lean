module

public import CFSG.Certificates.Kernel.CTIBqSound3128
public import Certificates.Kernel.TwoE6.CTIBqChecks

public section

namespace CertificateChecks.KernelTwoE6

open CFSG.KC.CTIBq

open Certificates in
open CFSG.EvenSmallLie.TwoE6 in
theorem cert3128 : fgOK = true := by
  have h := sound3128 CFSG.Monster.B.Bin.gramRows (CFSG.Monster.B.CTIB.Native.liftImgsN 6)
    (CFSG.Monster.B.CTIB.Native.liftImgsN 8) CFSG.Monster.B.Bin.quotRows1
    CFSG.Monster.B.Bin.quotRows2 GR A6 A8 Q1 Q2 kBindsN k3128
  rw [← CFSG.Monster.B.CTIB.Native.gArr] at h
  unfold CFSG.EvenSmallLie.TwoE6.fgOK CFSG.EvenSmallLie.TwoE6.fgPairOK
  unfold fgG fgPairG at h
  exact h

end CertificateChecks.KernelTwoE6

end
