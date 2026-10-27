module

public import CFSG.Certificates.Kernel.CTIBqSound3140
public import Certificates.Kernel.TwoE6.CTIBqChecks

public section

namespace CertificateChecks.KernelTwoE6

open CFSG.KC.CTIBq

open Certificates in
open CFSG.EvenSmallLie.TwoE6 in
theorem cert3140 : d8WitnessOK = true := by
  have h := sound3140 CFSG.Monster.B.Bin.gramRows (CFSG.Monster.B.CTIB.Native.liftImgsN 6)
    (CFSG.Monster.B.CTIB.Native.liftImgsN 8) CFSG.Monster.B.Bin.quotRows1
    CFSG.Monster.B.Bin.quotRows2 GR A6 A8 Q1 Q2 kBindsN k3140
  rw [← CFSG.Monster.B.CTIB.Native.gArr] at h
  unfold CFSG.EvenSmallLie.TwoE6.d8WitnessOK
  unfold d8G at h
  exact h

end CertificateChecks.KernelTwoE6

end
