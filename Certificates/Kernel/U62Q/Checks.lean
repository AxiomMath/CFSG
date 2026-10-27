module

public import Certificates.Kernel.U62Q.Enum
public import Certificates.Kernel.T46K.ChainDefs
public import Certificates.Data.Kernel.U62Q

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 200

namespace CertificateChecks.KernelU62Q

open CFSG.KC.Enum CFSG.KS CFSG.KS.PC CFSG.KS.T46K CFSG.KC.U62Q CertificateChecks.KernelT46

theorem szQ : Nat.beq EQ.ng 3 = true ∧ Nat.beq EQ.N 729 = true :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem pG : allN 3 (fun k => CFSG.KC.Misc.ArrEnum.permB 693 10 (EQ.G k)) = true := by
  decide +kernel

theorem siftQ : allN 3 (fun k =>
    siftF LK POST PART LABT CNTT BT QT 5 0 (mapK (pg 10 (mask 10) (EQ.G k)) QT)) = true := by
  decide +kernel

theorem witQ : witK EQ.G = true := by
  decide +kernel

theorem coverQ : coverK = true := by
  decide +kernel

end CertificateChecks.KernelU62Q

end
