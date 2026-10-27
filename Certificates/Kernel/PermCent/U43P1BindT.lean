module

public import Certificates.Kernel.PermCent.U43P1Tab
public import Certificates.Data.Kernel.PermCent.U43P1Chk

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelPermCent.U43P1

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.KC.Enum CFSG.KS

theorem bindsT :
    (((List.range 6).all fun k => gensOK (tM1a.getD k []) (tM1aG k) &&
        Nat.beq (tM1aT k 0) (pidn 820 10)) &&
      ((List.range 4).all fun k => gensOK (tIa.getD k []) (tIaG k) &&
        Nat.beq (tIaT k 0) (pidn 820 10))) = true ∧
    TM0.N = 16 ∧ TM1.N = 32 ∧ TM2.N = 32 ∧ TM3.N = 32 ∧ TM4.N = 32 ∧ TM5.N = 32 ∧
    TI0.N = 16 ∧ TI1.N = 32 ∧ TI2.N = 32 ∧ TI3.N = 32 ∧
    TM0.ng = 3 ∧ TM1.ng = 4 ∧ TM2.ng = 4 ∧ TM3.ng = 3 ∧ TM4.ng = 4 ∧ TM5.ng = 3 ∧
    TI0.ng = 2 ∧ TI1.ng = 3 ∧ TI2.ng = 3 ∧ TI3.ng = 3 := by
  decide +kernel

end CertificateChecks.KernelPermCent.U43P1

end
