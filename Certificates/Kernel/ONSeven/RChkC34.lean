module

public import Certificates.Kernel.ONSeven.RDataC3
public import Certificates.Data.Kernel.ONSevenR
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONR

open CFSG.KC.ONR CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum

@[expose] noncomputable def c3Res (s : Nat) : Bool := resK C3.N 7 C3.T (cF 3 s) (C3.G s)

@[expose] noncomputable def c4Res (s : Nat) : Bool := resK C4.N 7 C4.T (cF 4 s) (C4.G s)

#kc_each CertificateChecks.KernelSpor.ONR.c3Res 0 3
#kc_each CertificateChecks.KernelSpor.ONR.c4Res 0 3

#kc_forall_chunks c3Res_all (fun s => c3Res s = true) 3 CertificateChecks.KernelSpor.ONR.c3Res 1
#kc_forall_chunks c4Res_all (fun s => c4Res s = true) 3 CertificateChecks.KernelSpor.ONR.c4Res 1

theorem c3_orb : orbK C3.N 7 2 C3.T C3.G C3.D C3.S = true := by quickRfl
theorem c4_orb : orbK C4.N 7 2 C4.T C4.G C4.D C4.S = true := by quickRfl

theorem c3_N : Nat.beq C3.N 99 = true := by quickRfl
theorem c3_EN : Nat.beq EC3.N 49 = true := by quickRfl
theorem c3_Eng : Nat.beq EC3.ng 2 = true := by quickRfl
theorem c3_EG : allN 2 (fun k => Nat.beq (EC3.G k) (C3.G k)) = true := by quickRfl
theorem c3_Gp : allN 2 (fun k => permB 99 7 (C3.G k)) = true := by quickRfl
theorem c4_N : Nat.beq C4.N 99 = true := by quickRfl
theorem c4_EN : Nat.beq EC4.N 49 = true := by quickRfl
theorem c4_Eng : Nat.beq EC4.ng 2 = true := by quickRfl
theorem c4_EG : allN 2 (fun k => Nat.beq (EC4.G k) (C4.G k)) = true := by quickRfl
theorem c4_Gp : allN 2 (fun k => permB 99 7 (C4.G k)) = true := by quickRfl
theorem c34_w : szOK 99 7 = true := by quickRfl

end CertificateChecks.KernelSpor.ONR

end
