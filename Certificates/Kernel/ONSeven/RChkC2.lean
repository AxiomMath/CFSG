module

public import Certificates.Kernel.ONSeven.RDataC2
public import Certificates.Data.Kernel.ONSevenR
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONR

open CFSG.KC.ONR CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum

@[expose] noncomputable def c2Res (s : Nat) : Bool := resK C2.N 12 C2.T (cF 2 s) (C2.G s)

#kc_each CertificateChecks.KernelSpor.ONR.c2Res 0 8

#kc_forall_chunks c2Res_all (fun s => c2Res s = true) 8 CertificateChecks.KernelSpor.ONR.c2Res 1

theorem c2_orb : orbK C2.N 12 4 C2.T C2.G C2.D C2.S = true := by quickRfl

set_option maxHeartbeats 0 in
theorem c2_f : fK 2772 1372 343 12 4 3 EC2.T EF2.T C2.G (fun l => C2.G (Nat.add 5 l)) X2 = true := by
  quickRfl

theorem c2_N : Nat.beq C2.N 2772 = true := by quickRfl
theorem c2_EN : Nat.beq EC2.N 1372 = true := by quickRfl
theorem c2_Eng : Nat.beq EC2.ng 4 = true := by quickRfl
theorem c2_FN : Nat.beq EF2.N 343 = true := by quickRfl
theorem c2_Fng : Nat.beq EF2.ng 3 = true := by quickRfl
theorem c2_EG : allN 4 (fun k => Nat.beq (EC2.G k) (C2.G k)) = true := by quickRfl
theorem c2_FG : allN 3 (fun l => Nat.beq (EF2.G l) (C2.G (Nat.add 5 l))) = true := by quickRfl
theorem c2_X : Nat.beq (X2 1) (C2.G 4) = true := by quickRfl
theorem c2_px : powsK 2772 12 (X2 1) X2 7 = true := by quickRfl
theorem c2_Gp : allN 8 (fun k => permB 2772 12 (C2.G k)) = true := by quickRfl
theorem c2_w : szOK 2772 12 = true := by quickRfl

end CertificateChecks.KernelSpor.ONR

end
