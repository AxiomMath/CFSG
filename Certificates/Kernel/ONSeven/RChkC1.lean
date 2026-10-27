module

public import Certificates.Kernel.ONSeven.RDataC1
public import Certificates.Data.Kernel.ONSevenR
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONR

open CFSG.KC.ONR CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum

@[expose] noncomputable def c1Res (s : Nat) : Bool := resK C1.N 12 C1.T (cF 1 s) (C1.G s)

#kc_each CertificateChecks.KernelSpor.ONR.c1Res 0 7

#kc_forall_chunks c1Res_all (fun s => c1Res s = true) 7 CertificateChecks.KernelSpor.ONR.c1Res 1

theorem c1_orb : orbK C1.N 12 4 C1.T C1.G C1.D C1.S = true := by quickRfl

set_option maxHeartbeats 0 in
theorem c1_f : fK 2746 1372 343 12 4 2 EC1.T EF1.T C1.G (fun l => C1.G (Nat.add 5 l)) X1 = true := by
  quickRfl

theorem c1_N : Nat.beq C1.N 2746 = true := by quickRfl
theorem c1_EN : Nat.beq EC1.N 1372 = true := by quickRfl
theorem c1_Eng : Nat.beq EC1.ng 4 = true := by quickRfl
theorem c1_FN : Nat.beq EF1.N 343 = true := by quickRfl
theorem c1_Fng : Nat.beq EF1.ng 2 = true := by quickRfl
theorem c1_EG : allN 4 (fun k => Nat.beq (EC1.G k) (C1.G k)) = true := by quickRfl
theorem c1_FG : allN 2 (fun l => Nat.beq (EF1.G l) (C1.G (Nat.add 5 l))) = true := by quickRfl
theorem c1_X : Nat.beq (X1 1) (C1.G 4) = true := by quickRfl
theorem c1_px : powsK 2746 12 (X1 1) X1 7 = true := by quickRfl
theorem c1_Gp : allN 7 (fun k => permB 2746 12 (C1.G k)) = true := by quickRfl
theorem c1_w : szOK 2746 12 = true := by quickRfl

end CertificateChecks.KernelSpor.ONR

end
