module

public import Certificates.Kernel.ONSeven.RDataC0
public import Certificates.Data.Kernel.ONSevenR
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONR

open CFSG.KC.ONR CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum

@[expose] noncomputable def c0Res (s : Nat) : Bool := resK C0.N 12 C0.T (cF 0 s) (C0.G s)

#kc_each CertificateChecks.KernelSpor.ONR.c0Res 0 7

#kc_forall_chunks c0Res_all (fun s => c0Res s = true) 7 CertificateChecks.KernelSpor.ONR.c0Res 1

theorem c0_orb : orbK C0.N 12 4 C0.T C0.G C0.D C0.S = true := by quickRfl

set_option maxHeartbeats 0 in
theorem c0_f : fK 2746 1372 343 12 4 2 EC0.T EF0.T C0.G (fun l => C0.G (Nat.add 5 l)) X0 = true := by
  quickRfl

theorem c0_N : Nat.beq C0.N 2746 = true := by quickRfl
theorem c0_EN : Nat.beq EC0.N 1372 = true := by quickRfl
theorem c0_Eng : Nat.beq EC0.ng 4 = true := by quickRfl
theorem c0_FN : Nat.beq EF0.N 343 = true := by quickRfl
theorem c0_Fng : Nat.beq EF0.ng 2 = true := by quickRfl
theorem c0_EG : allN 4 (fun k => Nat.beq (EC0.G k) (C0.G k)) = true := by quickRfl
theorem c0_FG : allN 2 (fun l => Nat.beq (EF0.G l) (C0.G (Nat.add 5 l))) = true := by quickRfl
theorem c0_X : Nat.beq (X0 1) (C0.G 4) = true := by quickRfl
theorem c0_px : powsK 2746 12 (X0 1) X0 7 = true := by quickRfl
theorem c0_Gp : allN 7 (fun k => permB 2746 12 (C0.G k)) = true := by quickRfl
theorem c0_w : szOK 2746 12 = true := by quickRfl

end CertificateChecks.KernelSpor.ONR

end
