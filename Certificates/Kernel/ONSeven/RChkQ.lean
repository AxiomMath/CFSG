module

public import Certificates.Kernel.ONSeven.RDataQ
public import Certificates.Data.Kernel.ONSevenR
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONR

open CFSG.KC.ONR CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum

@[expose] noncomputable def qRes (s : Nat) : Bool := resK Q.N 10 Q.T (qF s) (Q.G s)

#kc_each CertificateChecks.KernelSpor.ONR.qRes 0 59

#kc_forall_chunks qRes_all (fun s => qRes s = true) 59 CertificateChecks.KernelSpor.ONR.qRes 1

theorem q_orb : orbK Q.N 10 2 Q.T Q.G Q.D Q.S = true := by quickRfl

theorem q_chk : qK Q.N 10 EQ.T QL = true := by quickRfl

theorem q_N : Nat.beq Q.N 687 = true := by quickRfl
theorem q_EN : Nat.beq EQ.N 343 = true := by quickRfl
theorem q_Eng : Nat.beq EQ.ng 2 = true := by quickRfl
theorem q_G0 : Nat.beq (EQ.G 0) (Q.G 0) = true := by quickRfl
theorem q_G1 : Nat.beq (EQ.G 1) (Q.G 1) = true := by quickRfl
theorem q_Gp : allN 2 (fun k => permB 687 10 (Q.G k)) = true := by quickRfl
theorem q_w : szOK 687 10 = true := by quickRfl
theorem q_L : allN 57 (fun j => Nat.beq (QL (Nat.add (Nat.mul 8 j) 1)) (Q.G (Nat.add 2 j))) = true := by
  quickRfl

end CertificateChecks.KernelSpor.ONR

end
