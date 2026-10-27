module

public import Certificates.Kernel.HS799102.GlueData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS799102

open CFSG.KC.PCent CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def mulB (x y : Nat) : Nat := pcomp 100 7 (mask 7) x y

@[expose] noncomputable def commB (x y : Nat) : Bool := Nat.beq (mulB x y) (mulB y x)

theorem ch799102_bsift : (siftB (TH.F 0) && siftB (TH.F 1)) = true := by quickRfl

theorem ch799102_bc : (Nat.beq (mulB (TH.F 0) (mulB (TH.F 0) (TH.F 0))) (pidn 100 7) &&
    Nat.beq (mulB (TH.F 1) (mulB (TH.F 1) (TH.F 1))) (pidn 100 7) && commB (TH.F 0) (TH.F 1) &&
    !Nat.beq (TH.F 0) (pidn 100 7) && !Nat.beq (TH.F 1) (pidn 100 7) &&
    !Nat.beq (TH.F 1) (TH.F 0) && !Nat.beq (TH.F 1) (mulB (TH.F 0) (TH.F 0)) &&
    Nat.beq (TH.F 4) (mulB (TH.F 2) (TH.F 3))) = true := by quickRfl

theorem ch799102_bw : allN 4 (fun j => siftB (TH.F (Nat.add 5 j)) &&
    commB (TH.F (Nat.add 5 j)) (TH.F 2) && commB (TH.F (Nat.add 5 j)) (TH.F 3)) = true := by
  quickRfl

theorem ch799102_bcomm : (Nat.beq (commP 100 7 (TH.F 5) (TH.F 6)) (TH.F 0) &&
    Nat.beq (commP 100 7 (TH.F 7) (TH.F 8)) (TH.F 1)) = true := by quickRfl

end CertificateChecks.KernelHS799102

end
