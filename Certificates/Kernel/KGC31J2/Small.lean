module

public import Certificates.Kernel.KGC31J2.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Quasithin.Vol2.KGFactC31ActCheck
public import CFSG.Sporadic.Schreier.CountSpec
public import CFSG.Sporadic.Schreier.PairJ2Cert
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public import Certificates.Data.Kernel.KGC31PGrid

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31J2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KC.Child3 CFSG.KC.J2Enum
open CertificateChecks.KernelSporSch

theorem kOrd5a : pord 315 9 5 X5a = true := by quickRfl
theorem kOrd5b : pord 315 9 5 X5b = true := by quickRfl
theorem kOrd7 : pord 315 9 7 X7 = true := by quickRfl

theorem kComm : Nat.beq (pc 315 9 X5a X5b) (pc 315 9 X5b X5a) = true := by quickRfl

theorem kGrid : pgridInj 315 9 X5a X5b 5 = true := by quickRfl

theorem kN : Nat.beq RJ.N 2835 = true := by quickRfl

theorem kCS : (Nat.beq RJ.CS.length 2 && Nat.beq (lget RJ.CS 0) 2520 &&
    Nat.beq (lget RJ.CS 1) 315) = true := by quickRfl

theorem kOff : offOK RJ.CS RJ.OFF RJ.N = true := by quickRfl

theorem kGP : (Nat.beq (RJ.GP 0) (PJ2.S 0) && Nat.beq (RJ.GP 1) (PJ2.S 1) &&
    Nat.beq (RJ.GIP 0) (PJ2.SI 0) && Nat.beq (RJ.GIP 1) (PJ2.SI 1)) = true := by quickRfl

@[expose] noncomputable def repOK (i : Nat) : Bool :=
  canonK 315 9 (mask 9) (315 * 9) (RJ.E (lget RJ.OFF i)) &&
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PJ2.LR PJ2.TRI PJ2.BP 3 0 (RJ.E (lget RJ.OFF i)) &&
    permOK 315 9 (mask 9) (315 * 9) (RJ.E (lget RJ.OFF i)) (pinv 315 9 (RJ.E (lget RJ.OFF i))) &&
    pord 315 9 2 (RJ.E (lget RJ.OFF i))

theorem kRep0 : repOK 0 = true := by quickRfl
theorem kRep1 : repOK 1 = true := by quickRfl

theorem kLev : (Nat.beq (rcnt (PJ2.LR 0)) 315 && Nat.beq (rcnt (PJ2.LR 1)) 160 &&
    Nat.beq (rcnt (PJ2.LR 2)) 12) = true := by quickRfl

theorem kR : (canonK 315 9 (mask 9) (315 * 9) (PJ2.S 0) &&
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PJ2.LR PJ2.TRI PJ2.BP 3 0 (PJ2.S 0) &&
    canonK 315 9 (mask 9) (315 * 9) (PJ2.S 1) &&
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PJ2.LR PJ2.TRI PJ2.BP 3 0 (PJ2.S 1)) = true := by
  quickRfl

theorem kE0len : Nat.beq E0.length 315 = true := by quickRfl

theorem kTot : Nat.beq (fld20 (sumF 315 (lget E0)) 0) 2835 = true := by quickRfl

end CertificateChecks.KernelKGC31J2

end
