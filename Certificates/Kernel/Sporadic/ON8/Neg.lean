module

public import Certificates.Kernel.Sporadic.ON8.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.ON5.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON8

open CFSG.KC.Enum CFSG.KS.ON CFSG.KS.IE

@[expose] noncomputable def IDbad (i : Nat) : Nat := nIf(Nat.beq i 154, Nat.succ (IDf i), IDf i)

theorem neg_d : Bool.not (ieSl dcK sp IDbad PD LD QD 4 144 0 16) = true := by quickRfl

theorem neg_a : Bool.not (strictB (Nat.succ (tab ON8T.AS (asl 0))) fun a =>
    allN 154 fun t => Nat.beq (cjI (asl 0) t) (imgAt IDf (Nat.sub a 1) t)) = true := by quickRfl

theorem neg_t : Bool.not (allN 154 fun t => Nat.beq (imgAt IHf 1 t) (sp t)) = true := by quickRfl

end CertificateChecks.KernelSpor.ON8

end
