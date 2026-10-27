module

public import Certificates.Kernel.Sporadic.Q3A.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Q3AK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)
local notation "inv" => invEqK 1782 11 (mask 11) (1782 * 11)

@[expose] noncomputable def W0 : Nat := SuzTwG 6
@[expose] noncomputable def TAU : Nat := Q3ATau.F 0
@[expose] noncomputable def RH0 : Nat := Q3ARho0.F 0
@[expose] noncomputable def S1 : Nat := SuzMGS1.F 0
@[expose] noncomputable def S2 : Nat := SuzMGS2.F 0
@[expose] noncomputable def ST (k : Nat) : Nat :=
  nIf(Nat.beq k 0, Q3ASt0.F 0, nIf(Nat.beq k 1, Q3ASt1.F 0, Q3ASt2.F 0))
@[expose] noncomputable def RHO2 : Nat := pc W0 (pc RHO (Q3AI 10))

@[expose] noncomputable def oparK (y : Nat) : Nat := hx Q3AOP.F y
@[expose] noncomputable def olabK (y : Nat) : Nat := hx Q3AOL.F y
@[expose] noncomputable def odepK (y : Nat) : Nat := hx Q3AOD.F y

@[expose] noncomputable def otOK (y : Nat) : Bool :=
  strictB (oparK y) fun p => bIf(Nat.beq p 22880, true,
    bIf(Nat.beq (odepK y) 0, bIf(Nat.beq y 2622, true, Nat.beq y 2158),
      bAnd(Nat.blt p 22880, bAnd(Nat.blt (oparK p) 22880, bAnd(Nat.blt (odepK p) (odepK y),
        bAnd(Nat.blt (olabK y) 3, Nat.beq (actK (ST (olabK y)) p) y))))))

theorem tCan : bAnd(cn W0, bAnd(cn TAU, bAnd(cn RH0, bAnd(cn S1, bAnd(cn S2,
    bAnd(cn (ST 0), bAnd(cn (ST 1), cn (ST 2)))))))) = true := by quickRfl

theorem tInv : bAnd(inv W0 (Q3AI 10), bAnd(inv TAU (Q3AI 5), bAnd(inv RH0 (Q3AI 6),
    bAnd(inv S1 (Q3AI 11), bAnd(inv S2 (Q3AI 12), bAnd(inv (ST 0) (Q3AI 7),
    bAnd(inv (ST 1) (Q3AI 8), inv (ST 2) (Q3AI 9)))))))) = true := by quickRfl

theorem tMemA : bAnd(OddCore.msift W0, bAnd(OddCore.msift TAU, bAnd(OddCore.msift RH0,
    OddCore.msift S1))) = true := by quickRfl

theorem tMemB : bAnd(OddCore.msift S2, bAnd(OddCore.msift (ST 0), bAnd(OddCore.msift (ST 1),
    OddCore.msift (ST 2)))) = true := by quickRfl

theorem tAct : bAnd(Nat.beq (actK W0 0) 58, bAnd(Nat.beq (actK RH0 58) 2622,
    bAnd(Nat.beq (actK S1 58) 2158, bAnd(Nat.beq (frootK 58) 10,
    bAnd(Nat.beq (actK (pidn 1782 11) 58) 58, bAnd(Nat.beq (actK W0 58) 0,
    bAnd(Nat.beq (actK TAU 0) 58, bAnd(Nat.beq (actK TAU 58) 0, bAnd(Nat.beq (actK TAU 2622) 2622,
    bAnd(Nat.beq (actK RH0 0) 58, bAnd(Nat.beq (actK RH0 2622) 0,
    bAnd(Nat.beq (actK S1 0) 0, bAnd(Nat.beq (actK S1 2158) 58,
    bAnd(Nat.beq (actK S2 0) 58, bAnd(Nat.beq (actK S2 58) 0, Nat.beq (actK S2 2158) 2158))))))))))))))) =
    true := by quickRfl

theorem tStab : allN 3 (fun k => bAnd(Nat.beq (actK (ST k) 0) 0, Nat.beq (actK (ST k) 58) 58)) =
    true := by quickRfl

theorem tRel : Nat.beq (pc (pc RH0 (pc RHO2 (Q3AI 6))) (pc RHO2 RHO)) (pidn 1782 11) = true := by
  quickRfl

theorem tForest : allN 22880 otOK = true := by quickRfl

theorem tCI : Nat.beq (Q3ACI 1536) (cIA 58) = true := by quickRfl

theorem tCommon : allN 486 (fun t => strictB (n0K t) fun y =>
    bIf(adjK (Q3ACI 1536) y, Nat.blt (oparK y) 22880, true)) = true := by quickRfl

end CertificateChecks.KernelSpor.Q3AK

end
