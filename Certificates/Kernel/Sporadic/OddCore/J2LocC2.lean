
module

public import Certificates.Kernel.Sporadic.OddCore.J2Loc
public import Certificates.Data.Kernel.Spor.PEnumR
public import Certificates.Data.Kernel.Spor.MulHF
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J2Loc

@[expose] def CQ : List Nat := [0, 1477]

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

theorem c2E0 : slK J2C2.cnt (CFSG.KS.PEnumR.penumPtR 315 9 (mask 9) J2C2.GI 4 J2C2.cnt J2C2.T
    J2C2.PL J2C2.POS J2C2.SRT J2C2.SRI) 0 960 = true := by quickRfl
theorem c2E1 : slK J2C2.cnt (CFSG.KS.PEnumR.penumPtR 315 9 (mask 9) J2C2.GI 4 J2C2.cnt J2C2.T
    J2C2.PL J2C2.POS J2C2.SRT J2C2.SRI) 960 960 = true := by quickRfl

theorem c2H0 : slK J2C2.cnt (hsortPtKF 315 9 (mask 9) J2C2.cnt J2C2.T J2C2.HS J2C2.HSI) 0 1920 =
    true := by quickRfl

@[expose] noncomputable def clIx (c : Nat) : Bool :=
  strictB (r32 J2C2Cl c) (fun q => bAnd(Nat.blt q J2C2.cnt,
    bIf(Nat.blt (Nat.mod c 8) 4,
      Nat.beq q (r32 J2C2.POS (Nat.add (Nat.mul (Nat.div c 8) 4) (Nat.mod c 8))),
      Nat.beq (r32 J2C2.POS (Nat.add (Nat.mul q 4) (Nat.sub (Nat.mod c 8) 4))) (Nat.div c 8))))

theorem c2Cl0 : slK (Nat.mul J2C2.cnt 8) clIx 0 15360 = true := by quickRfl

@[expose] noncomputable def qComm (i : Nat) : Bool :=
  strictB (J2C2.T i) (fun y => allN 5 (fun j => eq22 315 9 (mask 9) y (J2Q.GI j) (J2Q.GI j) y))

@[expose] noncomputable def lmemK (l : List Nat) (i : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => bIf(Nat.beq i x, true, ih)) l

@[expose] noncomputable def qOK (i : Nat) : Bool :=
  bIf(qComm i, lmemK CQ i, bIf(lmemK CQ i, false, true))

theorem qC0 : slK J2C2.cnt qOK 0 1920 = true := by quickRfl

theorem cq_cnt : Nat.beq (cntBelowK J2C2.cnt (lmemK CQ) 30) 2 = true := by quickRfl

end CertificateChecks.KernelSpor.J2Loc

end
