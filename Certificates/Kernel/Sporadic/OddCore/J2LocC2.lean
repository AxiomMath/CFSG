
module

public import Certificates.Kernel.Sporadic.OddCore.J2Loc
meta import Certificates.Kernel.Sporadic.OddCore.J2Loc
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J2Loc

meta def cqM : List Nat :=
  (List.range c2RecM.size).filter fun i => qM.all fun g =>
    CFSG.PSL3Four.Native.comp 315 c2RecM[i]! g == CFSG.PSL3Four.Native.comp 315 g c2RecM[i]!

#knatlist CertificateChecks.KernelSpor.J2Loc.CQ cqM

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

theorem c2E0 : penumSlK 315 9 (mask 9) (315 * 9) true J2C2.G J2C2.GI 4 J2C2.cnt J2C2.T J2C2.PL
    J2C2.POS J2C2.SRT J2C2.SRI 0 240 = true := by quickRfl
theorem c2E1 : penumSlK 315 9 (mask 9) (315 * 9) true J2C2.G J2C2.GI 4 J2C2.cnt J2C2.T J2C2.PL
    J2C2.POS J2C2.SRT J2C2.SRI 240 240 = true := by quickRfl
theorem c2E2 : penumSlK 315 9 (mask 9) (315 * 9) true J2C2.G J2C2.GI 4 J2C2.cnt J2C2.T J2C2.PL
    J2C2.POS J2C2.SRT J2C2.SRI 480 240 = true := by quickRfl
theorem c2E3 : penumSlK 315 9 (mask 9) (315 * 9) true J2C2.G J2C2.GI 4 J2C2.cnt J2C2.T J2C2.PL
    J2C2.POS J2C2.SRT J2C2.SRI 720 240 = true := by quickRfl
theorem c2E4 : penumSlK 315 9 (mask 9) (315 * 9) true J2C2.G J2C2.GI 4 J2C2.cnt J2C2.T J2C2.PL
    J2C2.POS J2C2.SRT J2C2.SRI 960 240 = true := by quickRfl
theorem c2E5 : penumSlK 315 9 (mask 9) (315 * 9) true J2C2.G J2C2.GI 4 J2C2.cnt J2C2.T J2C2.PL
    J2C2.POS J2C2.SRT J2C2.SRI 1200 240 = true := by quickRfl
theorem c2E6 : penumSlK 315 9 (mask 9) (315 * 9) true J2C2.G J2C2.GI 4 J2C2.cnt J2C2.T J2C2.PL
    J2C2.POS J2C2.SRT J2C2.SRI 1440 240 = true := by quickRfl
theorem c2E7 : penumSlK 315 9 (mask 9) (315 * 9) true J2C2.G J2C2.GI 4 J2C2.cnt J2C2.T J2C2.PL
    J2C2.POS J2C2.SRT J2C2.SRI 1680 240 = true := by quickRfl

theorem c2H0 : slK J2C2.cnt (hsortPtK 315 9 (mask 9) J2C2.cnt J2C2.T J2C2.HS J2C2.HSI) 0 480 =
    true := by quickRfl
theorem c2H1 : slK J2C2.cnt (hsortPtK 315 9 (mask 9) J2C2.cnt J2C2.T J2C2.HS J2C2.HSI) 480 480 =
    true := by quickRfl
theorem c2H2 : slK J2C2.cnt (hsortPtK 315 9 (mask 9) J2C2.cnt J2C2.T J2C2.HS J2C2.HSI) 960 480 =
    true := by quickRfl
theorem c2H3 : slK J2C2.cnt (hsortPtK 315 9 (mask 9) J2C2.cnt J2C2.T J2C2.HS J2C2.HSI) 1440 480 =
    true := by quickRfl

theorem c2Cl0 : slK (Nat.mul J2C2.cnt 8)
    (findPtK J2C2.cnt J2C2.T (prodQK 315 9 (mask 9) 8 J2C2.T (bothK 4 J2C2.GI J2C2I)) J2C2Cl)
    0 1920 = true := by quickRfl
theorem c2Cl1 : slK (Nat.mul J2C2.cnt 8)
    (findPtK J2C2.cnt J2C2.T (prodQK 315 9 (mask 9) 8 J2C2.T (bothK 4 J2C2.GI J2C2I)) J2C2Cl)
    1920 1920 = true := by quickRfl
theorem c2Cl2 : slK (Nat.mul J2C2.cnt 8)
    (findPtK J2C2.cnt J2C2.T (prodQK 315 9 (mask 9) 8 J2C2.T (bothK 4 J2C2.GI J2C2I)) J2C2Cl)
    3840 1920 = true := by quickRfl
theorem c2Cl3 : slK (Nat.mul J2C2.cnt 8)
    (findPtK J2C2.cnt J2C2.T (prodQK 315 9 (mask 9) 8 J2C2.T (bothK 4 J2C2.GI J2C2I)) J2C2Cl)
    5760 1920 = true := by quickRfl
theorem c2Cl4 : slK (Nat.mul J2C2.cnt 8)
    (findPtK J2C2.cnt J2C2.T (prodQK 315 9 (mask 9) 8 J2C2.T (bothK 4 J2C2.GI J2C2I)) J2C2Cl)
    7680 1920 = true := by quickRfl
theorem c2Cl5 : slK (Nat.mul J2C2.cnt 8)
    (findPtK J2C2.cnt J2C2.T (prodQK 315 9 (mask 9) 8 J2C2.T (bothK 4 J2C2.GI J2C2I)) J2C2Cl)
    9600 1920 = true := by quickRfl
theorem c2Cl6 : slK (Nat.mul J2C2.cnt 8)
    (findPtK J2C2.cnt J2C2.T (prodQK 315 9 (mask 9) 8 J2C2.T (bothK 4 J2C2.GI J2C2I)) J2C2Cl)
    11520 1920 = true := by quickRfl
theorem c2Cl7 : slK (Nat.mul J2C2.cnt 8)
    (findPtK J2C2.cnt J2C2.T (prodQK 315 9 (mask 9) 8 J2C2.T (bothK 4 J2C2.GI J2C2I)) J2C2Cl)
    13440 1920 = true := by quickRfl

@[expose] noncomputable def qComm (i : Nat) : Bool :=
  strictB (J2C2.T i) (fun y => allN 5 (fun j => Nat.beq (pc y (J2Q.GI j)) (pc (J2Q.GI j) y)))

@[expose] noncomputable def lmemK (l : List Nat) (i : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => bIf(Nat.beq i x, true, ih)) l

@[expose] noncomputable def qOK (i : Nat) : Bool :=
  bIf(qComm i, lmemK CQ i, bIf(lmemK CQ i, false, true))

theorem qC0 : slK J2C2.cnt qOK 0 320 = true := by quickRfl
theorem qC1 : slK J2C2.cnt qOK 320 320 = true := by quickRfl
theorem qC2 : slK J2C2.cnt qOK 640 320 = true := by quickRfl
theorem qC3 : slK J2C2.cnt qOK 960 320 = true := by quickRfl
theorem qC4 : slK J2C2.cnt qOK 1280 320 = true := by quickRfl
theorem qC5 : slK J2C2.cnt qOK 1600 320 = true := by quickRfl

theorem cq_cnt : Nat.beq (cntBelowK J2C2.cnt (lmemK CQ) 30) 2 = true := by quickRfl

end CertificateChecks.KernelSpor.J2Loc

end
