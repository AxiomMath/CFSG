module

public import Certificates.Kernel.Ly3085.Omega.Data
public import Certificates.Data.Kernel.LyOmega.Base
public import Certificates.Kernel.Ly3085.O2.Data
public import Certificates.Kernel.SporSch.Ly.SevA
public import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness

@[expose] public section

set_option maxRecDepth 400000

#ks_chars CFSG.KD.LyOm.LyFDT CFSG.Sporadic.LySchreier.Native.formDigitsTxt

namespace CFSG.KD.LyOm

open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL CFSG.KC.Loop
open CertificateChecks.KernelSporSch.LySv (AF AI RA UP DG TT RT)

@[expose] noncomputable def GP : Nat → Nat := pickL [P0, P1, PI0, PI1]

@[expose] noncomputable def GAB : Nat → Nat := pickL [AF 0, AF 1, AI 0, AI 1]

@[expose] noncomputable def GR : Nat → Nat := pickL [R0, R1, Q0, Q1]

@[expose] noncomputable def GK : Nat → Nat := pickL [KQ0, KQ1, KR0, KR1]

@[expose] noncomputable def N2 : Nat := spreadB CFSG.KD.LyO2.C.MS (getRec CFSG.KD.LyO2.KX 2331 0)

@[expose] noncomputable def allL (f : Nat → Bool) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) l

theorem consts : bAnd(bConstsOK BC, sConstsOK SC) = true := by quickRfl

theorem vld : allL (fVld BC) [T, TI, P0, P1, PI0, PI1, Gt0, Gt1, FL, PTA, PTB, PYB, PTT, TTt] = true := by
  quickRfl

theorem tti : Nat.beq (fMul BC T TI) BC.ONEF = true := by quickRfl
theorem tit : Nat.beq (fMul BC TI T) BC.ONEF = true := by quickRfl
theorem gt0 : Nat.beq (fTr (AF 2)) Gt0 = true := by quickRfl
theorem gt1 : Nat.beq (fTr (AF 3)) Gt1 = true := by quickRfl
theorem p0 : Nat.beq (fMul BC T P0) (fMul BC Gt0 T) = true := by quickRfl
theorem p1 : Nat.beq (fMul BC T P1) (fMul BC Gt1 T) = true := by quickRfl
theorem pi0 : Nat.beq (fMul BC P0 PI0) BC.ONEF = true := by quickRfl
theorem pi1 : Nat.beq (fMul BC P1 PI1) BC.ONEF = true := by quickRfl
theorem o2p : bAnd(Nat.beq P0 CFSG.KD.LyO2.P0, bAnd(Nat.beq P1 CFSG.KD.LyO2.P1,
    bAnd(Nat.beq PI0 CFSG.KD.LyO2.PI0, Nat.beq PI1 CFSG.KD.LyO2.PI1))) = true := by quickRfl
theorem fl : digLanesK LyFDT.chars FL 12321 = true := by quickRfl

@[expose] noncomputable def utOK (UT : Nat) (w : List Nat) : Bool :=
  bAnd(validM 5 9324 BC.L7 BC.H7 UT, trOK 7 111 UT (fMul BC (fWord BC GAB BC.ONEF w) UP))

theorem ut1 : utOK UT1 WG1 = true := by quickRfl
theorem ut2 : utOK UT2 WG2 = true := by quickRfl
theorem ut3 : utOK UT3 WG3 = true := by quickRfl
theorem ut4 : utOK UT4 WG4 = true := by quickRfl
theorem root2 : sameSpan BC N2 (bMul BC UT2 T) = true := by quickRfl

@[expose] noncomputable def ppOK (UT PP : Nat) : Bool :=
  bAnd(sVld SC PP, relayOK (bMul BC (bMul BC UT FL) UP) PP)

theorem pp1 : ppOK UT1 PP1 = true := by quickRfl
theorem pp2 : ppOK UT2 PP2 = true := by quickRfl
theorem pp3 : ppOK UT3 PP3 = true := by quickRfl
theorem pp4 : ppOK UT4 PP4 = true := by quickRfl

theorem ss : bAnd(sVld SC SS, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => bAnd(Nat.beq (sEnt SS (Nat.div t 7) (Nat.mod t 7)) (fld(DG, Nat.mul 4 (Nat.add 777 t), 15)),
      ih)) 49) = true := by quickRfl

@[expose] noncomputable def beOK (PP BE : Nat) : Bool :=
  Nat.beq BE (sMul SC (sTr PP) (sMul SC (sTr SS) PP))

theorem be1 : beOK PP1 BE1 = true := by quickRfl
theorem be2 : beOK PP2 BE2 = true := by quickRfl
theorem be3 : beOK PP3 BE3 = true := by quickRfl
theorem be4 : beOK PP4 BE4 = true := by quickRfl

@[expose] noncomputable def rOK (R Q KQ KR : Nat) (ra : Array Nat) : Bool :=
  bAnd(sVld SC R, bAnd(sVld SC Q,
  bAnd(Nat.rec (motive := fun _ => Bool) true
      (fun t ih => bAnd(Nat.beq (sEnt R (Nat.div t 7) (Nat.mod t 7)) (ra[t]!), ih)) 49,
  bAnd(Nat.beq (sMul SC R Q) SC.ONE, bAnd(Nat.beq (sMul SC Q R) SC.ONE,
    bAnd(kronOK Q Q KQ, kronOK R R KR))))))

theorem r0 : rOK R0 Q0 KQ0 KR0 (RA[0]!) = true := by quickRfl
theorem r1 : rOK R1 Q1 KQ1 KR1 (RA[1]!) = true := by quickRfl

@[expose] noncomputable def ofArr (ra : Array Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun t acc => Nat.lor acc (Nat.shiftLeft (ra[t]!) (Nat.mul 11 t))) 49

theorem beta2 : Nat.rec (motive := fun _ => Bool) true (fun j ih => bAnd(
    (fun R => bAnd(sVld SC R, Nat.beq (sMul SC (sTr R) (sMul SC BE2 R)) BE2)) (ofArr (RA[j]!)), ih)) 5
    = true := by quickRfl

@[expose] noncomputable def EL : Nat := fMul BC (fMul BC (fMul BC UP (toBig SS)) (fTr UP)) FL

theorem fixE : bAnd(Nat.rec (motive := fun _ => Bool) true (fun j ih => bAnd(
      Nat.beq (fMul BC (AF (Nat.add j 2)) EL) (fMul BC EL (AF (Nat.add j 2))), ih)) 5,
    Nat.beq (fMul BC TT EL) (fMul BC EL TT)) = true := by quickRfl

theorem formF : bAnd(Nat.beq (fTr FL) FL,
    bAnd(Nat.beq (fMul BC (fMul BC (fTr (AF 0)) FL) (AF 0)) FL,
      Nat.beq (fMul BC (fMul BC (fTr (AF 1)) FL) (AF 1)) FL)) = true := by quickRfl

theorem beta : bAnd(Nat.beq BE1 0,
    bAnd(notB (Nat.beq BE2 BE4),
    bAnd(sVld SC BI2, bAnd(Nat.beq (sMul SC BE2 BI2) SC.ONE,
    bAnd(sVld SC BI4, bAnd(Nat.beq (sMul SC BE4 BI4) SC.ONE,
    bAnd(notB (Nat.beq BE3 0),
    bAnd(sVld SC X3, bAnd(notB (Nat.beq X3 0), Nat.beq (sMul SC X3 BE3) 0))))))))) = true := by
  quickRfl

@[expose] noncomputable def fixBeta (BE : Nat) (w : List Nat) : Bool :=
  Nat.beq (wordR (sBlk SC) GK BE (List.reverse w)) BE

theorem fw3_0 : fixBeta BE3 WF3_0 = true := by quickRfl
theorem fw3_1 : fixBeta BE3 WF3_1 = true := by quickRfl
theorem fw4_0 : fixBeta BE4 WF4_0 = true := by quickRfl
theorem fw4_1 : fixBeta BE4 WF4_1 = true := by quickRfl

@[expose] noncomputable def fixSpan (N : Nat) (w : List Nat) : Bool :=
  sameSpan BC N (bWord BC GP N (List.reverse w))

theorem h2fix0 : fixSpan N2 WH2_0 = true := by quickRfl
theorem h2fix1 : fixSpan N2 WH2_1 = true := by quickRfl

theorem clsP : bAnd(Nat.beq PTA (fWord BC GP BC.ONEF (List.reverse WTA)),
    bAnd(Nat.beq PTB (fWord BC GP BC.ONEF (List.reverse WTB)),
      Nat.beq PYB (fWord BC GP BC.ONEF (List.reverse WYB)))) = true := by quickRfl

theorem clsT : bAnd(Nat.beq (fMul BC T PTT) (fMul BC TTt T), Nat.beq TTt (fTr TT)) = true := by
  quickRfl

theorem clsRT : bAnd(sVld SC RTl,
    bAnd(Nat.rec (motive := fun _ => Bool) true
      (fun t ih => bAnd(Nat.beq (sEnt RTl (Nat.div t 7) (Nat.mod t 7)) (RT[t]!), ih)) 49,
    Nat.beq (fMul BC TT UP) (fMul BC UP (toBig RTl)))) = true := by quickRfl

theorem clsC : bAnd(Nat.beq (sClass SC RTl) 1,
    bAnd(Nat.beq (sClass SC (sWord SC GR SC.ONE WYB)) (Nat.shiftLeft 1 16),
    bAnd(Nat.beq (sClass SC (sWord SC GR SC.ONE WTA)) (Nat.shiftLeft 1 32),
      Nat.beq (sClass SC (sWord SC GR SC.ONE WTB)) (Nat.shiftLeft 1 48)))) = true := by quickRfl

end CFSG.KD.LyOm

end
