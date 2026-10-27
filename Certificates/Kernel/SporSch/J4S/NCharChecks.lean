module

public import Certificates.Kernel.SporSch.J4S.InvC
public import Certificates.Data.Kernel.SporSch.J4SNChar
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.Schreier.J4SNCharData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Schreier.J4SInvCheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J4NChar

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11
open CFSG.Sporadic.J4Schreier
open CertificateChecks.KernelSporSch

theorem fw : allN 25 (fun c => bAnd(forestK J4IC.T uClasses[c]!,
    witK J4E.T uClasses[c]! uWitness[c]!)) = true := by quickRfl

theorem cov : coverK J4E.T uClasses = true := by quickRfl

theorem x1 : Nat.beq (fixCntK (J4E.T 118)) 128 = true := by quickRfl
theorem x2 : Nat.beq (fixCntK (J4E.T 448)) 128 = true := by quickRfl
theorem x3 : Nat.beq (fixCntK (J4E.T 502)) 128 = true := by quickRfl

theorem cm1 : Nat.beq (compK (J4E.T 448) (J4E.T 502)) (J4E.T 118) = true := by quickRfl
theorem cm2 : Nat.beq (compK (J4E.T 118) (J4E.T 448)) (J4E.T 502) = true := by quickRfl
theorem cm3 : Nat.beq (compK (J4E.T 118) (J4E.T 118)) pidK = true := by quickRfl
theorem cm4 : Nat.beq (compK (J4E.T 448) (J4E.T 448)) pidK = true := by quickRfl

theorem cj : allN 4 (fun i => bAnd(Nat.beq (ent 10 (J4IC.T i) 118) 118,
    bAnd(bIf(Nat.beq (ent 10 (J4IC.T i) 448) 448, true, Nat.beq (ent 10 (J4IC.T i) 448) 502),
    bAnd(bIf(Nat.beq (ent 10 (J4IC.T i) 502) 448, true, Nat.beq (ent 10 (J4IC.T i) 502) 502),
      Bool.not (Nat.beq (ent 10 (J4IC.T i) 448) (ent 10 (J4IC.T i) 502)))))) = true := by
  quickRfl

theorem ex : Nat.beq (ent 10 (J4IC.T 0) 448) 502 = true := by quickRfl

theorem f2 : Nat.beq (fix2CntK (J4E.T 118) (J4E.T 448)) 32 = true := by quickRfl

theorem quad : allN 4 (fun a => allN 4 (fun b => allN 2048 (fun v =>
    quadK (J4E.T (k4 a)) (J4E.T (k4 b)) v))) = true := by quickRfl

theorem prod : allN 4 (fun a => allN 4 (fun b =>
    Nat.beq (compK (J4E.T (k4 a)) (J4E.T (k4 b))) (J4E.T (k4 (Nat.xor a b))))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.J4NChar

end
