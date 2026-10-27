module

public import Certificates.Kernel.SporSch.Tits.Graph2265D
public import Certificates.Kernel.SporSch.Tits.Action2262
public import CFSG.Certificates.Kernel.SporSch.TitsGraphSound
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.CFSGNative.Schreier.Merge

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsGraph

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelSporSch.TitsAction

@[expose] noncomputable def ptsK (v u : Nat) : Bool :=
  bIf(Nat.beq (lpK (3 * v)) u, true, bIf(Nat.beq (lpK (3 * v + 1)) u, true,
    Nat.beq (lpK (3 * v + 2)) u))

theorem kN : nbrK 1755 2925 10 11 12 lpK TitsGN.NB TitsGN.NL TitsGN.PW = true := by quickRfl

theorem kE : allN 1755 (fun u => allN 10 (fun i => strictB (pgW 11 TitsGN.NB (10 * u + i))
    (fun b => strictB (pgW 12 TitsGN.NL (10 * u + i)) (fun v =>
    bAnd(bIf(Nat.beq b u, false, true), bAnd(ptsK v u, ptsK v b)))))) = true := by quickRfl

theorem k01 : (Array.ofFn (n := 10) fun i => pgW 11 TitsGN.NB (10 * 0 + i.val)).contains 1 =
    true := by quickRfl

theorem kI0 : allN 1755 (fun x => Nat.beq (pgW 11 (TitsGS.ST 0) x)
    (if (titsIndiv.take 0).contains x then (titsIndiv.take 0).idxOf x + 1 else 0)) = true := by
  quickRfl
theorem kI1 : allN 1755 (fun x => Nat.beq (pgW 11 (TitsGS.ST 2) x)
    (if (titsIndiv.take 1).contains x then (titsIndiv.take 1).idxOf x + 1 else 0)) = true := by
  quickRfl
theorem kI2 : allN 1755 (fun x => Nat.beq (pgW 11 (TitsGS.ST 7) x)
    (if (titsIndiv.take 2).contains x then (titsIndiv.take 2).idxOf x + 1 else 0)) = true := by
  quickRfl
theorem kI3 : allN 1755 (fun x => Nat.beq (pgW 11 (TitsGS.ST 15) x)
    (if (titsIndiv.take 3).contains x then (titsIndiv.take 3).idxOf x + 1 else 0)) = true := by
  quickRfl
theorem kI4 : allN 1755 (fun x => Nat.beq (pgW 11 (TitsGS.ST 24) x)
    (if (titsIndiv.take 4).contains x then (titsIndiv.take 4).idxOf x + 1 else 0)) = true := by
  quickRfl
theorem kI5 : allN 1755 (fun x => Nat.beq (pgW 11 (TitsGS.ST 32) x)
    (if (titsIndiv.take 5).contains x then (titsIndiv.take 5).idxOf x + 1 else 0)) = true := by
  quickRfl
theorem kI6 : allN 1755 (fun x => Nat.beq (pgW 11 (TitsGS.ST 40) x)
    (if (titsIndiv.take 6).contains x then (titsIndiv.take 6).idxOf x + 1 else 0)) = true := by
  quickRfl

theorem kC0 : numK 1755 11 (TitsGS.ST 0) 1 (TitsGS.REP 0) = true := by quickRfl
theorem kC0' : numK 1755 11 (TitsGS.ST 1) 1 (TitsGS.REP 1) = true := by quickRfl
theorem kC1 : numK 1755 11 (TitsGS.ST 5) 5 (TitsGS.REP 5) = true := by quickRfl
theorem kC1' : numK 1755 11 (TitsGS.ST 6) 5 (TitsGS.REP 6) = true := by quickRfl
theorem kC2 : numK 1755 11 (TitsGS.ST 13) 25 (TitsGS.REP 13) = true := by quickRfl
theorem kC2' : numK 1755 11 (TitsGS.ST 14) 25 (TitsGS.REP 14) = true := by quickRfl
theorem kC3 : numK 1755 11 (TitsGS.ST 22) 86 (TitsGS.REP 22) = true := by quickRfl
theorem kC3' : numK 1755 11 (TitsGS.ST 23) 86 (TitsGS.REP 23) = true := by quickRfl
theorem kC4 : numK 1755 11 (TitsGS.ST 30) 149 (TitsGS.REP 30) = true := by quickRfl
theorem kC4' : numK 1755 11 (TitsGS.ST 31) 149 (TitsGS.REP 31) = true := by quickRfl
theorem kC5 : numK 1755 11 (TitsGS.ST 38) 477 (TitsGS.REP 38) = true := by quickRfl
theorem kC5' : numK 1755 11 (TitsGS.ST 39) 477 (TitsGS.REP 39) = true := by quickRfl
theorem kC6 : numK 1755 11 (TitsGS.ST 46) 1755 (TitsGS.REP 46) = true := by quickRfl
theorem kC6' : numK 1755 11 (TitsGS.ST 47) 1755 (TitsGS.REP 47) = true := by quickRfl

theorem kS0 : Nat.beq (cntK 1755 11 (TitsGS.ST 0) (pgW 11 (TitsGS.ST 0) 1)) 1755 = true := by
  quickRfl
theorem kS1 : Nat.beq (cntK 1755 11 (TitsGS.ST 5) (pgW 11 (TitsGS.ST 5) 3)) 80 = true := by
  quickRfl
theorem kS2 : Nat.beq (cntK 1755 11 (TitsGS.ST 13) (pgW 11 (TitsGS.ST 13) 6)) 8 = true := by
  quickRfl
theorem kS3 : Nat.beq (cntK 1755 11 (TitsGS.ST 22) (pgW 11 (TitsGS.ST 22) 5)) 2 = true := by
  quickRfl
theorem kS4 : Nat.beq (cntK 1755 11 (TitsGS.ST 30) (pgW 11 (TitsGS.ST 30) 12)) 4 = true := by
  quickRfl
theorem kS5 : Nat.beq (cntK 1755 11 (TitsGS.ST 38) (pgW 11 (TitsGS.ST 38) 24)) 4 = true := by
  quickRfl

end CertificateChecks.KernelSporSch.TitsGraph

end
