module

public import Certificates.Data.Kernel.SporSch.LyFiveLane
public import Certificates.Kernel.SporSch.Ly.BSData
import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.SporSch.Ly.FiveLanesGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kc_eval CertificateChecks.KernelSporSch.LyFL D CertificateChecks.KernelSporSch.LyFiveLanesGen.lanesStep

namespace CertificateChecks.KernelSporSch.LyFL

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy CFSG.KC.LyFiveLane
open CFSG.RankThree.Native CertificateChecks.KernelSporSch.LyBS

@[expose] noncomputable def pw (M e : Nat) : Nat := powR 5 12 1332 111 8 L H CM RM ONE M e

@[expose] noncomputable def R0 : List Nat := ((List.replicate 65 ONE).set 1 A).set 2 B

@[expose] noncomputable def LT (z : Int) : Nat :=
  if z = 1 then D.AA else if z = 2 then D.BB else if z = -1 then D.AI else D.BI

@[expose] noncomputable def wordL (w : List Int) : Nat := w.foldl (fun acc z => mul acc (LT z)) ONE

@[expose] noncomputable def V (i : Nat) : Nat := [D.V0, D.V1, D.V2, D.V3].getD i ONE

@[expose] noncomputable def nfL (c : Nat) (e : Fin 4 → Nat) : Nat :=
  mul (mul (mul (mul (pw (V 3) (e 3)) (pw (V 2) (e 2))) (pw (V 1) (e 1))) (pw (V 0) (e 0)))
    (pw D.XX c)

theorem idx : insOK 65 lyFiveProg = true := by decide +kernel

@[expose] noncomputable def runOK : Bool :=
  (fun r => bAnd(Nat.beq (r.getD 1 0) D.AA, Nat.beq (r.getD 2 0) D.BB)) (runL mul pw lyFiveProg R0)

theorem run : runOK = true := by quickRfl

theorem powAI : Nat.beq (pw D.AA 24) D.AI = true := by quickRfl
theorem powBI : Nat.beq (pw D.BB 7) D.BI = true := by quickRfl
theorem powX : Nat.beq (pw D.AA 5) D.XX = true := by quickRfl

theorem word0 : Nat.beq (wordL (lyFiveVWords 0)) D.V0 = true := by quickRfl
theorem word1 : Nat.beq (wordL (lyFiveVWords 1)) D.V1 = true := by quickRfl
theorem word2 : Nat.beq (wordL (lyFiveVWords 2)) D.V2 = true := by quickRfl
theorem word3 : Nat.beq (wordL (lyFiveVWords 3)) D.V3 = true := by quickRfl

end CertificateChecks.KernelSporSch.LyFL

end
