module

public import Certificates.Kernel.J2F3.Data
public import Certificates.Data.Kernel.SporSch.MathieuOC
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2F3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.SporSch.BPW CFSG.KS.SporSch.MOC
open CertificateChecks.KernelSpor Certificates.Odd87F3.J2

@[expose] noncomputable def gP1 : List Nat := [J2CentT.F 10, J2CentT.F 11, J2CentT.F 12]

@[expose] noncomputable def gI1 : List Nat := [J2CentI 10, J2CentI 11, J2CentI 12]

@[expose] noncomputable def gP2 : List Nat :=
  [J2CentT.F 18, J2CentT.F 19, J2CentT.F 20, J2CentT.F 21, J2CentT.F 22]

@[expose] noncomputable def gI2 : List Nat :=
  [J2CentI 18, J2CentI 19, J2CentI 20, J2CentI 21, J2CentI 22]

@[expose] noncomputable def gP3 : List Nat := [J2CentT.F 32, J2CentT.F 33, J2CentT.F 34, J2CentT.F 35]

@[expose] noncomputable def gI3 : List Nat := [J2CentI 32, J2CentI 33, J2CentI 34, J2CentI 35]

@[expose] noncomputable def wordsOK (gP gI : List Nat) (ws : List (List Int)) (P PI : List Nat)
    (e : Nat) : Bool :=
  bAnd(Nat.beq P.length ws.length, bAnd(Nat.beq PI.length ws.length,
    allN ws.length (fun i => bAnd(Nat.beq (P.getD i 0) (wordK 315 9 gP gI (ws.getD i [])),
      bAnd(canonK 315 9 (mask 9) (315 * 9) (P.getD i 0),
      bAnd(Nat.beq (PI.getD i 0) (pinvS 315 9 (mask 9) (P.getD i 0)),
        Nat.beq (powK 315 9 (mask 9) (pidn 315 9) (P.getD i 0) e) (pidn 315 9)))))))

theorem ch5165w13 : wordsOK gP1 gI1 oddWordsR1_3 (og1.getD 0 []) (og1I.getD 0 []) 3 = true := by
  quickRfl

theorem ch5165w17 : wordsOK gP1 gI1 oddWordsR1_7 (og1.getD 2 []) (og1I.getD 2 []) 3 = true := by
  quickRfl

theorem ch5165w23 : wordsOK gP2 gI2 oddWordsR2_3 (og2.getD 0 []) (og2I.getD 0 []) 3 = true := by
  quickRfl

theorem ch5165w25 : wordsOK gP2 gI2 oddWordsR2_5 (og2.getD 1 []) (og2I.getD 1 []) 3 = true := by
  quickRfl

theorem ch5165w27 : wordsOK gP2 gI2 oddWordsR2_7 (og2.getD 2 []) (og2I.getD 2 []) 5 = true := by
  quickRfl

theorem ch5165w33 : wordsOK gP3 gI3 oddWordsR3_3 (og3.getD 0 []) (og3I.getD 0 []) 3 = true := by
  quickRfl

theorem ch5165w35 : wordsOK gP3 gI3 oddWordsR3_5 (og3.getD 1 []) (og3I.getD 1 []) 5 = true := by
  quickRfl

theorem ch5165r1 : candB 9 (J2CentT.F 9) bs rows1 J2R1.T J2R1.cnt 0 1800 = true := by quickRfl

theorem ch5165r2a : candB 9 (J2CentT.F 17) bs rows2 J2R2.T J2R2.cnt 0 2520 = true := by quickRfl

theorem ch5165r2b : candB 9 (J2CentT.F 17) bs rows2 J2R3.T J2R3.cnt 0 315 = true := by quickRfl

theorem ch5165r2c : rowsB 9 (J2CentT.F 17) (pidn 315 9) bs rows2 = true := by quickRfl

theorem ch5165r3a : candB 9 (J2CentT.F 31) bs rows3 J2R2.T J2R2.cnt 0 2520 = true := by quickRfl

theorem ch5165r3b : candB 9 (J2CentT.F 31) bs rows3 J2R3.T J2R3.cnt 0 315 = true := by quickRfl

theorem ch5165r3c : rowsB 9 (J2CentT.F 31) (pidn 315 9) bs rows3 = true := by quickRfl

end CertificateChecks.KernelJ2F3

end
