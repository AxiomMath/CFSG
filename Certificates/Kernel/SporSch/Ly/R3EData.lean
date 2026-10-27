module

public import Certificates.Kernel.SporSch.Ly.BSData
public import CFSG.Sporadic.Schreier.LyCheckR3E
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kly_sylowdata CertificateChecks.KernelSporSch.LySy 8

namespace CertificateChecks.KernelSporSch.LySy

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy
open CFSG.Sporadic.LySchreier.Native
open CertificateChecks.KernelSporSch.LyBS

theorem cnt : Nat.beq c 256 = true := by quickRfl
theorem ns : Nat.beq nS 32 = true := by quickRfl

theorem ugw : allN 5 (fun k => Nat.beq (wordR 5 12 1332 111 8 L H CM RM (CFx 12) (CIx 12) ONE
    ((sylowWords ())[k]!)) (UG k)) = true := by quickRfl
theorem ug5 : Nat.beq (UG 5) A = true := by quickRfl
theorem vUG : allN 6 (fun k => vld (UG k)) = true := by quickRfl
theorem vE0 : allBlk 0 (fun i => vld (E i)) 64 = true := by quickRfl
theorem vE1 : allBlk 64 (fun i => vld (E i)) 64 = true := by quickRfl
theorem vE2 : allBlk 128 (fun i => vld (E i)) 64 = true := by quickRfl
theorem vE3 : allBlk 192 (fun i => vld (E i)) 64 = true := by quickRfl
theorem e0 : Nat.beq (E 0) ONE = true := by quickRfl
theorem srt : allN 256 (fun i => sortB E ST SIT 256 i) = true := by quickRfl
theorem c0 : Nat.beq (C 0) 1 = true := by quickRfl
theorem cN : Nat.beq (C 32) 256 = true := by quickRfl

@[expose] noncomputable def MG2 : Nat :=
  mul (powR 5 12 1332 111 8 L H CM RM ONE (mul HM (E 113)) 7)
    (powR 5 12 1332 111 8 L H CM RM ONE (mul A HM) 4)

theorem vMG2 : vld MG2 = true := by quickRfl

theorem a1 : Nat.beq (mul (mul (mul (UG 2) (UG 1)) (UG 2)) (UG 1)) (E 113) = true := by quickRfl
theorem a2 : Nat.beq (mul (E 113) (E 113)) ONE = true := by quickRfl
theorem a3 : Bool.not (Nat.beq (E 113) ONE) = true := by quickRfl
theorem a4 : Bool.not (Nat.beq (E 113) A) = true := by quickRfl
theorem a5 : Nat.beq (mul A (E 113)) (mul (E 113) A) = true := by quickRfl
theorem a6 : Nat.beq (mul MG2 A) (mul (E 113) MG2) = true := by quickRfl

@[expose] noncomputable def commW (w : List Int) : Bool :=
  strictB (wordR 5 12 1332 111 8 L H CM RM (CFx 12) (CIx 12) ONE w) (fun md =>
    Nat.beq (mul md (E 113)) (mul (E 113) md))

theorem w0 : commW [12] = true := by quickRfl
theorem w1 : commW [6, 6, -12, 8, 10, 9] = true := by quickRfl
theorem w2 : commW [5, 5, 5, 9, 6, 10, -11] = true := by quickRfl
theorem w3 : commW [6, -11] = true := by quickRfl
theorem w4 : commW [-6, 5, -6, -6, 7, 6, 8, 10, 9, 12, 11, 12] = true := by quickRfl
theorem w5 : commW [2, 12, 1, -8, 6, -11, -12] = true := by quickRfl

theorem p1 : Nat.beq (powR 5 12 1332 111 8 L H CM RM ONE (mul (mul (CF 3) ONE) MG2) 18) ONE = true := by
  quickRfl
theorem p2 : Bool.not (Nat.beq (powR 5 12 1332 111 8 L H CM RM ONE (mul (mul (CF 3) A) MG2) 18)
    ONE) = true := by quickRfl
theorem p3 : Bool.not (Nat.beq (powR 5 12 1332 111 8 L H CM RM ONE (mul (mul (CF 3) (E 113)) MG2)
    18) ONE) = true := by quickRfl
theorem p4 : Nat.beq (powR 5 12 1332 111 8 L H CM RM ONE (mul (mul (CF 3) (mul A (E 113))) MG2) 18)
    ONE = true := by quickRfl

end CertificateChecks.KernelSporSch.LySy

end
