module

public import Certificates.Kernel.Sporadic.Fi24P7.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public noncomputable section

namespace CFSG.KD.Fi24P7

open CFSG.KC.Loop CFSG.KC.Fi24Fix CFSG.KD.Fi24G2e

@[expose] def pow7 (M : Nat) : Nat :=
  strictN (CFSG.KD.BrFi24.MUL M M) (fun M2 => strictN (CFSG.KD.BrFi24.MUL M2 M2) (fun M4 =>
    CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.MUL M4 M2) M))

@[expose] def pow3 (M : Nat) : Nat :=
  strictN (CFSG.KD.BrFi24.MUL M M) (fun M2 => CFSG.KD.BrFi24.MUL M2 M)

theorem MS.s0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (J.S0 ++ J.S0 ++ J.S0) CFSG.KD.BrFi24.ONE)
    CFSG.KD.BrFi24.ONE = true := by quickRfl

theorem MS.s1 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (J.S1 ++ J.S1 ++ J.S1) CFSG.KD.BrFi24.ONE)
    CFSG.KD.BrFi24.ONE = true := by quickRfl

theorem MS.s2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (J.S2 ++ J.S2 ++ J.S2) CFSG.KD.BrFi24.ONE)
    CFSG.KD.BrFi24.ONE = true := by quickRfl

theorem MS.s3 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (J.S3 ++ J.S3 ++ J.S3) CFSG.KD.BrFi24.ONE)
    CFSG.KD.BrFi24.ONE = true := by quickRfl

theorem MS.z3 : Nat.beq (pow3 (MX 32)) CFSG.KD.BrFi24.ONE = true := by quickRfl

theorem MS.a0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG
    (J.A0 ++ J.A0 ++ J.A0 ++ J.A0 ++ J.A0 ++ J.A0 ++ J.A0) CFSG.KD.BrFi24.ONE)
    CFSG.KD.BrFi24.ONE = true := by quickRfl

theorem MS.b0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG
    (J.B0 ++ J.B0 ++ J.B0 ++ J.B0 ++ J.B0 ++ J.B0 ++ J.B0) CFSG.KD.BrFi24.ONE)
    CFSG.KD.BrFi24.ONE = true := by quickRfl

theorem MS.a0s : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (J.A0 ++ J.S0) CFSG.KD.BrFi24.ONE)
    (wordMul CFSG.KD.BrFi24.MUL LG (J.S0 ++ J.A0) CFSG.KD.BrFi24.ONE) = true := by quickRfl

theorem MS.b0s : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (J.B0 ++ J.S0) CFSG.KD.BrFi24.ONE)
    (wordMul CFSG.KD.BrFi24.MUL LG (J.S0 ++ J.B0) CFSG.KD.BrFi24.ONE) = true := by quickRfl

theorem MS.t2s : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (J.T2 ++ J.S2) CFSG.KD.BrFi24.ONE)
    (wordMul CFSG.KD.BrFi24.MUL LG (J.S2 ++ J.T2) CFSG.KD.BrFi24.ONE) = true := by quickRfl

theorem MS.a2 : Nat.beq (pow7 (MX 0)) CFSG.KD.BrFi24.ONE = true := by quickRfl

theorem MS.a4 : Nat.beq (pow7 (MX 10)) CFSG.KD.BrFi24.ONE = true := by quickRfl

theorem MS.b4 : Nat.beq (pow7 (MX 21)) CFSG.KD.BrFi24.ONE = true := by quickRfl

theorem MS.a2s : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG J.S2 (MX 0))
    (CFSG.KD.BrFi24.MUL (MX 0) (wordMul CFSG.KD.BrFi24.MUL LG J.S2 CFSG.KD.BrFi24.ONE)) = true := by
  quickRfl

theorem MS.a4s : Nat.beq (CFSG.KD.BrFi24.MUL (MX 32) (MX 10)) (CFSG.KD.BrFi24.MUL (MX 10) (MX 32)) =
    true := by quickRfl

theorem MS.b4s : Nat.beq (CFSG.KD.BrFi24.MUL (MX 32) (MX 21)) (CFSG.KD.BrFi24.MUL (MX 21) (MX 32)) =
    true := by quickRfl

end CFSG.KD.Fi24P7

end
