module

public import Certificates.Kernel.Sporadic.Fi24P7.Data
public import Certificates.Kernel.Sporadic.Fi24Fix.Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Chain

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

theorem MS.z3 : Nat.beq (pow3 (MX 32)) CFSG.KD.BrFi24.ONE = true := by quickRfl

theorem MS.a4s : Nat.beq (CFSG.KD.BrFi24.MUL (MX 32) (MX 10)) (CFSG.KD.BrFi24.MUL (MX 10) (MX 32)) =
    true := by quickRfl

theorem MS.b4s : Nat.beq (CFSG.KD.BrFi24.MUL (MX 32) (MX 21)) (CFSG.KD.BrFi24.MUL (MX 21) (MX 32)) =
    true := by quickRfl

#kc_chain CFSG.KD.Fi24P7 "data/msp.plan.txt" 1664 13259754246569614631

theorem MSp.gS0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [nat_lit 11, nat_lit 10] CFSG.KD.BrFi24.ONE) MSp.GS0 = true := by
  quickRfl

theorem MSp.gS1b : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [nat_lit 2, nat_lit 7, nat_lit 8] CFSG.KD.BrFi24.ONE) MSp.HS1 = true := by
  quickRfl

theorem MSp.gS1a : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [nat_lit 11, nat_lit 10, nat_lit 1] MSp.HS1) MSp.GS1 = true := by
  quickRfl

theorem MSp.gS2b : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [nat_lit 9, nat_lit 6] CFSG.KD.BrFi24.ONE) MSp.HS2 = true := by
  quickRfl

theorem MSp.gS2a : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [nat_lit 11, nat_lit 10] MSp.HS2) MSp.GS2 = true := by
  quickRfl

theorem MSp.gS3b : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [nat_lit 2, nat_lit 4, nat_lit 5] CFSG.KD.BrFi24.ONE) MSp.HS3 = true := by
  quickRfl

theorem MSp.gS3a : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [nat_lit 11, nat_lit 10, nat_lit 1] MSp.HS3) MSp.GS3 = true := by
  quickRfl

theorem MSp.gA0b : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [nat_lit 4, nat_lit 5, nat_lit 6] CFSG.KD.BrFi24.ONE) MSp.HA0 = true := by
  quickRfl

theorem MSp.gA0a : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [nat_lit 1, nat_lit 2, nat_lit 3] MSp.HA0) MSp.GA0 = true := by
  quickRfl

theorem MSp.gB0a : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [nat_lit 8, nat_lit 7, nat_lit 3] MSp.HA0) MSp.GB0 = true := by
  quickRfl

theorem MSp.gT2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [nat_lit 2] CFSG.KD.BrFi24.ONE) MSp.GT2 = true := by
  quickRfl

theorem MSp.S0_val : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG J.S0 CFSG.KD.BrFi24.ONE) MSp.GS0 = true :=
  beq_wordMul_of_eq (w' := [nat_lit 11, nat_lit 10]) rfl MSp.gS0

theorem MSp.S1_val : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG J.S1 CFSG.KD.BrFi24.ONE) MSp.GS1 = true :=
  beq_wordMul_of_eq (w' := [nat_lit 11, nat_lit 10, nat_lit 1] ++ [nat_lit 2, nat_lit 7, nat_lit 8]) rfl (beq_wordMul_append MSp.gS1b MSp.gS1a)

theorem MSp.S2_val : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG J.S2 CFSG.KD.BrFi24.ONE) MSp.GS2 = true :=
  beq_wordMul_of_eq (w' := [nat_lit 11, nat_lit 10] ++ [nat_lit 9, nat_lit 6]) rfl (beq_wordMul_append MSp.gS2b MSp.gS2a)

theorem MSp.S3_val : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG J.S3 CFSG.KD.BrFi24.ONE) MSp.GS3 = true :=
  beq_wordMul_of_eq (w' := [nat_lit 11, nat_lit 10, nat_lit 1] ++ [nat_lit 2, nat_lit 4, nat_lit 5]) rfl (beq_wordMul_append MSp.gS3b MSp.gS3a)

theorem MSp.A0_val : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG J.A0 CFSG.KD.BrFi24.ONE) MSp.GA0 = true :=
  beq_wordMul_of_eq (w' := [nat_lit 1, nat_lit 2, nat_lit 3] ++ [nat_lit 4, nat_lit 5, nat_lit 6]) rfl (beq_wordMul_append MSp.gA0b MSp.gA0a)

theorem MSp.B0_val : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG J.B0 CFSG.KD.BrFi24.ONE) MSp.GB0 = true :=
  beq_wordMul_of_eq (w' := [nat_lit 8, nat_lit 7, nat_lit 3] ++ [nat_lit 4, nat_lit 5, nat_lit 6]) rfl (beq_wordMul_append MSp.gA0b MSp.gB0a)

theorem MSp.T2_val : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG J.T2 CFSG.KD.BrFi24.ONE) MSp.GT2 = true :=
  beq_wordMul_of_eq (w' := [nat_lit 2]) rfl MSp.gT2

theorem MSp.q2A0 : Nat.beq (CFSG.KD.BrFi24.MUL MSp.GA0 MSp.GA0) MSp.Q2A0 = true := by
  quickRfl

theorem MSp.q4A0 : Nat.beq (CFSG.KD.BrFi24.MUL MSp.Q2A0 MSp.Q2A0) MSp.Q4A0 = true := by
  quickRfl

theorem MSp.p7A0 : Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.MUL MSp.Q4A0 MSp.Q2A0) MSp.GA0) CFSG.KD.BrFi24.ONE = true := by
  quickRfl

theorem MSp.q2B0 : Nat.beq (CFSG.KD.BrFi24.MUL MSp.GB0 MSp.GB0) MSp.Q2B0 = true := by
  quickRfl

theorem MSp.q4B0 : Nat.beq (CFSG.KD.BrFi24.MUL MSp.Q2B0 MSp.Q2B0) MSp.Q4B0 = true := by
  quickRfl

theorem MSp.p7B0 : Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.MUL MSp.Q4B0 MSp.Q2B0) MSp.GB0) CFSG.KD.BrFi24.ONE = true := by
  quickRfl

theorem MSp.p3S1 : Nat.beq (pow3 MSp.GS1) CFSG.KD.BrFi24.ONE = true := by
  quickRfl

theorem MSp.p3S2 : Nat.beq (pow3 MSp.GS2) CFSG.KD.BrFi24.ONE = true := by
  quickRfl

theorem MSp.p3S3 : Nat.beq (pow3 MSp.GS3) CFSG.KD.BrFi24.ONE = true := by
  quickRfl

theorem MSp.cA0 : Nat.beq (CFSG.KD.BrFi24.MUL MSp.GA0 MSp.GS0) (CFSG.KD.BrFi24.MUL MSp.GS0 MSp.GA0) = true := by
  quickRfl

theorem MSp.cB0 : Nat.beq (CFSG.KD.BrFi24.MUL MSp.GB0 MSp.GS0) (CFSG.KD.BrFi24.MUL MSp.GS0 MSp.GB0) = true := by
  quickRfl

theorem MSp.cT2 : Nat.beq (CFSG.KD.BrFi24.MUL MSp.GT2 MSp.GS2) (CFSG.KD.BrFi24.MUL MSp.GS2 MSp.GT2) = true := by
  quickRfl

theorem MSp.cA2 : Nat.beq (CFSG.KD.BrFi24.MUL MSp.GS2 (MX 0)) (CFSG.KD.BrFi24.MUL (MX 0) MSp.GS2) = true := by
  quickRfl

theorem MSp.vld0 : CFSG.KD.BrFi24.VLD (MX 0) = true := by
  quickRfl

theorem MSp.p3S0 : Nat.beq (pow3 MSp.GS0) CFSG.KD.BrFi24.ONE = true := by
  quickRfl

theorem MSp.pow7_of {M Q2 Q4 : Nat} (h2 : Nat.beq (CFSG.KD.BrFi24.MUL M M) Q2 = true)
    (h4 : Nat.beq (CFSG.KD.BrFi24.MUL Q2 Q2) Q4 = true)
    (h7 : Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.MUL Q4 Q2) M) CFSG.KD.BrFi24.ONE = true) :
    Nat.beq (pow7 M) CFSG.KD.BrFi24.ONE = true := by
  have e : ∀ (y : Nat) (k : Nat → Nat), strictN y k = k y := fun y k => by cases y <;> rfl
  simp only [pow7, e]
  rw [Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h4]
  exact h7

theorem MSp.q2X0 : Nat.beq (CFSG.KD.BrFi24.MUL (MX 0) (MX 0)) MSp.Q2X0 = true := by quickRfl

theorem MSp.q4X0 : Nat.beq (CFSG.KD.BrFi24.MUL MSp.Q2X0 MSp.Q2X0) MSp.Q4X0 = true := by quickRfl

theorem MSp.p7X0 : Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.MUL MSp.Q4X0 MSp.Q2X0) (MX 0))
    CFSG.KD.BrFi24.ONE = true := by quickRfl

theorem MSp.q2X10 : Nat.beq (CFSG.KD.BrFi24.MUL (MX 10) (MX 10)) MSp.Q2X10 = true := by quickRfl

theorem MSp.q4X10 : Nat.beq (CFSG.KD.BrFi24.MUL MSp.Q2X10 MSp.Q2X10) MSp.Q4X10 = true := by quickRfl

theorem MSp.p7X10 : Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.MUL MSp.Q4X10 MSp.Q2X10) (MX 10))
    CFSG.KD.BrFi24.ONE = true := by quickRfl

theorem MSp.q2X21 : Nat.beq (CFSG.KD.BrFi24.MUL (MX 21) (MX 21)) MSp.Q2X21 = true := by quickRfl

theorem MSp.q4X21 : Nat.beq (CFSG.KD.BrFi24.MUL MSp.Q2X21 MSp.Q2X21) MSp.Q4X21 = true := by quickRfl

theorem MSp.p7X21 : Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.MUL MSp.Q4X21 MSp.Q2X21) (MX 21))
    CFSG.KD.BrFi24.ONE = true := by quickRfl

theorem MS.a2 : Nat.beq (pow7 (MX 0)) CFSG.KD.BrFi24.ONE = true :=
  MSp.pow7_of MSp.q2X0 MSp.q4X0 MSp.p7X0

theorem MS.a4 : Nat.beq (pow7 (MX 10)) CFSG.KD.BrFi24.ONE = true :=
  MSp.pow7_of MSp.q2X10 MSp.q4X10 MSp.p7X10

theorem MS.b4 : Nat.beq (pow7 (MX 21)) CFSG.KD.BrFi24.ONE = true :=
  MSp.pow7_of MSp.q2X21 MSp.q4X21 MSp.p7X21

end CFSG.KD.Fi24P7

end
