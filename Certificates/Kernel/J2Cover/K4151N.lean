module

public import Certificates.Kernel.J2Cover.K4151C
public import Certificates.Kernel.J2Cover.K20B
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.J2CoverSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2Cover
open CFSG.KC.Misc.ArrEnum
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover
open CFSG.ComponentClassification.J2Cover.External

theorem cntSBK : Nat.beq (prodCnt 315 9 2 SB.LR SB.TR cmK) 1 = true := by quickRfl

theorem countSB : countProducts 315 (commAll 315 [tblX, tblY]) (chainTables 315 subStrong subBase)
    (idT 315) = 1 := by
  have c0 : CnN 315 9 (FD.S 0) := by quickRfl
  have c1 : CnN 315 9 (FD.S 1) := by quickRfl
  have hX : tblX = φ (FD.S 0) := by unfold tblX; rw [fD_S 0 (by omega)]
  have hY : tblY = φ (FD.S 1) := by unfold tblY; rw [fD_S 1 (by omega)]
  rw [hX, hY, countProducts_sound sb_binds sb_perm SB.hl
    (f := commAll 315 [φ (FD.S 0), φ (FD.S 1)]) (fk := cmK) fun E cE => by
    unfold commAll cmK
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    rw [CFSG.KC.J2Cover.commT_unpack cE c0, CFSG.KC.J2Cover.commT_unpack cE c1]
    rfl, Nat.eq_of_beq_eq_true cntSBK]

@[expose] noncomputable def wordV : List Nat :=
  [FD.S 1, FD.S 0, FD.S 1, FD.S 0, FD.S 1, FD.S 0, FD.S 1, FD.S 1, FD.S 0, FD.S 1, FD.S 0, FD.S 1]

@[expose] noncomputable def d0K (X V : Nat) : Bool :=
  bAnd(Nat.beq (pg 9 (mask 9) X 0) 0, bAnd(Nat.beq (pg 9 (mask 9) V 0) 0,
    allN 315 (fun i => bIf(Nat.beq i 0, true,
      bIf(bAnd(Nat.beq (pg 9 (mask 9) X i) i, Nat.beq (pg 9 (mask 9) V i) i), false, true)))))

theorem d0S : strictB (prodK 315 9 wordV) (fun V => d0K (FD.S 0) V) = true := by quickRfl

theorem d0 : d0K (FD.S 0) (prodK 315 9 wordV) = true := by
  have e : ∀ (y : Nat) (k : Nat → Bool), strictB y k = k y := fun y k => by cases y <;> rfl
  have h := d0S
  rw [e] at h
  exact h

end CertificateChecks.KernelJ2Cover

end
