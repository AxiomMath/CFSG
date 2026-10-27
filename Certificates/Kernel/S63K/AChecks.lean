module

public import Certificates.Kernel.S63K.AData
public import CFSG.Certificates.Kernel.S63K.BfsSound
public import Certificates.Data.Kernel.S63K.Pick
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.KernelS63.AD

open CFSG.KC.S63K CFSG.KS.SporSch.M24 CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def mw (A B : ℕ) : ℕ := CFSG.KC.F2W.mulW 24 A B

@[expose] noncomputable def powK (X e : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) idP (fun _ acc => mw acc X) e

@[expose] noncomputable def memQ (Y : ℕ) : Bool := (List.range 512).any fun w => eqM (QP w) Y

@[expose] noncomputable def fld (R s : ℕ) : ℕ := Nat.shiftRight R (24 * s) % 16777216

@[expose] noncomputable def posL (R : ℕ) : List ℕ := (List.range 512).map (fld R)

@[expose] noncomputable def maskOf (rs : List ℕ) : ℕ :=
  rs.foldl (fun m r => Nat.lor m (Nat.shiftLeft 1 r)) 0

@[expose] noncomputable def covK (ps : List ℕ) (R : ℕ) : Bool :=
  Nat.beq ps.length 512 &&
    ((ps.zip (posL R)).all fun pr => Nat.blt pr.2 512 && eqM (QP pr.2) pr.1) &&
    Nat.beq (maskOf (posL R)) (2 ^ 512 - 1)

@[expose] noncomputable def subProdsK : List ℕ → List ℕ
  | [] => [idP]
  | y :: ys => subProdsK ys ++ (subProdsK ys).map (mw y)

@[expose] noncomputable def cjL (j c : ℕ) : ℕ := mw (mw (LP c) (QP j)) (LP (LInv c))

@[expose] noncomputable def cjL' (i c : ℕ) : ℕ := mw (mw (LP c) (LP i)) (LP (LInv c))

@[expose] noncomputable def irK (j : ℕ) : List ℕ := pickK (cjL j) 512 504 0 [idP, Zp] []

@[expose] noncomputable def cmA (a b : ℕ) : ℕ := mw (mw (QP (QInv a)) (LP (LInv b))) (mw (QP a) (LP b))

@[expose] noncomputable def cmK : List ℕ :=
  pickK (fun c => cmA (c / 504) (c % 504)) 512 (512 * 504) 0 [idP, Zp] []

theorem repQ : bfsK (stepK QG) QP QPar QLab QW QS 8 (512 + 1) 512 idP = true := by quickRfl

theorem repL : bfsK (stepK LG) LP LPar LLab LW LS 6 (504 + 1) 504 idP = true := by quickRfl

theorem closQ : (allN 512 fun h => allN 8 fun l =>
    bAnd(Nat.blt (QW (h * 8 + l)) 512, Nat.beq (QP (QW (h * 8 + l))) (stepK QG (QP h) l))) = true := by
  quickRfl

theorem closL : (allN 504 fun h => allN 6 fun l =>
    bAnd(Nat.blt (LW (h * 6 + l)) 504, Nat.beq (LP (LW (h * 6 + l))) (stepK LG (LP h) l))) = true := by
  quickRfl

theorem invQ : (allN 512 fun i => bAnd(Nat.blt (QInv i) 512,
    bAnd(Nat.beq (QP (QInv i)) (ipK (QP i) 64 (QP i) idP % 2 ^ 576), eqM (mw (QP i) (QP (QInv i))) idP))) =
    true := by
  quickRfl

theorem invL : (allN 504 fun i => bAnd(Nat.blt (LInv i) 504,
    bAnd(Nat.beq (LP (LInv i)) (ipK (LP i) 64 (LP i) idP % 2 ^ 576), eqM (mw (LP i) (LP (LInv i))) idP))) =
    true := by
  quickRfl

theorem gq : (allN 8 fun k => bAnd(eqM (mw (QG k) (QG k)) idP, eqM (mw (QG k) Zp) (mw Zp (QG k)))) =
    true := by
  quickRfl

theorem gl : (allN 6 fun k => bAnd(eqM (mw (LG k) (LG k)) idP, eqM (mw (LG k) Zp) (mw Zp (LG k)))) =
    true := by
  quickRfl

theorem zq : memQ Zp = true := by quickRfl

theorem t10 : (allN 504 fun i => eqM (LP i) idP || !memQ (LP i)) = true := by quickRfl

theorem t11 : (allN 6 fun k => allN 512 fun i => memQ (mw (mw (LG k) (QP i)) (LG k))) = true := by
  quickRfl

theorem t12 : (allN 504 fun i => !eqM (mw (LP i) (LP i)) idP || eqM (LP i) idP ||
    (List.range 504).any fun c => !eqM (mw (LP i) (cjL' i c)) idP &&
      eqM (powK (mw (LP i) (cjL' i c)) 63) idP) = true := by
  quickRfl

@[expose] noncomputable def t13K (j : ℕ) : Bool := eqM (QP j) idP || eqM (QP j) Zp ||
    ((irK j).all (fun c => decide (c < 504)) &&
      covK (subProdsK ((irK j).map (cjL j) ++ [Zp])) (RP j))

@[expose] noncomputable def t13C (b : ℕ) : Bool := allN 8 fun r => t13K (8 * b + r)

#kc_each CertificateChecks.KernelS63.AD.t13C 0 64

theorem t14 : ((cmK.map fun c => (c / 504, c % 504)).all (fun p => decide (p.1 < 512) && decide (p.2 < 504)) &&
    covK (subProdsK ((cmK.map fun c => (c / 504, c % 504)).map (fun p => cmA p.1 p.2) ++ [Zp])) RC) =
    true := by
  quickRfl

theorem t15 : (allN 512 fun i => allN 8 fun k =>
    eqM (mw (mw (QP i) (QG k)) (QP (QInv i))) (QG k) ||
      eqM (mw (mw (QP i) (QG k)) (QP (QInv i))) (mw (QG k) Zp)) = true := by
  quickRfl

theorem t16 : (allN 504 fun i => eqM (LP i) idP || (List.range 8).any fun k =>
    !eqM (mw (mw (LP i) (QG k)) (LP (LInv i))) (QG k) &&
      !eqM (mw (mw (LP i) (QG k)) (LP (LInv i))) (mw (QG k) Zp)) = true := by
  quickRfl

theorem neg : bAnd(bIf(eqM Zp idP, false, true), bAnd(bIf(eqM (LP 1) Zp, false, true),
    bAnd(bIf(covK (subProdsK ((irK 2).map (cjL 2) ++ [Zp])) (RP 3), false, true),
    bIf(bfsK (stepK QG) QP QPar QLab QW QS 8 (512 + 1) 512 (QP 1), false, true)))) = true := by
  quickRfl

end CertificateChecks.KernelS63.AD

end
