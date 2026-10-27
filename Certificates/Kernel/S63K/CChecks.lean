module

public import Certificates.Kernel.S63K.CData
public import CFSG.Certificates.Kernel.S63K.BfsSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.KernelS63.CD

open CFSG.KC.S63K CFSG.KS.SporSch.M24 CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def mw (A B : ℕ) : ℕ := CFSG.KC.F2W.mulW 24 A B

@[expose] noncomputable def eqP (A B : ℕ) : Bool := Nat.beq (A % 2 ^ 576) (B % 2 ^ 576)

@[expose] noncomputable def closK : Bool :=
  allN 3072 fun h => allN 4 fun l =>
    bAnd(Nat.blt (EW (h * 4 + l)) 3072, Nat.beq (EP (EW (h * 4 + l))) (stepK CG (EP h) l))

@[expose] noncomputable def invK : Bool :=
  allN 3072 fun i => bAnd(Nat.blt (EInv i) 3072,
    bAnd(Nat.beq (EP (EInv i)) (ipK (EP i) 64 (EP i) idP % 2 ^ 576), eqP (mw (EP i) (EP (EInv i))) idP))

@[expose] noncomputable def o3K (i : ℕ) : Bool :=
  !eqP (EP i) idP && eqP (mw (mw (EP i) (EP i)) (EP i)) idP

@[expose] noncomputable def sq12K (X : ℕ) : ℕ := (List.range 12).foldl (fun acc _ => mw acc acc) X

@[expose] noncomputable def cjK (X : ℕ) : ℕ := mw (mw (EP (C3 0)) X) (EP (EInv (C3 0)))

@[expose] noncomputable def p2K (i : ℕ) : Bool :=
  eqP (sq12K (EP i)) idP && eqP (sq12K (mw (EP i) (cjK (EP i)))) idP

@[expose] noncomputable def P2L : List ℕ := (List.range 3072).filter p2K

@[expose] noncomputable def zK (i : ℕ) : Bool :=
  P2L.all fun j => eqP (mw (EP i) (EP j)) (mw (EP j) (EP i))

@[expose] noncomputable def ZL : List ℕ := P2L.filter zK

@[expose] noncomputable def cmK (i c : ℕ) : ℕ := mw (mw (EP (EInv i)) (EP (EInv c))) (mw (EP i) (EP c))

@[expose] noncomputable def finK (i : ℕ) : Bool :=
  ZL.contains i || (List.range 3072).any fun c =>
    ZL.any (fun j => eqP (EP j) (cmK i c)) && !eqP (cmK i c) idP && !eqP (cmK i c) (T0 0)

theorem rep : bfsK (stepK CG) EP EPar ELab EW ES 4 (3072 + 1) 3072 idP = true := by quickRfl

theorem clos : closK = true := by quickRfl

theorem inv : invK = true := by quickRfl

theorem c3 : (List.range 3072).find? o3K = some (C3 0) := by decide +kernel

theorem fin : P2L.all finK = true := by quickRfl

theorem zlen : ZL.length ≤ 8 := by decide +kernel

theorem c3lt : C3 0 < 3072 := by decide +kernel

theorem neg : bAnd(bIf(o3K 0, false, true), bAnd(bIf(eqP (EP 1) idP, false, true),
    bIf(bfsK (stepK CG) EP EPar ELab EW ES 4 (3072 + 1) 3072 (EP 1), false, true))) = true := by
  quickRfl

end CertificateChecks.KernelS63.CD

end
