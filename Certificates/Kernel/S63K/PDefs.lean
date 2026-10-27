module

public import Certificates.Kernel.S63K.PData
public import Certificates.Kernel.S63K.HBind
public import Certificates.Kernel.S63K.IData
public import Certificates.Kernel.S63K.CData
public import Certificates.Kernel.S63K.AData
public import Certificates.Data.Kernel.S63K.ConjTree
public import Certificates.Data.Kernel.S63K.Sorted
public import Certificates.Data.Kernel.S63K.Pick
public import Certificates.Data.D4HexLocWords
public import Certificates.Data.D4HexLinkCheck
public import CFSG.Certificates.Kernel.S63K.BfsSound

public section

namespace CertificateChecks.KernelS63.PD

open CFSG.KC.S63K CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.M24 CertificateChecks.KernelS63

@[expose] noncomputable def mw (A B : ℕ) : ℕ := CFSG.KC.F2W.mulW 24 A B

@[expose] noncomputable def T0r : ℕ := CD.T0 0 % 2 ^ 576

@[expose] noncomputable def cmP (A B : ℕ) : Bool := eqM (mw A B) (mw B A)

@[expose] noncomputable def invK (X : ℕ) : Bool :=
  bAnd(eqM (mw X X) idP, bIf(eqM X idP, false, true))

@[expose] noncomputable def cjS (j X : ℕ) : ℕ := mw (mw (SW j) X) (SV j) % 2 ^ 576

@[expose] def stepW (j : ℕ) : List ℕ := (CFSG.D4Hex.locStepWords.getD j (true, [])).2

@[expose] noncomputable def wordsK : Bool :=
  bAnd(allN 12 fun j => bAnd(Nat.beq (SW j) (wordK ID.G idM (stepW j) % 2 ^ 576),
      Nat.beq (SV j) (wordK ID.G idM (stepW j).reverse % 2 ^ 576)),
    Nat.beq (U0 0) (wordK ID.G idM CFSG.D4Hex.locU0Word % 2 ^ 576))

@[expose] noncomputable def faK (h j : ℕ) : Bool :=
  strictB (cjS j (HD.TP (FO h))) fun y =>
    bIf(bAnd(Nat.blt (FW (12 * h + j)) 495, Nat.beq (HD.TP (FO (FW (12 * h + j)))) y), true,
      bAnd(Nat.beq (FW (12 * h + j)) 0, Nat.beq (memS HD.TP HD.TS 4096 y) 0))

@[expose] noncomputable def ch4237F (b : ℕ) : Bool :=
  allN 33 fun r => allN 12 fun j => faK (Nat.add (Nat.mul 33 b) r) j

@[expose] noncomputable def inK (i : ℕ) : Bool :=
  bIf(invK (HD.TP i), bAnd(Nat.blt (FI i) 495, Nat.beq (FO (FI i)) i), true)

@[expose] noncomputable def ch4237I (b : ℕ) : Bool := allN 64 fun r => inK (Nat.add (Nat.mul 64 b) r)

@[expose] noncomputable def ceK (i : ℕ) : Bool :=
  bIf(allN 4 fun k => cmP (HD.TP i) (HD.UG k), bIf(eqM (HD.TP i) idP, true, eqM (HD.TP i) (ID.ZP 0)),
    true)

@[expose] noncomputable def ch4237Z (b : ℕ) : Bool := allN 64 fun r => ceK (Nat.add (Nat.mul 64 b) r)

@[expose] noncomputable def paK (h j : ℕ) : Bool :=
  strictB (cjS j (HD.TP (QA h))) fun ya => strictB (cjS j (HD.TP (QB h))) fun yb =>
    bIf(bAnd(Nat.blt (QW (12 * h + j)) 2464, bAnd(Nat.beq (HD.TP (QA (QW (12 * h + j)))) ya,
        Nat.beq (HD.TP (QB (QW (12 * h + j)))) yb)), true,
      bAnd(Nat.beq (QW (12 * h + j)) 0, bIf(Nat.beq (memS HD.TP HD.TS 4096 ya) 0, true,
        Nat.beq (memS HD.TP HD.TS 4096 yb) 0)))

@[expose] noncomputable def ch4237P (b : ℕ) : Bool :=
  allN 81 fun r => (fun h => bIf(Nat.blt h 2464, allN 12 fun j => paK h j, true))
    (Nat.add (Nat.mul 81 b) r)

@[expose] noncomputable def qcode (i : ℕ) : ℕ := 4096 * QA i + QB i

@[expose] noncomputable def tiK (i : ℕ) : Bool :=
  bAnd(Nat.blt (TI i) 4096, bAnd(Nat.beq (HD.TP (TI i)) (ipK (HD.TP i) 64 (HD.TP i) idP % 2 ^ 576),
    eqM (CFSG.KC.F2W.mulW 24 (HD.TP i) (HD.TP (TI i))) idP))

@[expose] noncomputable def ch4237V (b : ℕ) : Bool := allN 64 fun r => tiK (Nat.add (Nat.mul 64 b) r)

@[expose] noncomputable def tqK (i : ℕ) : Bool :=
  allN 4 fun k => Nat.beq (memS AD.QP AD.QS 512
    (mw (mw (HD.TP i) (HD.UG k)) (mw (HD.TP (TI i)) (HD.UG k)) % 2 ^ 576)) 1

@[expose] noncomputable def ch4237C (b : ℕ) : Bool := allN 64 fun r => tqK (Nat.add (Nat.mul 64 b) r)

@[expose] noncomputable def sqU (k X : ℕ) : ℕ := mw (mw (HD.UG k) X) (mw (HD.UG k) X)

@[expose] noncomputable def qK (i : ℕ) : Bool :=
  bAnd(allN 8 fun k => bIf(cmP (AD.QP i) (AD.QG k), true,
      eqM (mw (AD.QP i) (AD.QG k)) (mw (ID.ZP 0) (mw (AD.QG k) (AD.QP i)))),
    bAnd(bIf(eqM (mw (AD.QP i) (AD.QP i)) idP, true, eqM (mw (AD.QP i) (AD.QP i)) (ID.ZP 0)),
    bAnd(bIf(allN 8 fun k => cmP (AD.QP i) (AD.QG k),
        bIf(eqM (AD.QP i) idP, true, eqM (AD.QP i) (ID.ZP 0)), true),
      bIf(invK (AD.QP i), bIf(Nat.beq (memS ID.ZP ID.ZS 819 (AD.QP i)) 1, true,
        (List.range 4).any fun k => !eqM (sqU k (AD.QP i)) idP && !eqM (sqU k (AD.QP i)) (ID.ZP 0)),
        true))))

@[expose] noncomputable def ch4237Q (b : ℕ) : Bool := allN 64 fun r => qK (Nat.add (Nat.mul 64 b) r)

@[expose] noncomputable def pwV : ℕ := PW 0 / 16777216
@[expose] noncomputable def pwA : ℕ := PW 0 / 4096 % 4096
@[expose] noncomputable def pwB : ℕ := PW 0 % 4096

@[expose] noncomputable def pwI (iv : ℕ) : Bool :=
  bAnd(invK (AD.QP iv), Nat.beq (memS ID.ZP ID.ZS 819 (AD.QP iv)) 0)

@[expose] noncomputable def pwT (ia ib : ℕ) : Bool :=
  bAnd(cmP (AD.QP ib) (AD.QP pwV),
    eqM (mw (AD.QP ia) (AD.QP ib)) (mw (ID.ZP 0) (mw (AD.QP ib) (AD.QP ia))))

@[expose] noncomputable def pwK : Bool :=
  bAnd(Nat.blt pwV 512, bAnd(Nat.blt pwA 512, bAnd(Nat.blt pwB 512,
  bAnd(allN pwV (fun iv => bIf(invK (AD.QP iv), Nat.beq (memS ID.ZP ID.ZS 819 (AD.QP iv)) 1,
    true)), bAnd(pwI pwV,
  bAnd(allN pwA (fun ia => bIf(cmP (AD.QP ia) (AD.QP pwV),
    allN 512 fun ib => bIf(pwT ia ib, false, true), true)),
  bAnd(cmP (AD.QP pwA) (AD.QP pwV), bAnd(allN pwB (fun ib => bIf(pwT pwA ib, false, true)),
    pwT pwA pwB))))))))

@[expose] noncomputable def inV (k v : ℕ) : Bool :=
  strictB (mw (mw (CD.CG k) v) (CD.CG k)) fun w =>
    bIf(eqM w (ID.ZP 0), true, bIf(eqM w (ID.ZP 1), true, eqM w (ID.ZP 5)))

@[expose] noncomputable def vK : Bool :=
  bAnd(invK (ID.ZP 0), bAnd(invK T0r, bAnd(invK (ID.ZP 1), bAnd(invK (ID.ZP 5),
  bAnd(eqM (mw (ID.ZP 0) (ID.ZP 1)) (ID.ZP 5), bAnd(eqM (mw (ID.ZP 1) (ID.ZP 0)) (ID.ZP 5),
  bAnd(eqM (mw (ID.ZP 0) (ID.ZP 5)) (ID.ZP 1), bAnd(eqM (mw (ID.ZP 5) (ID.ZP 0)) (ID.ZP 1),
  bAnd(eqM (mw (ID.ZP 1) (ID.ZP 5)) (ID.ZP 0), bAnd(eqM (mw (ID.ZP 5) (ID.ZP 1)) (ID.ZP 0),
  bAnd(cmP T0r (ID.ZP 0), bAnd(cmP T0r (ID.ZP 1), bAnd(cmP T0r (ID.ZP 5),
  bAnd(allN 4 fun k => bAnd(inV k (ID.ZP 0), bAnd(inV k (ID.ZP 1), inV k (ID.ZP 5))),
  bAnd((List.range 3).any (fun a => eqM (ZCP a) (ID.ZP 1)),
  bAnd((List.range 3).any (fun a => eqM (ZCP a) (ID.ZP 5)),
  bAnd(Nat.blt (VC 0) 3072, bAnd(cmP (CD.EP (VC 0)) (ID.ZP 0), bAnd(cmP (CD.EP (VC 0)) (ID.ZP 1),
  bAnd(cmP (CD.EP (VC 0)) (ID.ZP 5), strictB (mw (CD.EP (VC 0)) (CD.EP (VC 0))) fun s =>
    bIf(eqM s (ID.ZP 0), true, bIf(eqM s (ID.ZP 1), true, eqM s (ID.ZP 5)))))))))))))))))))))))

@[expose] noncomputable def fuK (i : ℕ) : Bool :=
  bIf(cmP (ID.ZP i) T0r, bIf(Nat.beq i 0, true, bIf(Nat.beq i 1, true, bIf(Nat.beq i 5, true,
    (List.range 24).any fun a => eqM (UCP a) (ID.ZP i)))), true)

@[expose] noncomputable def ch4237U (b : ℕ) : Bool := allN 63 fun r => fuK (Nat.add (Nat.mul 63 b) r)

@[expose] noncomputable def stepOKK (s : Bool × List ℕ) : Bool :=
  s.2.all (fun k => decide (k < 8)) && (if s.1 then Nat.beq (HD.ptW s.2 0) 0 else
    CFSG.D4Hex.sortKey (HD.ptW s.2 0) (HD.ptW s.2 1) (HD.ptW s.2 5) == CFSG.D4Hex.lineKey 0 1 5)

end CertificateChecks.KernelS63.PD

end
