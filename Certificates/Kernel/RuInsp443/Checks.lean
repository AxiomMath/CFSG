module

public import Certificates.Kernel.RuInsp443.Data
public import Certificates.Kernel.SporSch.Ru.GensData
public import Certificates.Kernel.SporSch.Ru.C2253
public import Certificates.Data.Kernel.RuInsp443
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuInsp

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.RuInsp CFSG.Quasithin.KGC31.Ru
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelSporSch.RuCe

@[expose] noncomputable def G6 (l : Nat) : Nat :=
  nIf(Nat.beq l 0, A0, nIf(Nat.beq l 1, A1, nIf(Nat.beq l 2, C0, nIf(Nat.beq l 3, C1,
    nIf(Nat.beq l 4, Ns0, Ns1)))))

@[expose] noncomputable def G6I (l : Nat) : Nat :=
  nIf(Nat.beq l 0, A0I, nIf(Nat.beq l 1, A1I, nIf(Nat.beq l 2, C0I, nIf(Nat.beq l 3, C1I,
    nIf(Nat.beq l 4, Ns0I, Ns1I)))))

@[expose] noncomputable def cn (p : Nat) : Bool := canonK 4060 12 (mask 12) (4060 * 12) p

@[expose] noncomputable def wd6 (wd : List Int) (r : Nat) : Bool :=
  wordEqK 4060 12 (mask 12) (pidn 4060 12) G6 G6I 6 wd r

@[expose] noncomputable def BVs : List Nat := [BV 0, BV 1, BV 2, BV 3, BV 4]

@[expose] noncomputable def BEs : List Nat := [BE 0, BE 1, BE 2]

@[expose] noncomputable def CK : Nat :=
  pcomp 4060 12 (mask 12)
    (pcomp 4060 12 (mask 12) (pcomp 4060 12 (mask 12) (KG 0) (XK 0)) (XK 2)) (XK 1)

theorem xW : wd6 xEW (XK 0) = true := by quickRfl
theorem bv0 : wd6 (basisV32EW.getD 0 []) (BV 0) = true := by quickRfl
theorem bv1 : wd6 (basisV32EW.getD 1 []) (BV 1) = true := by quickRfl
theorem bv2 : wd6 (basisV32EW.getD 2 []) (BV 2) = true := by quickRfl
theorem bv3 : wd6 (basisV32EW.getD 3 []) (BV 3) = true := by quickRfl
theorem bv4 : wd6 (basisV32EW.getD 4 []) (BV 4) = true := by quickRfl
theorem be0 : wd6 (basisEW.getD 0 []) (BE 0) = true := by quickRfl
theorem be1 : wd6 (basisEW.getD 1 []) (BE 1) = true := by quickRfl
theorem be2 : wd6 (basisEW.getD 2 []) (BE 2) = true := by quickRfl

theorem pX : permOK 4060 12 (mask 12) (4060 * 12) (XK 0) (XK 1) = true := by quickRfl
theorem pK : permOK 4060 12 (mask 12) (4060 * 12) (KG 0) (XK 2) = true := by quickRfl

theorem cAll : bAnd(cn (XK 0), bAnd(cn (XK 1), bAnd(cn (XK 2), bAnd(cn (KG 0),
    bAnd(cn (BV 0), bAnd(cn (BV 1), bAnd(cn (BV 2), bAnd(cn (BV 3), bAnd(cn (BV 4),
    bAnd(cn (BE 0), bAnd(cn (BE 1), bAnd(cn (BE 2), cn (pidn 4060 12))))))))))))) = true := by
  quickRfl

theorem chk : chkKxEK 4060 12 (mask 12) (pidn 4060 12) CK BVs BEs 5 3 = true := by quickRfl

end CertificateChecks.KernelRuInsp

end
