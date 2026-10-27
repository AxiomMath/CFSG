module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.L34W.Tabs
public import Certificates.Kernel.L34W.Gens
public import Certificates.Data.Kernel.L34W.ChCover
meta import Certificates.Data.ChengHeldCover
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelL34W

open CFSG.PSL3Four.Native CFSG.OddStandard.ChengHeldData
open CFSG.ComponentClassification.GrSLit.L34Facts

meta def frG : Array (Array Nat) := wordTabs frTg
meta def id42M : Array Nat := idTab 42

end CertificateChecks.KernelL34W

#kpenum CertificateChecks.KernelL34W.CC 42 6 false CertificateChecks.KernelL34W.frG
  CertificateChecks.KernelL34W.frG CertificateChecks.KernelL34W.id42M 64

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.L34W
open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.Tm

theorem ch6136_f4 : bAnd(relsC T1X.F (eqKC 1 2) (frC 0) (frame4Rels 0),
    relsC T1X.F (eqKC 1 0) (frC 1) (frame4Rels 1)) = true := by
  quickRfl

theorem ch6136_a4 : bAnd(bAnd(actC T1X.F AlX.F (eqKC 1 2) (frC 0) 1 (actRels 0 0),
    bAnd(actC T1X.F AlX.F (eqKC 1 2) (frC 0) 2 (actRels 0 1),
      actC T1X.F AlX.F (eqKC 1 2) (frC 0) 3 (actRels 0 2))),
    bAnd(actC T1X.F AlX.F (eqKC 1 0) (frC 1) 1 (actRels 1 0),
    bAnd(actC T1X.F AlX.F (eqKC 1 0) (frC 1) 2 (actRels 1 1),
      actC T1X.F AlX.F (eqKC 1 0) (frC 1) 3 (actRels 1 2)))) = true := by
  quickRfl

theorem ch6136_f2 : relsC T1X.F eqN2C (frC 2) frame2Rels = true := by quickRfl

theorem ch6136_a2 : bAnd(actC T1X.F AlX.F eqN2C (frC 2) 1 (act2Rels 0),
    bAnd(actC T1X.F AlX.F eqN2C (frC 2) 2 (act2Rels 1),
      actC T1X.F AlX.F eqN2C (frC 2) 3 (act2Rels 2))) = true := by
  quickRfl

theorem ch6136_g : bAnd(actC T1X.F AlX.F (eqKC 1 2) (frC 0) 31 (gRels 0),
    bAnd(actC T1X.F AlX.F (eqKC 1 0) (frC 1) 31 (gRels 1),
      actC T1X.F AlX.F eqN2C (frC 2) 31 (gRels 2))) = true := by
  quickRfl

theorem ch6136_neg_rel : (!relsC T1X.F (eqKC 1 2) (frC 0) [(vt, Tm.one)]) = true := by quickRfl

theorem ch6136_neg_act : (!actC T1X.F AlX.F (eqKC 1 2) (frC 0) 1 (actRels 0 1)) = true := by
  quickRfl

theorem ch6136_neg_n2 : (!relsC T1X.F eqN2C (frC 2) [(vt, pw vt 2)]) = true := by quickRfl

theorem ch6136_gens : bAnd(Nat.beq (CC.G 0) (tgK GT 4), bAnd(Nat.beq (CC.G 1) (tgK GT 8),
    bAnd(Nat.beq (CC.G 2) (tgK GT 3), bAnd(Nat.beq (CC.G 3) (tgK GT 2),
    bAnd(Nat.beq (CC.G 4) (tgK GT 24), Nat.beq (CC.G 5) (tgK GT 16)))))) = true := by
  quickRfl

theorem ch6136_cnt : CC.cnt = 64 := rfl
theorem ch6136_k : CC.k = 6 := rfl
theorem ch6136_hd : penumHdK (pidn 42 6) 64 64 CC.T CC.PL = true := by quickRfl

theorem ch6136_sl : penumSlK 42 6 (mask 6) (42 * 6) false CC.G CC.GI 6 64 CC.T CC.PL
    CC.POS CC.SRT CC.SRI 0 64 = true := by
  quickRfl

theorem ch6136_neg_sl : (!penumSlK 42 6 (mask 6) (42 * 6) false
    (fun j => CC.G (nIf(Nat.beq j 0, 1, nIf(Nat.beq j 1, 0, j)))) CC.GI 6 64 CC.T CC.PL
    CC.POS CC.SRT CC.SRI 0 64) = true := by
  quickRfl

theorem ch6136_comm : bAnd(Nat.beq (pcomp 42 6 (mask 6) (repK GT 4) (repK GT 3))
      (pcomp 42 6 (mask 6) (repK GT 3) (repK GT 4)),
    Nat.beq (pcomp 42 6 (mask 6) (repK GT 5) (repK GT 3))
      (pcomp 42 6 (mask 6) (repK GT 3) (repK GT 5))) = true := by
  quickRfl

end CertificateChecks.KernelL34W

end
