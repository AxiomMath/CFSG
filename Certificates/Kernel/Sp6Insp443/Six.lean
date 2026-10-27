module

public import Certificates.Kernel.Sp6Insp443.Facts
public import Certificates.Data.Kernel.Sp6Insp443.Six
public import Certificates.Data.Kernel.A45Cls.Defs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelS6I.E
  "Certificates/Kernel/Sp6Insp443/data/six.json.gz" 30658 3214267150612451684
  (dT : List Nat) (dS : List Nat) (sW : List Nat) (zM : List Nat) (cw : List (List Nat))
  (cP : List Nat) (cI : List Nat) (sig : List Nat) (pat : List (List Nat))

namespace CertificateChecks.KernelS6I

open CFSG.KC CFSG.KC.Enum CFSG.KC.A45Cls CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Sp6I
  CFSG.EvenSmallLie.Sp6
  CertificateChecks.KernelLC.Sp6J CFSG.SectionRank.QTK.Insp443.Sp6

@[expose] def sixW (t : Nat) : Nat := [1, 3, 4].getD t 0

@[expose] def sixDs (t : Nat) : List (List CFSG.Sporadic.Th.Native.Table) :=
  [ds1, ds3, ds4].getD t []

@[expose] noncomputable def sixD (t r DT DS : Nat) : Bool :=
  bAnd(tabsPK 36 6 (mask 6) (36 * 6) DT ((sixDs t).getD r []) 0,
  bAnd(Nat.beq (lenT ((sixDs t).getD r [])) 4,
  bAnd(allN 4 (fun i => permOK 36 6 (mask 6) (36 * 6) (laneK (36 * 6) DT i) (laneK (36 * 6) DT i)),
  bAnd(allN 4 (fun i => commPK 36 6 (mask 6) (36 * 6) DT 4 (laneK (36 * 6) DT i)),
    spanPK 36 6 (mask 6) (36 * 6) One36 DT DS 4))))

@[expose] noncomputable def sixG (t r y yi s : Nat) : Bool :=
  bAnd(Nat.blt s 6,
  bAnd(allN 4 (fun i => memPK (36 * 6) (E.dS.getD (6 * t + s) 0) 16
      (pcomp 36 6 (mask 6) y (pcomp 36 6 (mask 6) (laneK (36 * 6) (E.dT.getD (6 * t + r) 0) i) yi))),
    allN 4 (fun i => memPK (36 * 6) (E.dS.getD (6 * t + r) 0) 16
      (pcomp 36 6 (mask 6) yi (pcomp 36 6 (mask 6) (laneK (36 * 6) (E.dT.getD (6 * t + s) 0) i)
        y)))))

@[expose] noncomputable def sixPat (t g : Nat) : Nat :=
  patK (36 * 6) (fun r => E.dS.getD (6 * t + r) 0) 16 6 g

@[expose] noncomputable def ch725106s (t : Nat) : Bool :=
  strictB (E.cP.getD t 0) (fun C => strictB (E.cI.getD t 0) (fun CI =>
  strictB (E.sW.getD t 0) (fun SW => strictB (D.wT.getD (sixW t) 0) (fun WT =>
  strictB (E.zM.getD t 0) (fun zm =>
  bAnd(lettersNK (E.cw.getD t []),
  bAnd(Nat.beq (wordNK 36 6 (mask 6) One36 XQ.S XQ.SI (E.cw.getD t [])) C,
  bAnd(permOK 36 6 (mask 6) (36 * 6) C CI,
  bAnd(tabsPK 36 6 (mask 6) (36 * 6) WT (cands5.getD (sixW t) []) 0,
  bAnd(Nat.beq (lenT (cands5.getD (sixW t) [])) 5,
  bAnd(allN 5 (fun i => permOK 36 6 (mask 6) (36 * 6) (laneK (36 * 6) WT i) (laneK (36 * 6) WT i)),
  bAnd(allN 5 (fun i => commPK 36 6 (mask 6) (36 * 6) WT 5 (laneK (36 * 6) WT i)),
  bAnd(spanPK 36 6 (mask 6) (36 * 6) One36 WT SW 5,
  bAnd(allN 6 (fun r => sixD t r (E.dT.getD (6 * t + r) 0) (E.dS.getD (6 * t + r) 0)),
  bAnd(Nat.blt zm 32,
  bAnd(Nat.beq (laneK (36 * 6) SW zm) (pcomp 36 6 (mask 6) C (pcomp 36 6 (mask 6)
    (wordK 36 6 (mask 6) One36 XQ.S XQ.SI (sp6InvRepWords.getD 0 [])) CI)),
  bAnd(allN 32 (fun s => bIf(Nat.beq (fixK 36 6 (laneK (36 * 6) SW s)) 16, Nat.beq s zm,
    bIf(Nat.beq s zm, false, true))),
  bAnd(allN 5 (fun j => strictB (pcomp 36 6 (mask 6) C (pcomp 36 6 (mask 6) (C1Q.S j) CI))
    (fun y => strictB (pcomp 36 6 (mask 6) C (pcomp 36 6 (mask 6) (C1Q.SI j) CI)) (fun yi =>
      bAnd(permOK 36 6 (mask 6) (36 * 6) (C1Q.S j) (C1Q.SI j),
        allN 6 (fun r => sixG t r y yi (E.sig.getD (6 * (5 * t + j) + r) 0)))))),
  allN 32 (fun s => bAnd(Nat.beq ((E.pat.getD t []).getD s 0) (sixPat t (laneK (36 * 6) SW s)),
    allN s (fun s' => bIf(Nat.beq ((E.pat.getD t []).getD s 0) ((E.pat.getD t []).getD s' 0),
      false, true))))))))))))))))))))))

#kc_each ch725106s 0 3

theorem ch725106n_sig : notB (sixG 0 1
    (pcomp 36 6 (mask 6) (E.cP.getD 0 0) (pcomp 36 6 (mask 6) (C1Q.S 1) (E.cI.getD 0 0)))
    (pcomp 36 6 (mask 6) (E.cP.getD 0 0) (pcomp 36 6 (mask 6) (C1Q.SI 1) (E.cI.getD 0 0))) 1) =
    true := by
  quickRfl

end CertificateChecks.KernelS6I

end
