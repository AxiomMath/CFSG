module

public import Certificates.Kernel.Sp6Insp443.Facts
public import Certificates.Data.Kernel.A45Cls.Defs
public import Certificates.Data.CFSGNative.Insp443.PermTests
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelS6I.F
  "Certificates/Kernel/Sp6Insp443/data/fano.json.gz" 70708 7954237937862006898
  (aT : List Nat) (sA : List Nat) (wT : List Nat) (sW : List Nat) (kT : List Nat) (kS : List Nat)
  (hT : List Nat) (hS : List Nat) (uM : List Nat) (cw : List (List Nat)) (cP : List Nat)
  (cI : List Nat) (nM : List (List Nat)) (nw : List (List (List Nat))) (nP : List (List Nat))
  (nI : List (List Nat)) (gs : List Nat)

namespace CertificateChecks.KernelS6I

open CFSG.KC CFSG.KC.Enum CFSG.KC.A45Cls CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Sp6I
  CFSG.EvenSmallLie.Sp6 CertificateChecks.KernelLC.Sp6J CFSG.SectionRank.QTK.Insp443.Sp6
  CFSG.SectionRank.QTK.Insp443.PermKit.Native

@[expose] def fanoW (t : Nat) : Nat := [2, 4].getD t 0

@[expose] def fanoA (t : Nat) : Nat := [0, 1].getD t 0

@[expose] def fanoRows (t : Nat) : List Nat := [rows2, rows4].getD t []

@[expose] noncomputable def fanoB (P S c : Nat) : Bool :=
  bAnd(allN c (fun i => permOK 36 6 (mask 6) (36 * 6) (laneK (36 * 6) P i) (laneK (36 * 6) P i)),
  bAnd(allN c (fun i => commPK 36 6 (mask 6) (36 * 6) P c (laneK (36 * 6) P i)),
    spanPK 36 6 (mask 6) (36 * 6) One36 P S c))

@[expose] noncomputable def memIs (S c g : Nat) (b : Bool) : Bool :=
  bIf(memPK (36 * 6) S c g, b, bIf(b, false, true))

@[expose] noncomputable def fanoKH (t p : Nat) : Bool :=
  strictB (F.kT.getD (7 * t + p - 1) 0) (fun KT => strictB (F.kS.getD (7 * t + p - 1) 0) (fun KS =>
  strictB (F.hT.getD (7 * t + p - 1) 0) (fun HT => strictB (F.hS.getD (7 * t + p - 1) 0) (fun HS =>
  bAnd(fanoB KT KS 2, bAnd(fanoB HT HS 5,
  bAnd(allN 8 (fun d => memIs KS 4 (laneK (36 * 6) (F.sA.getD t 0) d) (bIf(dot3 d p, false, true))),
  bAnd(allN 64 (fun m => memIs HS 32 (laneK (36 * 6) (F.sW.getD t 0) m)
    (bIf(bsum (fanoRows t) m p, false, true))),
  bAnd(allN 3 (fun i => memIs KS 4 (laneK (36 * 6) (F.aT.getD t 0) i)
    (bIf(dot3 (Nat.shiftLeft 1 i) p, false, true))),
    allN 6 (fun j => memIs HS 32 (laneK (36 * 6) (F.wT.getD t 0) j)
      (bIf(Nat.testBit ((fanoRows t).getD j 0) p, false, true))))))))))))

@[expose] noncomputable def fanoPQ (t y yi p q : Nat) : Bool :=
  strictB (F.kT.getD (7 * t + p - 1) 0) (fun KTp => strictB (F.kS.getD (7 * t + p - 1) 0) (fun KSp =>
  strictB (F.hT.getD (7 * t + p - 1) 0) (fun HTp => strictB (F.hS.getD (7 * t + p - 1) 0) (fun HSp =>
  strictB (F.kT.getD (7 * t + q - 1) 0) (fun KTq => strictB (F.kS.getD (7 * t + q - 1) 0) (fun KSq =>
  strictB (F.hT.getD (7 * t + q - 1) 0) (fun HTq => strictB (F.hS.getD (7 * t + q - 1) 0) (fun HSq =>
  bAnd(allN 2 (fun i => memPK (36 * 6) KSq 4
    (pcomp 36 6 (mask 6) y (pcomp 36 6 (mask 6) (laneK (36 * 6) KTp i) yi))),
  bAnd(allN 2 (fun i => memPK (36 * 6) KSp 4
    (pcomp 36 6 (mask 6) yi (pcomp 36 6 (mask 6) (laneK (36 * 6) KTq i) y))),
  bAnd(allN 5 (fun i => memPK (36 * 6) HSq 32
    (pcomp 36 6 (mask 6) y (pcomp 36 6 (mask 6) (laneK (36 * 6) HTp i) yi))),
    allN 5 (fun i => memPK (36 * 6) HSp 32
      (pcomp 36 6 (mask 6) yi (pcomp 36 6 (mask 6) (laneK (36 * 6) HTq i) y))))))))))))))

@[expose] noncomputable def fanoG (t y yi j : Nat) : Bool :=
  bAnd(allN 3 (fun i => memPK (36 * 6) (F.sA.getD t 0) 8
    (pcomp 36 6 (mask 6) y (pcomp 36 6 (mask 6) (laneK (36 * 6) (F.aT.getD t 0) i) yi))),
  bAnd(allN 3 (fun i => memPK (36 * 6) (F.sA.getD t 0) 8
    (pcomp 36 6 (mask 6) yi (pcomp 36 6 (mask 6) (laneK (36 * 6) (F.aT.getD t 0) i) y))),
    allN 7 (fun p => strictB (F.gs.getD (7 * (34 * t + j) + p) 0) (fun q =>
      bAnd(Nat.blt 0 q, bAnd(Nat.blt q 8, fanoPQ t y yi (p + 1) q))))))

@[expose] noncomputable def ch725107f (t : Nat) : Bool :=
  strictB (F.cP.getD t 0) (fun C => strictB (F.cI.getD t 0) (fun CI =>
  strictB (F.sW.getD t 0) (fun SW => strictB (F.wT.getD t 0) (fun WT =>
  strictB (F.uM.getD t 0) (fun um => strictB (laneK (36 * 6) SW um) (fun U =>
  bAnd(lettersNK (F.cw.getD t []),
  bAnd(Nat.beq (wordNK 36 6 (mask 6) One36 XQ.S XQ.SI (F.cw.getD t [])) C,
  bAnd(permOK 36 6 (mask 6) (36 * 6) C CI,
  bAnd(tabsPK 36 6 (mask 6) (36 * 6) WT (cands7.getD (fanoW t) []) 0,
  bAnd(Nat.beq (lenT (cands7.getD (fanoW t) [])) 6,
  bAnd(fanoB WT SW 6,
  bAnd(tabsPK 36 6 (mask 6) (36 * 6) (F.aT.getD t 0) (cands7.getD (fanoA t) []) 0,
  bAnd(Nat.beq (lenT (cands7.getD (fanoA t) [])) 3,
  bAnd(fanoB (F.aT.getD t 0) (F.sA.getD t 0) 3,
  bAnd(allN 7 (fun p => fanoKH t (p + 1)),
  bAnd(Nat.blt um 64,
  bAnd(Nat.beq U (pcomp 36 6 (mask 6) C (pcomp 36 6 (mask 6)
    (wordK 36 6 (mask 6) One36 XQ.S XQ.SI (sp6InvRepWords.getD 3 [])) CI)),
  bAnd(Nat.beq (fixK 36 6 U) 4,
  bAnd(allN 64 (fun s => bIf(Nat.beq (fixK 36 6 (laneK (36 * 6) SW s)) 4,
    bIf(allN 28 (fun q => bIf(Nat.beq ((F.nM.getD t []).getD q 0) s, false, true)), false, true),
    true)),
  bAnd(allN 28 (fun q => strictB ((F.nP.getD t []).getD q 0) (fun NP =>
    strictB ((F.nI.getD t []).getD q 0) (fun NI =>
    bAnd(Nat.blt ((F.nM.getD t []).getD q 0) 64,
    bAnd(lettersNK ((F.nw.getD t []).getD q []),
    bAnd(Nat.beq (wordNK 36 6 (mask 6) One36 XQ.S XQ.SI ((F.nw.getD t []).getD q [])) NP,
    bAnd(permOK 36 6 (mask 6) (36 * 6) NP NI,
    bAnd(Nat.beq (laneK (36 * 6) SW ((F.nM.getD t []).getD q 0))
      (pcomp 36 6 (mask 6) NP (pcomp 36 6 (mask 6) U NI)),
      fanoG t NP NI (6 + q))))))))),
  allN 6 (fun j => strictB (pcomp 36 6 (mask 6) C (pcomp 36 6 (mask 6) (C4Q.S j) CI))
    (fun y => strictB (pcomp 36 6 (mask 6) C (pcomp 36 6 (mask 6) (C4Q.SI j) CI)) (fun yi =>
      bAnd(permOK 36 6 (mask 6) (36 * 6) (C4Q.S j) (C4Q.SI j), fanoG t y yi j)))))))))))))))))))))))))

#kc_each ch725107f 0 2

theorem ch725107n_gs : notB (fanoPQ 0
    (pcomp 36 6 (mask 6) (F.cP.getD 0 0) (pcomp 36 6 (mask 6) (C4Q.S 0) (F.cI.getD 0 0)))
    (pcomp 36 6 (mask 6) (F.cP.getD 0 0) (pcomp 36 6 (mask 6) (C4Q.SI 0) (F.cI.getD 0 0))) 1 2) =
    true := by
  quickRfl

end CertificateChecks.KernelS6I

end
