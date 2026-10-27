module

public import Certificates.Kernel.J3Ref.RecC
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.LocalQT.PEnumD
public import CFSG.Certificates.Kernel.Common.Each
public import Certificates.Data.Kernel.Spor.PEnumB
public import Certificates.Data.Kernel.Spor.MulHQ
meta import Certificates.Data.J3Cls
public meta import CFSG.Sporadic.SmallOddCore.J3LocalCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ3QLoc

open CFSG.SectionRank.QTK.Insp443.J3Cls CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CertificateChecks.KernelJ3Ref

meta def qGM : Array (Array Nat) := j3QGens.toArray.map natArr

meta def qIM : Array (Array Nat) := qGM.map invM

meta def qRecM : Array (Array Nat) := recOfM qGM

meta def qHVM : Array (Array Nat) := hvOfM qRecM

meta def qClM : Array Nat := clOfM qRecM qGM

meta def qNpM : Array Nat := Id.run do
  let idx := indexM qRecM
  let mut out : Array Nat := #[]
  for x in qRecM do
    for c in cGM do
      out := out.push (idx.getD (compM (compM c x) (invM c)) qRecM.size)
  return out

end CertificateChecks.KernelJ3QLoc

#kmulh CertificateChecks.KernelJ3QLoc.J3RQ 6156 13 CertificateChecks.KernelJ3Ref.ids5M
  CertificateChecks.KernelJ3QLoc.qGM CertificateChecks.KernelJ3Ref.idM 100

#kmisc_packarrs CertificateChecks.KernelJ3QLoc.J3QI CertificateChecks.KernelJ3QLoc.qIM 13

#kmisc_packarrs CertificateChecks.KernelJ3QLoc.J3RQV CertificateChecks.KernelJ3QLoc.qHVM 64

#krows32 CertificateChecks.KernelJ3QLoc.J3RQCl CertificateChecks.KernelJ3QLoc.qClM

#krows32 CertificateChecks.KernelJ3QLoc.J3RQNp CertificateChecks.KernelJ3QLoc.qNpM

namespace CertificateChecks.KernelJ3QLoc

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.PEnumB
open CertificateChecks.KernelSpor CertificateChecks.KernelJ3Ref

@[expose] def qWords : List (List Nat) := [[1], [3], [5, 5], [4, 4, 4], [5, 3, 5]]

@[expose] noncomputable def cS (l : Nat) : Nat := J3CentP (Nat.add l 9)

@[expose] noncomputable def qW (j : Nat) : Nat :=
  wfoldK 6156 13 (mask 13) cS (qWords.getD j []) (pidn 6156 13)

@[expose] noncomputable def cC (j : Nat) : Nat := J3CentP (Nat.add j 10)

@[expose] noncomputable def cCI (j : Nat) : Nat := J3CentI (Nat.add j 10)

theorem q_head : bAnd(allN 5 (fun j => bAnd(Nat.beq (J3RQ.GI j) (qW j),
      Nat.beq (J3RQ.G j) (pidn 6156 13))),
    bAnd(Nat.beq J3RQ.cnt 32, penumHdK (pidn 6156 13) J3RQ.cnt 100 J3RQ.T J3RQ.PL)) = true := by
  quickRfl

theorem q_inv : allN 5 (fun j => bAnd(canonK 6156 13 (mask 13) (6156 * 13) (J3QI j),
    invEqK 6156 13 (mask 13) (6156 * 13) (J3RQ.GI j) (J3QI j))) = true := by
  quickRfl

theorem q_pt : allBlk 0
    (penumPtB 6156 13 (mask 13) bsJ J3RQ.GI 5 J3RQ.cnt J3RQ.T J3RQ.PL J3RQ.POS J3RQ.SRT J3RQ.SRI)
    32 = true := by
  quickRfl

@[expose] noncomputable def q_hv (b : Nat) : Bool :=
  allBlk (Nat.mul b 8) (hvK 6156 13 (mask 13) J3RQ.T J3RQV) 8

#kc_each CertificateChecks.KernelJ3QLoc.q_hv 0 4

theorem q_hs : allBlk 0 (hsortVK J3RQ.cnt J3RQV J3RQ.HS J3RQ.HSI) 32 = true := by
  quickRfl

theorem q_cl : allBlk 0
    (findProdB J3RQ.cnt 13 (mask 13) bsJ 10 J3RQ.T (bothK 5 J3RQ.GI J3QI) J3RQCl) 320 = true := by
  quickRfl

theorem q_np : allBlk 0 (findConjB J3RQ.cnt 13 (mask 13) bsJ 5 J3RQ.T cC cCI J3RQNp) 160 =
    true := by
  quickRfl

@[expose] noncomputable def qL : List Nat := [J3RQ.GI 0, J3RQ.GI 1, J3RQ.GI 2, J3RQ.GI 3, J3RQ.GI 4]

theorem q_cent :
    Nat.beq (cntBelowK J3RC.cnt (fun i => centB 13 (mask 13) bsJ qL (J3RC.T i)) 30) 2 = true := by
  quickRfl

theorem q_neg_cl :
    findProdB J3RQ.cnt 13 (mask 13) bsJ 10 J3RQ.T (bothK 5 J3RQ.GI J3QI) J3RQNp 1 = false := by
  decide +kernel

theorem q_neg_np : findConjB J3RQ.cnt 13 (mask 13) bsJ 5 J3RQ.T cC cCI J3RQCl 1 = false := by
  decide +kernel

end CertificateChecks.KernelJ3QLoc

end
