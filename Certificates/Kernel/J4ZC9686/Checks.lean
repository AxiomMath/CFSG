module

public import Certificates.Kernel.J4ZC9686.Data
public import Certificates.Kernel.J4R0.Data
public import Certificates.Kernel.J4Count.FixCEData
public import Certificates.Data.Kernel.J4ZC9686
public import Certificates.Kernel.J4Q.MatData
public import Certificates.Kernel.J4Q.QT2AData
public import Certificates.Kernel.J4Q.QTData
public import Certificates.Kernel.J4Q.MaskData
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4ZC9686

open CFSG.KC.J4ZC9686 CFSG.KD.J4Q CertificateChecks.KernelJ4R0
open CFSG.KC.J4Q (getN notB)

@[expose] noncomputable def QL : List Nat :=
  [QA_0, QA_1, QA_2, QA_3, QA_4, QA_5, QA_6, QA_7, QA_8, QA_9, QA_10, QA_11, CFSG.KD.J4FixCE.CMD]

@[expose] noncomputable def BI : List Nat := invsB one BS B3I B4I

theorem ch9686inv : invOK c rm one BS = true := by quickRfl

theorem ch9686perf : perfOK c rm one BS BI = true := by quickRfl

@[expose] noncomputable def ch9686kn (k : Nat) : Bool :=
  knOK c rm one XS BS TS (getN one QL k) (KW.getD k [])

#kc_each ch9686kn 0 13

theorem ch9686neg_perf : notB (perfOK c rm one BS (BI.set 0 (getN one BS 1))) = true := by
  quickRfl

theorem ch9686neg_kn : notB (knOK c rm one XS BS TS (getN one QL 0)
    ((KW.getD 0 []).set 0 ((KW.getD 0 []).getD 0 (0, 0) |>.1, 0))) = true := by quickRfl

theorem ch9686neg_q : notB (knOK c rm one XS BS TS (getN one QL 1) (KW.getD 0 [])) = true := by
  quickRfl

end CertificateChecks.KernelJ4ZC9686
