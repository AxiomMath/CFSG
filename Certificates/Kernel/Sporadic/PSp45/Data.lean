module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import Certificates.Kernel.Sporadic.PSp45.Words
public meta import Certificates.Kernel.Sporadic.PSp45.Words
public meta import CFSG.Monster.B.Mathieu.Order
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.PSp45

open CFSG.KS.SporSch.MOCG CFSG.ComponentClassification.CatFactsSmall.PSp43

meta def tXM : Array Nat :=
  (CFSG.Monster.B.Mathieu.imageList (CFSG.Sporadic.Schreier.tab x45)).toArray

meta def tYM : Array Nat :=
  (CFSG.Monster.B.Mathieu.imageList (CFSG.Sporadic.Schreier.tab y45)).toArray

meta def tFM : Array Nat :=
  (CFSG.Monster.B.Mathieu.imageList (CFSG.Sporadic.Schreier.tab f45)).toArray

meta def SP : Array (Array Nat) := strongOf 45 #[tXM, tYM] wordsP

meta def baseP : Array Nat := #[0, 1, 16, 3]

meta def SA : Array (Array Nat) := strongOf 45 #[tXM, tYM, tFM] wordsA

meta def baseA : Array Nat := #[0, 1, 3, 9]

meta def repsM : Array (Array Nat) := (invRepWords.map (evalW 45 #[tXM, tYM])).toArray

meta def rep0M : Array Nat := repsM[0]!

meta def rep1M : Array Nat := repsM[1]!

meta def oneM : Array Nat := idA 45

end CertificateChecks.KernelSpor.PSp45

#kss_list CertificateChecks.KernelSpor.PSp45.tX CertificateChecks.KernelSpor.PSp45.tXM

#kss_list CertificateChecks.KernelSpor.PSp45.tY CertificateChecks.KernelSpor.PSp45.tYM

#kss_list CertificateChecks.KernelSpor.PSp45.tF CertificateChecks.KernelSpor.PSp45.tFM

#ks_rawchain CertificateChecks.KernelSpor.P45Q 45 6 16 CertificateChecks.KernelSpor.PSp45.SP
  CertificateChecks.KernelSpor.PSp45.baseP 2 CertificateChecks.KernelSpor.PSp45.wordsP

#ks_rawchain CertificateChecks.KernelSpor.A45Q 45 6 16 CertificateChecks.KernelSpor.PSp45.SA
  CertificateChecks.KernelSpor.PSp45.baseA 3 CertificateChecks.KernelSpor.PSp45.wordsA

#kss_classes CertificateChecks.KernelSpor.P45CL 45 6 CertificateChecks.KernelSpor.PSp45.tXM
  CertificateChecks.KernelSpor.PSp45.tYM CertificateChecks.KernelSpor.PSp45.repsM

namespace CertificateChecks.KernelSpor.PSp45

@[expose] noncomputable def One : Nat := CFSG.KC.Enum.pidn 45 6

@[expose] noncomputable def R0 : Nat := (P45CL.getD 0 (0, 0, 0, [], [], [], [])).2.2.1

@[expose] noncomputable def R1 : Nat := (P45CL.getD 1 (0, 0, 0, [], [], [], [])).2.2.1

end CertificateChecks.KernelSpor.PSp45

#kss_cntord CertificateChecks.KernelSpor.P45X CertificateChecks.KernelSpor.P45Q 45 6
  CertificateChecks.KernelSpor.PSp45.SP CertificateChecks.KernelSpor.PSp45.baseP
  CertificateChecks.KernelSpor.PSp45.One CertificateChecks.KernelSpor.PSp45.oneM 2

#kss_cntword CertificateChecks.KernelSpor.P45Y0 CertificateChecks.KernelSpor.P45Q 45 6
  CertificateChecks.KernelSpor.PSp45.SP CertificateChecks.KernelSpor.PSp45.baseP 2 5
  CertificateChecks.KernelSpor.PSp45.ws45N CertificateChecks.KernelSpor.PSp45.R0
  CertificateChecks.KernelSpor.PSp45.rep0M

#kss_cntword CertificateChecks.KernelSpor.P45Y1 CertificateChecks.KernelSpor.P45Q 45 6
  CertificateChecks.KernelSpor.PSp45.SP CertificateChecks.KernelSpor.PSp45.baseP 2 5
  CertificateChecks.KernelSpor.PSp45.ws45N CertificateChecks.KernelSpor.PSp45.R1
  CertificateChecks.KernelSpor.PSp45.rep1M

end
