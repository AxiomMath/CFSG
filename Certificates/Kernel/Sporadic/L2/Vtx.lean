
module

public import Certificates.Kernel.Sporadic.L2.G4
public import Certificates.Kernel.Sporadic.L2.KA0
public import Certificates.Kernel.Sporadic.L2.KA1
public import Certificates.Kernel.Sporadic.L2.KA2
public import Certificates.Kernel.Sporadic.L2.KA3
public import Certificates.Kernel.Sporadic.L2.KA4
public import Certificates.Kernel.Sporadic.L2.KA5
public import Certificates.Kernel.Sporadic.L2.KW
public import Certificates.Kernel.Sporadic.L2.KG
public import Certificates.Kernel.Sporadic.L2.KS0
public import Certificates.Kernel.Sporadic.L2.KS1
public import Certificates.Kernel.Sporadic.L2.KL

public section

#kon_join CertificateChecks.KernelSpor.L2K.aAll CertificateChecks.KernelSpor.L2K.aSl 567
#kon_join CertificateChecks.KernelSpor.L2K.wAll CertificateChecks.KernelSpor.L2K.wSl 54
#kon_join CertificateChecks.KernelSpor.L2K.grAll CertificateChecks.KernelSpor.L2K.grSl 18
#kon_join CertificateChecks.KernelSpor.L2K.teAll CertificateChecks.KernelSpor.L2K.teSl 6
#kon_join CertificateChecks.KernelSpor.L2K.stAll CertificateChecks.KernelSpor.L2K.stSl 77

namespace CertificateChecks.KernelSpor.L2G

open CFSG.KC.Enum CFSG.KS CertificateChecks.KernelSpor.L2K

theorem vtxOK : VtxOK where
  a := slices (len := 5) (k := 567) (by norm_num) (by norm_num) aAll
  w := slices (len := 3) (k := 54) (by norm_num) (by norm_num) wAll
  sA := kSortA
  sT := kSortT

theorem hgr : ∀ x < 2997, grChk x = true := by
  intro x hx
  by_cases h : x < 2880
  · exact slices (len := 160) (k := 18) (by norm_num) (by norm_num) grAll x h
  · unfold grChk grK
    rw [nblt_f (show ¬ x < 2835 by omega)]

theorem hte : ∀ x < 2997, teG x = true :=
  slices (len := 500) (k := 6) (by norm_num) (by norm_num) teAll

theorem hst : ∀ i < 76545, stepK i = true := by
  intro i hi
  have h := slices (len := 1000) (k := 77) (by norm_num) (by norm_num) stAll i hi
  unfold stepG at h
  rwa [show Nat.blt i 76545 = true from nblt.2 hi] at h

theorem aOK_k : CFSG.Sporadic.SuzRecog.LevelTwo.aOK = true := aOK_true vtxOK

theorem vOK_k : CFSG.Sporadic.SuzRecog.LevelTwo.vOK = true := vOK_true vtxOK

theorem graphOK_k : CFSG.Sporadic.SuzRecog.LevelTwo.graphOK = true := graphOK_true vtxOK hgr

theorem elimOK_k : CFSG.Sporadic.SuzRecog.LevelTwo.elimOK = true := elimOK_true hst hte

end CertificateChecks.KernelSpor.L2G

end
