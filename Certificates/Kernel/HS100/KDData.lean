module

public import Certificates.Kernel.LocalComp.Child3Gen
public import Certificates.Kernel.SporSch.Mathieu.Gen
public import Certificates.Kernel.HS100.ChainData
public import Certificates.Data.Kernel.Child3
public import Certificates.Data.HSThreeKD
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import Certificates.Data.HSThreeKD
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelHS100.KDE

open CFSG.KS.SporSch.MOCG CFSG.LocalAnalysis.GLTheoremA.KD264HS

meta def GM : Array (Array Nat) := #[CFSG.RankThree.Native.hs100Arr 0, CFSG.RankThree.Native.hs100Arr 1]

meta def repsL : List (Array Nat) := [evalW 100 GM zW]

end CertificateChecks.KernelHS100.KDE

public section

set_option maxRecDepth 400000

#lc_reps CertificateChecks.KernelHS100.KD3 7 CertificateChecks.KernelHS100.KDE.GM
  CertificateChecks.KernelHS100.KDE.repsL

namespace CertificateChecks.KernelHS100

open CFSG.KC.Child3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def HPI (j : Nat) : Nat := pinvS 100 7 (mask 7) (HP.F j)

@[expose] noncomputable def kdW (wd : List Int) : Nat := wordK 100 7 (mask 7) (pidn 100 7) HP.F HPI wd

@[expose] noncomputable def kp (p q : Nat) : Nat := pcomp 100 7 (mask 7) p q

@[expose] noncomputable def kdBlk (k : Nat) : Bool :=
  (List.range' (1000 * k) (min 1000 (KD3.N - 1000 * k))).all
    (repK 100 7 KD3.GP KD3.GIP 2 KD3.CS KD3.OFF KD3.CI KD3.E KD3.P KD3.L KD3.K KD3.S KD3.SI KD3.N
      130000)

end CertificateChecks.KernelHS100

end
