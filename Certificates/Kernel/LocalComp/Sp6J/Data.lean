module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import Certificates.Kernel.LocalComp.Sp6J.Words
public meta import Certificates.Kernel.LocalComp.Sp6J.Words
public meta import CFSG.Monster.B.Mathieu.Order
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.LocalAnalysis.EvenSmallLie.Sp6JConditionInputs
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JConditionInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Sp6J

open CFSG.KS.SporSch.MOCG CFSG.EvenSmallLie.Sp6

meta def XG : Array (Array Nat) :=
  #[(CFSG.Monster.B.Mathieu.imageList (CFSG.Sporadic.Schreier.tab sp6A)).toArray,
    (CFSG.Monster.B.Mathieu.imageList (CFSG.Sporadic.Schreier.tab sp6B)).toArray]

meta def SX : Array (Array Nat) := strongOf 36 XG xQWords

meta def baseX : Array Nat := #[0, 1, 2, 4, 8, 12]

meta def CG1 : Array (Array Nat) := (c1Words.map (evalW 36 XG)).toArray

meta def CG2 : Array (Array Nat) := (c2Words.map (evalW 36 XG)).toArray

meta def CG3 : Array (Array Nat) := (c3Words.map (evalW 36 XG)).toArray

meta def CG4 : Array (Array Nat) := (c4Words.map (evalW 36 XG)).toArray

meta def SC1 : Array (Array Nat) := strongOf 36 CG1 q1Words

meta def SC2 : Array (Array Nat) := strongOf 36 CG2 q2Words

meta def SC3 : Array (Array Nat) := strongOf 36 CG3 q3Words

meta def SC4 : Array (Array Nat) := strongOf 36 CG4 q4Words

meta def base1 : Array Nat := #[0, 1, 4, 2, 12]

meta def base2 : Array Nat := #[0, 1, 4, 2]

meta def base3 : Array Nat := #[0, 1, 2, 4]

meta def id36 : Array Nat := idA 36

end CertificateChecks.KernelLC.Sp6J

#ks_rawchain CertificateChecks.KernelLC.Sp6J.XQ 36 6 36 CertificateChecks.KernelLC.Sp6J.SX
  CertificateChecks.KernelLC.Sp6J.baseX 2 CertificateChecks.KernelLC.Sp6J.xQWords

#ks_rawchain CertificateChecks.KernelLC.Sp6J.C1Q 36 6 36 CertificateChecks.KernelLC.Sp6J.SC1
  CertificateChecks.KernelLC.Sp6J.base1 5 CertificateChecks.KernelLC.Sp6J.q1Words

#ks_rawchain CertificateChecks.KernelLC.Sp6J.C2Q 36 6 36 CertificateChecks.KernelLC.Sp6J.SC2
  CertificateChecks.KernelLC.Sp6J.base2 3 CertificateChecks.KernelLC.Sp6J.q2Words

#ks_rawchain CertificateChecks.KernelLC.Sp6J.C3Q 36 6 36 CertificateChecks.KernelLC.Sp6J.SC3
  CertificateChecks.KernelLC.Sp6J.base3 6 CertificateChecks.KernelLC.Sp6J.q3Words

#ks_rawchain CertificateChecks.KernelLC.Sp6J.C4Q 36 6 36 CertificateChecks.KernelLC.Sp6J.SC4
  CertificateChecks.KernelLC.Sp6J.base3 6 CertificateChecks.KernelLC.Sp6J.q4Words

namespace CertificateChecks.KernelLC.Sp6J

@[expose] noncomputable def One36 : Nat := CFSG.KC.Enum.pidn 36 6

@[expose] def xCS : List Nat := 763 :: List.replicate 35 124

end CertificateChecks.KernelLC.Sp6J

end
