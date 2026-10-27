module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import Certificates.Kernel.LocalComp.Child3Gen
public import Certificates.Kernel.LocalComp.ExcU6.Words
public meta import Certificates.Kernel.LocalComp.ExcU6.Words
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcU6Inputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcU6Inputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.ExcU6

open CFSG.KS.SporSch.MOCG CFSG.Sporadic.Schreier CFSG.EvenSmallLie.UnitarySix
open CFSG.ComponentClassification.RankTwoClassical.ExcU6

@[expose] noncomputable def One693 : Nat := CFSG.KC.Enum.pidn 693 10

meta def LA : Array (Array Nat) := letterArrs

meta def SG : Array (Array Nat) := ((aWords ++ tWords).map (evalW 693 LA)).toArray

meta def ALA : Array Nat := (alWords.map fun w => CFSG.KS.RawGen.pack 10 (evalW 693 LA w)).toArray

meta def G2 : Array (Array Nat) := (s2Words.map (evalW 693 SG)).toArray

meta def G3 : Array (Array Nat) := (s3Words.map (evalW 693 SG)).toArray

meta def S2 : Array (Array Nat) := strongOf 693 G2 s2QWords

meta def S3 : Array (Array Nat) := strongOf 693 G3 s3QWords

meta def RSL : List (Array Nat) := sRepWords.map (evalW 693 SG)

meta def R2L : List (Array Nat) := r2Words.map (evalW 693 G2)

meta def R3L : List (Array Nat) := r3Words.map (evalW 693 G3)

meta def t2 : Array Nat := evalW 693 SG [2, 3]

meta def t3 : Array Nat := evalW 693 SG [3, 6, 9]

meta def tJ : Array Nat := evalW 693 SG [1]

meta def base2 : Array Nat := #[1, 45, 3]

meta def base3 : Array Nat := #[1, 3, 45]

meta def id693 : Array Nat := idA 693

end CertificateChecks.KernelLC.ExcU6

#kss_list CertificateChecks.KernelLC.ExcU6.ALL CertificateChecks.KernelLC.ExcU6.ALA

#ks_perm CertificateChecks.KernelLC.ExcU6.X2 10 CertificateChecks.KernelLC.ExcU6.t2
#ks_perm CertificateChecks.KernelLC.ExcU6.X3 10 CertificateChecks.KernelLC.ExcU6.t3
#ks_perm CertificateChecks.KernelLC.ExcU6.J1 10 CertificateChecks.KernelLC.ExcU6.tJ

end
