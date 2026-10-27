module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import Certificates.Kernel.LocalComp.Child3Gen
public import Certificates.Kernel.LocalComp.ExcO8E.Words
public meta import Certificates.Kernel.LocalComp.ExcO8E.Words
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8EInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8EInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.ExcO8E

open CFSG.KS.SporSch.MOCG CFSG.Sporadic.Schreier CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ComponentClassification.RankTwoClassical.ExcO8E CFSG.Monster.B.Co2.Native

@[expose] noncomputable def One480 : Nat := CFSG.KC.Enum.pidn 480 9

meta def EG : Array (Array Nat) := eArrs

meta def tE0 : Array Nat := eArrs[0]!
meta def tE1 : Array Nat := eArrs[1]!
meta def tE2 : Array Nat := eArrs[2]!
meta def tE3 : Array Nat := eArrs[3]!
meta def tE4 : Array Nat := eArrs[4]!
meta def tE5 : Array Nat := eArrs[5]!
meta def tE6 : Array Nat := eArrs[6]!
meta def tE7 : Array Nat := eArrs[7]!

meta def tZ1 : Array Nat := pairA negArr (CFSG.Monster.B.Co2.Native.idA 240)

meta def tZ2 : Array Nat := pairA (CFSG.Monster.B.Co2.Native.idA 240) negArr

meta def tZ3 : Array Nat := pairA negArr negArr

meta def GE : Array (Array Nat) := (seWords.map (evalW 480 EG)).toArray

meta def SSE : Array (Array Nat) := strongOf 480 GE seQWords

meta def G48 : Array (Array Nat) := (s48Words.map (evalW 480 GE)).toArray

meta def G16 : Array (Array Nat) := (s16Words.map (evalW 480 GE)).toArray

meta def S48 : Array (Array Nat) := strongOf 480 G48 s48QWords

meta def S16 : Array (Array Nat) := strongOf 480 G16 s16QWords

meta def REL : List (Array Nat) := seRepWords.map (evalW 480 GE)

meta def R48L : List (Array Nat) := r48Words.map (evalW 480 G48)

meta def R16L : List (Array Nat) := r16Words.map (evalW 480 G16)

meta def t48 : Array Nat := evalW 480 GE [4, 3, 2, 4, 3, 1, 2, 4, 3, 1, 2, 4, 3, 1, 2, 1]

meta def t16 : Array Nat := evalW 480 GE [4, 2, 3, 1, 2, 4, 1, 2, 3, 1, 2, 1]

meta def base4 : Array Nat := #[0, 1, 4, 240]

meta def base3 : Array Nat := #[0, 1, 240]

meta def id480 : Array Nat := CFSG.KS.SporSch.MOCG.idA 480

end CertificateChecks.KernelLC.ExcO8E

#ks_perm CertificateChecks.KernelLC.ExcO8E.E0 9 CertificateChecks.KernelLC.ExcO8E.tE0
#ks_perm CertificateChecks.KernelLC.ExcO8E.E1 9 CertificateChecks.KernelLC.ExcO8E.tE1
#ks_perm CertificateChecks.KernelLC.ExcO8E.E2 9 CertificateChecks.KernelLC.ExcO8E.tE2
#ks_perm CertificateChecks.KernelLC.ExcO8E.E3 9 CertificateChecks.KernelLC.ExcO8E.tE3
#ks_perm CertificateChecks.KernelLC.ExcO8E.E4 9 CertificateChecks.KernelLC.ExcO8E.tE4
#ks_perm CertificateChecks.KernelLC.ExcO8E.E5 9 CertificateChecks.KernelLC.ExcO8E.tE5
#ks_perm CertificateChecks.KernelLC.ExcO8E.E6 9 CertificateChecks.KernelLC.ExcO8E.tE6
#ks_perm CertificateChecks.KernelLC.ExcO8E.E7 9 CertificateChecks.KernelLC.ExcO8E.tE7
#ks_perm CertificateChecks.KernelLC.ExcO8E.Z1 9 CertificateChecks.KernelLC.ExcO8E.tZ1
#ks_perm CertificateChecks.KernelLC.ExcO8E.Z2 9 CertificateChecks.KernelLC.ExcO8E.tZ2
#ks_perm CertificateChecks.KernelLC.ExcO8E.Z3 9 CertificateChecks.KernelLC.ExcO8E.tZ3
#ks_perm CertificateChecks.KernelLC.ExcO8E.X48 9 CertificateChecks.KernelLC.ExcO8E.t48
#ks_perm CertificateChecks.KernelLC.ExcO8E.X16 9 CertificateChecks.KernelLC.ExcO8E.t16

end
