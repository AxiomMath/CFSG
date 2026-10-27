module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import Certificates.Kernel.LocalComp.Child3Gen
public import Certificates.Kernel.LocalComp.ExcSp6.Words
public meta import Certificates.Kernel.LocalComp.ExcSp6.Words
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcSp6Inputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcSp6Inputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.ExcSp6

open CFSG.KS.SporSch.MOCG CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3
open CFSG.ComponentClassification.RankTwoClassical.ExcSp6

@[expose] noncomputable def One276 : Nat := CFSG.KC.Enum.pidn 276 9

meta def TG : Array (Array Nat) := (Array.range 8).map fun k => co3TArrs[k]!

meta def STQ : Array (Array Nat) := strongOf 276 TG tQWords

meta def SAG : Array (Array Nat) := (saWords.map (evalW 276 TG)).toArray

meta def SSA : Array (Array Nat) := strongOf 276 SAG saQWords

meta def SBG : Array (Array Nat) := (sbWords.map (evalW 276 TG)).toArray

meta def SSB : Array (Array Nat) := strongOf 276 SBG sbQWords

meta def RTL : List (Array Nat) := tRepWords.map (evalW 276 TG)

meta def RAL : List (Array Nat) := raWords.map (evalW 276 SAG)

meta def RBL : List (Array Nat) := rbWords.map (evalW 276 SBG)

meta def tXA : Array Nat := evalW 276 TG [3, 1, 3, 2]

meta def tXB : Array Nat := evalW 276 TG [1, 5]

meta def base3 : Array Nat := #[0, 1, 2]

meta def base01 : Array Nat := #[0, 1]

meta def base02 : Array Nat := #[0, 2]

meta def id276 : Array Nat := idA 276

end CertificateChecks.KernelLC.ExcSp6

#ks_perm CertificateChecks.KernelLC.ExcSp6.XA 9 CertificateChecks.KernelLC.ExcSp6.tXA
#ks_perm CertificateChecks.KernelLC.ExcSp6.XB 9 CertificateChecks.KernelLC.ExcSp6.tXB

#ks_rawchain CertificateChecks.KernelLC.ExcSp6.TQ 276 9 16 CertificateChecks.KernelLC.ExcSp6.STQ
  CertificateChecks.KernelLC.ExcSp6.base3 8 CertificateChecks.KernelLC.ExcSp6.tQWords

#ks_rawchain CertificateChecks.KernelLC.ExcSp6.SA 276 9 16 CertificateChecks.KernelLC.ExcSp6.SSA
  CertificateChecks.KernelLC.ExcSp6.base01 7 CertificateChecks.KernelLC.ExcSp6.saQWords

#ks_rawchain CertificateChecks.KernelLC.ExcSp6.SB 276 9 16 CertificateChecks.KernelLC.ExcSp6.SSB
  CertificateChecks.KernelLC.ExcSp6.base02 5 CertificateChecks.KernelLC.ExcSp6.sbQWords

#kss_cntord CertificateChecks.KernelLC.ExcSp6.NT CertificateChecks.KernelLC.ExcSp6.TQ 276 9
  CertificateChecks.KernelLC.ExcSp6.STQ CertificateChecks.KernelLC.ExcSp6.base3
  CertificateChecks.KernelLC.ExcSp6.One276 CertificateChecks.KernelLC.ExcSp6.id276 2

#kss_cntord CertificateChecks.KernelLC.ExcSp6.NA CertificateChecks.KernelLC.ExcSp6.SA 276 9
  CertificateChecks.KernelLC.ExcSp6.SSA CertificateChecks.KernelLC.ExcSp6.base01
  CertificateChecks.KernelLC.ExcSp6.One276 CertificateChecks.KernelLC.ExcSp6.id276 2

#kss_cntord CertificateChecks.KernelLC.ExcSp6.NB CertificateChecks.KernelLC.ExcSp6.SB 276 9
  CertificateChecks.KernelLC.ExcSp6.SSB CertificateChecks.KernelLC.ExcSp6.base02
  CertificateChecks.KernelLC.ExcSp6.One276 CertificateChecks.KernelLC.ExcSp6.id276 2

#lc_reps CertificateChecks.KernelLC.ExcSp6.RT 9 CertificateChecks.KernelLC.ExcSp6.TG
  CertificateChecks.KernelLC.ExcSp6.RTL

#lc_reps CertificateChecks.KernelLC.ExcSp6.RA 9 CertificateChecks.KernelLC.ExcSp6.SAG
  CertificateChecks.KernelLC.ExcSp6.RAL

#lc_reps CertificateChecks.KernelLC.ExcSp6.RB 9 CertificateChecks.KernelLC.ExcSp6.SBG
  CertificateChecks.KernelLC.ExcSp6.RBL

end
