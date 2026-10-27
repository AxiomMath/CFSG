module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import Certificates.Kernel.LocalComp.Child3Gen
public import Certificates.Kernel.LocalComp.ExcO8W.Words
public meta import Certificates.Kernel.LocalComp.ExcO8W.Words
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8WInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8WInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.ExcO8W

open CFSG.KS.SporSch.MOCG CFSG.Sporadic.Schreier CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ComponentClassification.RankTwoClassical.ExcO8W

@[expose] noncomputable def One240 : Nat := CFSG.KC.Enum.pidn 240 8

meta def TG : Array (Array Nat) := (tWords.map (evalW 240 reflArrs)).toArray

meta def STQ : Array (Array Nat) := strongOf 240 TG tQWords

meta def G24 : Array (Array Nat) := (s24Words.map (evalW 240 TG)).toArray

meta def G60 : Array (Array Nat) := (s60Words.map (evalW 240 TG)).toArray

meta def G4 : Array (Array Nat) := (s4Words.map (evalW 240 TG)).toArray

meta def G8 : Array (Array Nat) := (s8Words.map (evalW 240 TG)).toArray

meta def S24 : Array (Array Nat) := strongOf 240 G24 s24QWords

meta def S60 : Array (Array Nat) := strongOf 240 G60 s60QWords

meta def S4 : Array (Array Nat) := strongOf 240 G4 s4QWords

meta def S8 : Array (Array Nat) := strongOf 240 G8 s8QWords

meta def RTL : List (Array Nat) := tRepWords.map (evalW 240 TG)

meta def R24L : List (Array Nat) := r24Words.map (evalW 240 G24)

meta def R60L : List (Array Nat) := r60Words.map (evalW 240 G60)

meta def R4L : List (Array Nat) := r4Words.map (evalW 240 G4)

meta def R8L : List (Array Nat) := r8Words.map (evalW 240 G8)

meta def t24 : Array Nat := evalW 240 TG [3, 2, 1]

meta def t60 : Array Nat := evalW 240 TG [1]

meta def t4 : Array Nat := evalW 240 TG [5, 4, 3, 2, 1]

meta def t8 : Array Nat := evalW 240 TG [10, 8, 1]

meta def base7 : Array Nat := #[0, 1, 4, 8, 12, 16, 20]

meta def base5 : Array Nat := #[0, 1, 4, 12, 20]

meta def id240 : Array Nat := idA 240

meta def relab (bs : List Nat) : Array Nat := Id.run do
  let order := bs ++ (List.range 240).filter fun x => !bs.contains x
  let mut s := Array.replicate 240 0
  for i in [0:240] do
    s := s.set! order[i]! i
  return s

meta def sig7 : Array Nat := relab [0, 1, 4, 8, 12, 16, 20]

meta def sig5 : Array Nat := relab [0, 1, 4, 12, 20]

meta def cjA (s g : Array Nat) : Array Nat := comp s (comp g (invA s))

meta def CST : Array (Array Nat) := STQ.map (cjA sig7)

meta def CS24 : Array (Array Nat) := S24.map (cjA sig7)

meta def CS60 : Array (Array Nat) := S60.map (cjA sig7)

meta def CS4 : Array (Array Nat) := S4.map (cjA sig7)

meta def CS8 : Array (Array Nat) := S8.map (cjA sig5)

meta def sig7i : Array Nat := invA sig7

meta def sig5i : Array Nat := invA sig5

meta def baseC7 : Array Nat := #[0, 1, 2, 3, 4, 5, 6]

meta def baseC5 : Array Nat := #[0, 1, 2, 3, 4]

end CertificateChecks.KernelLC.ExcO8W

#ks_perm CertificateChecks.KernelLC.ExcO8W.X24 8 CertificateChecks.KernelLC.ExcO8W.t24
#ks_perm CertificateChecks.KernelLC.ExcO8W.X60 8 CertificateChecks.KernelLC.ExcO8W.t60
#ks_perm CertificateChecks.KernelLC.ExcO8W.X4 8 CertificateChecks.KernelLC.ExcO8W.t4
#ks_perm CertificateChecks.KernelLC.ExcO8W.X8 8 CertificateChecks.KernelLC.ExcO8W.t8

#ks_rawchain CertificateChecks.KernelLC.ExcO8W.TQ 240 8 16 CertificateChecks.KernelLC.ExcO8W.STQ
  CertificateChecks.KernelLC.ExcO8W.base7 13 CertificateChecks.KernelLC.ExcO8W.tQWords

#ks_rawchain CertificateChecks.KernelLC.ExcO8W.Q24 240 8 16 CertificateChecks.KernelLC.ExcO8W.S24
  CertificateChecks.KernelLC.ExcO8W.base7 9 CertificateChecks.KernelLC.ExcO8W.s24QWords

#ks_rawchain CertificateChecks.KernelLC.ExcO8W.Q60 240 8 16 CertificateChecks.KernelLC.ExcO8W.S60
  CertificateChecks.KernelLC.ExcO8W.base7 9 CertificateChecks.KernelLC.ExcO8W.s60QWords

#ks_rawchain CertificateChecks.KernelLC.ExcO8W.Q4 240 8 16 CertificateChecks.KernelLC.ExcO8W.S4
  CertificateChecks.KernelLC.ExcO8W.base7 8 CertificateChecks.KernelLC.ExcO8W.s4QWords

#ks_rawchain CertificateChecks.KernelLC.ExcO8W.Q8 240 8 16 CertificateChecks.KernelLC.ExcO8W.S8
  CertificateChecks.KernelLC.ExcO8W.base5 5 CertificateChecks.KernelLC.ExcO8W.s8QWords

#ks_perm CertificateChecks.KernelLC.ExcO8W.Sig7 8 CertificateChecks.KernelLC.ExcO8W.sig7
#ks_perm CertificateChecks.KernelLC.ExcO8W.Sig7I 8 CertificateChecks.KernelLC.ExcO8W.sig7i
#ks_perm CertificateChecks.KernelLC.ExcO8W.Sig5 8 CertificateChecks.KernelLC.ExcO8W.sig5
#ks_perm CertificateChecks.KernelLC.ExcO8W.Sig5I 8 CertificateChecks.KernelLC.ExcO8W.sig5i

#ks_rawchain CertificateChecks.KernelLC.ExcO8W.CQT 240 8 16 CertificateChecks.KernelLC.ExcO8W.CST
  CertificateChecks.KernelLC.ExcO8W.baseC7 13 CertificateChecks.KernelLC.ExcO8W.tQWords

#ks_rawchain CertificateChecks.KernelLC.ExcO8W.CQ24 240 8 16 CertificateChecks.KernelLC.ExcO8W.CS24
  CertificateChecks.KernelLC.ExcO8W.baseC7 9 CertificateChecks.KernelLC.ExcO8W.s24QWords

#ks_rawchain CertificateChecks.KernelLC.ExcO8W.CQ60 240 8 16 CertificateChecks.KernelLC.ExcO8W.CS60
  CertificateChecks.KernelLC.ExcO8W.baseC7 9 CertificateChecks.KernelLC.ExcO8W.s60QWords

#ks_rawchain CertificateChecks.KernelLC.ExcO8W.CQ4 240 8 16 CertificateChecks.KernelLC.ExcO8W.CS4
  CertificateChecks.KernelLC.ExcO8W.baseC7 8 CertificateChecks.KernelLC.ExcO8W.s4QWords

#ks_rawchain CertificateChecks.KernelLC.ExcO8W.CQ8 240 8 16 CertificateChecks.KernelLC.ExcO8W.CS8
  CertificateChecks.KernelLC.ExcO8W.baseC5 5 CertificateChecks.KernelLC.ExcO8W.s8QWords

#kss_cntord CertificateChecks.KernelLC.ExcO8W.CNT CertificateChecks.KernelLC.ExcO8W.CQT 240 8
  CertificateChecks.KernelLC.ExcO8W.CST CertificateChecks.KernelLC.ExcO8W.baseC7
  CertificateChecks.KernelLC.ExcO8W.One240 CertificateChecks.KernelLC.ExcO8W.id240 2

#kss_cntord CertificateChecks.KernelLC.ExcO8W.CN24 CertificateChecks.KernelLC.ExcO8W.CQ24 240 8
  CertificateChecks.KernelLC.ExcO8W.CS24 CertificateChecks.KernelLC.ExcO8W.baseC7
  CertificateChecks.KernelLC.ExcO8W.One240 CertificateChecks.KernelLC.ExcO8W.id240 2

#kss_cntord CertificateChecks.KernelLC.ExcO8W.CN60 CertificateChecks.KernelLC.ExcO8W.CQ60 240 8
  CertificateChecks.KernelLC.ExcO8W.CS60 CertificateChecks.KernelLC.ExcO8W.baseC7
  CertificateChecks.KernelLC.ExcO8W.One240 CertificateChecks.KernelLC.ExcO8W.id240 2

#kss_cntord CertificateChecks.KernelLC.ExcO8W.CN4 CertificateChecks.KernelLC.ExcO8W.CQ4 240 8
  CertificateChecks.KernelLC.ExcO8W.CS4 CertificateChecks.KernelLC.ExcO8W.baseC7
  CertificateChecks.KernelLC.ExcO8W.One240 CertificateChecks.KernelLC.ExcO8W.id240 2

#kss_cntord CertificateChecks.KernelLC.ExcO8W.CN8 CertificateChecks.KernelLC.ExcO8W.CQ8 240 8
  CertificateChecks.KernelLC.ExcO8W.CS8 CertificateChecks.KernelLC.ExcO8W.baseC5
  CertificateChecks.KernelLC.ExcO8W.One240 CertificateChecks.KernelLC.ExcO8W.id240 2

#lc_reps CertificateChecks.KernelLC.ExcO8W.RT 8 CertificateChecks.KernelLC.ExcO8W.TG
  CertificateChecks.KernelLC.ExcO8W.RTL

#lc_reps CertificateChecks.KernelLC.ExcO8W.R24 8 CertificateChecks.KernelLC.ExcO8W.G24
  CertificateChecks.KernelLC.ExcO8W.R24L

#lc_reps CertificateChecks.KernelLC.ExcO8W.R60 8 CertificateChecks.KernelLC.ExcO8W.G60
  CertificateChecks.KernelLC.ExcO8W.R60L

#lc_reps CertificateChecks.KernelLC.ExcO8W.R4 8 CertificateChecks.KernelLC.ExcO8W.G4
  CertificateChecks.KernelLC.ExcO8W.R4L

#lc_reps CertificateChecks.KernelLC.ExcO8W.R8 8 CertificateChecks.KernelLC.ExcO8W.G8
  CertificateChecks.KernelLC.ExcO8W.R8L

end
