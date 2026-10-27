module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import Certificates.Kernel.LocalComp.Child3Gen
public import Certificates.Kernel.LocalComp.M12Cent.Words
public meta import Certificates.Kernel.LocalComp.M12Cent.Words
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFusion
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFusion

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.M12Cent

open CFSG.KS.SporSch.MOCG CFSG.Sporadic.Schreier CFSG.ComponentClassification.M12Cover

@[expose] noncomputable def One12 : Nat := CFSG.KC.Enum.pidn 12 4

@[expose] noncomputable def One24 : Nat := CFSG.KC.Enum.pidn 24 5

meta def tA : Array Nat := (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Mathieu.m12gA).toArray

meta def tB : Array Nat := (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Mathieu.m12gB).toArray

meta def tA1 : Array Nat := (CFSG.Monster.B.Mathieu.imageList m12A1).toArray

meta def tB1 : Array Nat := (CFSG.Monster.B.Mathieu.imageList m12B1).toArray

meta def tS : Array Nat := (CFSG.Monster.B.Mathieu.imageList m12Sigma).toArray

meta def tZ : Array Nat := (CFSG.Monster.B.Mathieu.imageList (blockHom (permZ, permZ))).toArray

meta def base3 : Array Nat := #[0, 1, 2]

meta def S1 : Array (Array Nat) :=
  strongOf 12 (m12CentWords1.map (evalW 12 #[tA, tB])).toArray m12CentChainWords1

meta def S3 : Array (Array Nat) :=
  strongOf 12 (m12CentWords2.map (evalW 12 #[tA, tB])).toArray m12CentChainWords2

meta def S2 : Array (Array Nat) :=
  strongOf 24 ((m12CentWords1.map (evalW 24 #[tA1, tB1])).toArray.push tS) q2Words

meta def S4 : Array (Array Nat) :=
  strongOf 24 ((q4GWords.map (evalW 24 #[tA1, tB1])).toArray.push tS) q4Words

meta def S5 : Array (Array Nat) :=
  strongOf 24 ((m12SigmaCentWords.map (evalW 24 #[tA1, tB1])).toArray.push tS) q5Words

meta def G1 : Array (Array Nat) := S1.extract 0 4

meta def G3 : Array (Array Nat) := S3.extract 0 3

meta def G2 : Array (Array Nat) := S2.extract 0 5

meta def G4 : Array (Array Nat) := S4.extract 0 4

meta def RA1 : List (Array Nat) := k1Words.map (evalW 12 G1)

meta def RA3 : List (Array Nat) := k3Words.map (evalW 12 G3)

meta def RA2 : List (Array Nat) := q2RWords.map (evalW 24 G2)

meta def RA4 : List (Array Nat) := q4RWords.map (evalW 24 G4)

meta def id12 : Array Nat := idA 12

meta def id24 : Array Nat := idA 24

end CertificateChecks.KernelLC.M12Cent

#kss_list CertificateChecks.KernelLC.M12Cent.LA CertificateChecks.KernelLC.M12Cent.tA
#kss_list CertificateChecks.KernelLC.M12Cent.LB CertificateChecks.KernelLC.M12Cent.tB
#kss_list CertificateChecks.KernelLC.M12Cent.LA1 CertificateChecks.KernelLC.M12Cent.tA1
#kss_list CertificateChecks.KernelLC.M12Cent.LB1 CertificateChecks.KernelLC.M12Cent.tB1
#kss_list CertificateChecks.KernelLC.M12Cent.LS CertificateChecks.KernelLC.M12Cent.tS
#kss_list CertificateChecks.KernelLC.M12Cent.LZ CertificateChecks.KernelLC.M12Cent.tZ

#ks_perm CertificateChecks.KernelLC.M12Cent.PA 4 CertificateChecks.KernelLC.M12Cent.tA
#ks_perm CertificateChecks.KernelLC.M12Cent.PB 4 CertificateChecks.KernelLC.M12Cent.tB
#ks_perm CertificateChecks.KernelLC.M12Cent.PA1 5 CertificateChecks.KernelLC.M12Cent.tA1
#ks_perm CertificateChecks.KernelLC.M12Cent.PB1 5 CertificateChecks.KernelLC.M12Cent.tB1
#ks_perm CertificateChecks.KernelLC.M12Cent.PS 5 CertificateChecks.KernelLC.M12Cent.tS
#ks_perm CertificateChecks.KernelLC.M12Cent.PZ 5 CertificateChecks.KernelLC.M12Cent.tZ

#ks_rawchain CertificateChecks.KernelLC.M12Cent.C1 12 4 16 CertificateChecks.KernelLC.M12Cent.S1
  CertificateChecks.KernelLC.M12Cent.base3 4 CFSG.Sporadic.Schreier.m12CentChainWords1

#ks_rawchain CertificateChecks.KernelLC.M12Cent.C3 12 4 16 CertificateChecks.KernelLC.M12Cent.S3
  CertificateChecks.KernelLC.M12Cent.base3 3 CFSG.Sporadic.Schreier.m12CentChainWords2

#ks_rawchain CertificateChecks.KernelLC.M12Cent.Q2 24 5 16 CertificateChecks.KernelLC.M12Cent.S2
  CertificateChecks.KernelLC.M12Cent.base3 5 CertificateChecks.KernelLC.M12Cent.q2Words

#ks_rawchain CertificateChecks.KernelLC.M12Cent.Q4 24 5 16 CertificateChecks.KernelLC.M12Cent.S4
  CertificateChecks.KernelLC.M12Cent.base3 4 CertificateChecks.KernelLC.M12Cent.q4Words

#ks_rawchain CertificateChecks.KernelLC.M12Cent.Q5 24 5 16 CertificateChecks.KernelLC.M12Cent.S5
  CertificateChecks.KernelLC.M12Cent.base3 4 CertificateChecks.KernelLC.M12Cent.q5Words

#kss_cntord CertificateChecks.KernelLC.M12Cent.X1 CertificateChecks.KernelLC.M12Cent.C1 12 4
  CertificateChecks.KernelLC.M12Cent.S1 CertificateChecks.KernelLC.M12Cent.base3
  CertificateChecks.KernelLC.M12Cent.One12 CertificateChecks.KernelLC.M12Cent.id12 4

#kss_cntord CertificateChecks.KernelLC.M12Cent.X3 CertificateChecks.KernelLC.M12Cent.C3 12 4
  CertificateChecks.KernelLC.M12Cent.S3 CertificateChecks.KernelLC.M12Cent.base3
  CertificateChecks.KernelLC.M12Cent.One12 CertificateChecks.KernelLC.M12Cent.id12 4

#kss_cntord CertificateChecks.KernelLC.M12Cent.X2 CertificateChecks.KernelLC.M12Cent.Q2 24 5
  CertificateChecks.KernelLC.M12Cent.S2 CertificateChecks.KernelLC.M12Cent.base3
  CertificateChecks.KernelLC.M12Cent.One24 CertificateChecks.KernelLC.M12Cent.id24 4

#kss_cntord CertificateChecks.KernelLC.M12Cent.X4 CertificateChecks.KernelLC.M12Cent.Q4 24 5
  CertificateChecks.KernelLC.M12Cent.S4 CertificateChecks.KernelLC.M12Cent.base3
  CertificateChecks.KernelLC.M12Cent.One24 CertificateChecks.KernelLC.M12Cent.id24 4

#kss_cntord CertificateChecks.KernelLC.M12Cent.X5 CertificateChecks.KernelLC.M12Cent.Q5 24 5
  CertificateChecks.KernelLC.M12Cent.S5 CertificateChecks.KernelLC.M12Cent.base3
  CertificateChecks.KernelLC.M12Cent.One24 CertificateChecks.KernelLC.M12Cent.id24 4

#lc_reps CertificateChecks.KernelLC.M12Cent.R1 4 CertificateChecks.KernelLC.M12Cent.G1
  CertificateChecks.KernelLC.M12Cent.RA1

#lc_reps CertificateChecks.KernelLC.M12Cent.R3 4 CertificateChecks.KernelLC.M12Cent.G3
  CertificateChecks.KernelLC.M12Cent.RA3

#lc_reps CertificateChecks.KernelLC.M12Cent.R2 5 CertificateChecks.KernelLC.M12Cent.G2
  CertificateChecks.KernelLC.M12Cent.RA2

#lc_reps CertificateChecks.KernelLC.M12Cent.R4 5 CertificateChecks.KernelLC.M12Cent.G4
  CertificateChecks.KernelLC.M12Cent.RA4

end
