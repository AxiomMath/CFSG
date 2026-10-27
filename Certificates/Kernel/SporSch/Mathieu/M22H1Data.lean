module

public import Certificates.Kernel.SporSch.Mathieu.M22OData
public import Certificates.Kernel.LocalComp.Child3Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.M22Inputs
public meta import Certificates.Kernel.SporSch.Mathieu.M22OData
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.M22Inputs
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts
public meta import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M22H1

open CFSG.KS.SporSch.MOCG CertificateChecks.KernelSporSch.M22OC
open CFSG.EvenSporadicStandard.HypOne.M22

@[expose] noncomputable def One22 : Nat := CFSG.KC.Enum.pidn 22 5

meta def id22 : Array Nat := idA 22

meta def G3 : Array (Array Nat) := SC1.extract 0 3

meta def zM : Array Nat := evalW 22 #[tAM, tBM, tDM] zWordA

meta def GA : Array (Array Nat) := G3.push zM

meta def GO1 : Array (Array Nat) := (SO1.extract 0 3).push orepsM[0]!

meta def GO2 : Array (Array Nat) := (SO2.extract 0 3).push orepsM[1]!

meta def SA : Array (Array Nat) := strongOf 22 GA kChainWordsA

meta def SKO1 : Array (Array Nat) := strongOf 22 GO1 kChainWordsO1

meta def SKO2 : Array (Array Nat) := strongOf 22 GO2 kChainWordsO2

meta def baseA : Array Nat := #[0, 1, 3, 2]

meta def baseO2 : Array Nat := #[0, 1, 2, 3]

meta def RI : List (Array Nat) := innerFourWords.map (evalW 22 G3)

meta def RKA : List (Array Nat) := kFourWordsA.map (evalW 22 GA)

meta def RKO1 : List (Array Nat) := kFourWordsO1.map (evalW 22 GO1)

meta def RKO2 : List (Array Nat) := kFourWordsO2.map (evalW 22 GO2)

end CertificateChecks.KernelSporSch.M22H1

#ks_rawchain CertificateChecks.KernelSporSch.M22KA 22 5 16 CertificateChecks.KernelSporSch.M22H1.SA
  CertificateChecks.KernelSporSch.M22H1.baseA 4 CFSG.EvenSporadicStandard.HypOne.M22.kChainWordsA

#ks_rawchain CertificateChecks.KernelSporSch.M22KO1 22 5 16
  CertificateChecks.KernelSporSch.M22H1.SKO1 CertificateChecks.KernelSporSch.M22OC.baseC 4
  CFSG.EvenSporadicStandard.HypOne.M22.kChainWordsO1

#ks_rawchain CertificateChecks.KernelSporSch.M22KO2 22 5 16
  CertificateChecks.KernelSporSch.M22H1.SKO2 CertificateChecks.KernelSporSch.M22H1.baseO2 4
  CFSG.EvenSporadicStandard.HypOne.M22.kChainWordsO2

#kss_cntord CertificateChecks.KernelSporSch.M22H1XI CertificateChecks.KernelSporSch.M22C1 22 5
  CertificateChecks.KernelSporSch.M22OC.SC1 CertificateChecks.KernelSporSch.M22OC.baseC
  CertificateChecks.KernelSporSch.M22H1.One22 CertificateChecks.KernelSporSch.M22H1.id22 4

#kss_cntord CertificateChecks.KernelSporSch.M22H1XA CertificateChecks.KernelSporSch.M22KA 22 5
  CertificateChecks.KernelSporSch.M22H1.SA CertificateChecks.KernelSporSch.M22H1.baseA
  CertificateChecks.KernelSporSch.M22H1.One22 CertificateChecks.KernelSporSch.M22H1.id22 4

#kss_cntord CertificateChecks.KernelSporSch.M22H1XO1 CertificateChecks.KernelSporSch.M22KO1 22 5
  CertificateChecks.KernelSporSch.M22H1.SKO1 CertificateChecks.KernelSporSch.M22OC.baseC
  CertificateChecks.KernelSporSch.M22H1.One22 CertificateChecks.KernelSporSch.M22H1.id22 4

#kss_cntord CertificateChecks.KernelSporSch.M22H1XO2 CertificateChecks.KernelSporSch.M22KO2 22 5
  CertificateChecks.KernelSporSch.M22H1.SKO2 CertificateChecks.KernelSporSch.M22H1.baseO2
  CertificateChecks.KernelSporSch.M22H1.One22 CertificateChecks.KernelSporSch.M22H1.id22 4

#lc_reps CertificateChecks.KernelSporSch.M22H1RI 5 CertificateChecks.KernelSporSch.M22H1.G3
  CertificateChecks.KernelSporSch.M22H1.RI

#lc_reps CertificateChecks.KernelSporSch.M22H1RA 5 CertificateChecks.KernelSporSch.M22H1.GA
  CertificateChecks.KernelSporSch.M22H1.RKA

#lc_reps CertificateChecks.KernelSporSch.M22H1RO1 5 CertificateChecks.KernelSporSch.M22H1.GO1
  CertificateChecks.KernelSporSch.M22H1.RKO1

#lc_reps CertificateChecks.KernelSporSch.M22H1RO2 5 CertificateChecks.KernelSporSch.M22H1.GO2
  CertificateChecks.KernelSporSch.M22H1.RKO2

end
