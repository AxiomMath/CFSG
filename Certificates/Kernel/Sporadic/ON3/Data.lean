
module

public import Certificates.Kernel.Sporadic.ON.GenTab
public import Certificates.Kernel.Sporadic.ON.GenLv
public import Certificates.Kernel.Sporadic.ON2.GenWords
public meta import CFSG.Sporadic.Schreier.ONCheckAuxInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON3

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

meta def zM : Array Nat := zArr
meta def qM : Array Nat := qArr
meta def cM : Array Nat := cArr
meta def ciM : Array Nat := pinvCand nPts cArr
meta def d1M : Array Nat := (wordArrs Data.intersectionWords)[0]!
meta def d2M : Array Nat := (wordArrs Data.intersectionWords)[1]!
meta def d3M : Array Nat := (wordArrs Data.intersectionWords)[2]!
meta def d4M : Array Nat := (wordArrs Data.intersectionWords)[3]!
meta def m2M : Array Nat := (wordArrs Data.MWords)[1]!
meta def m3M : Array Nat := (wordArrs Data.MWords)[2]!
meta def l1M : Array Nat := (wordArrs Data.LWords)[0]!
meta def l2M : Array Nat := (wordArrs Data.LWords)[1]!
meta def wM : Array Nat := cqcArr 2

meta def wordsM : Array (List Int) :=
  let ws : Array (List Int) := #[Data.zWord, Data.centerGeneratorWord, Data.pairConjugatorWord,
    Data.intersectionWords[0]!, Data.intersectionWords[1]!, Data.intersectionWords[2]!,
    Data.intersectionWords[3]!, Data.MWords[1]!, Data.MWords[2]!, Data.LWords[0]!,
    Data.LWords[1]!, Data.TWords[0]!, Data.TWords[1]!, Data.TWords[2]!, Data.TWords[3]!,
    Data.TWords[4]!, Data.TWords[5]!, Data.TChain.strongWords[6]!, Data.TChain.strongWords[7]!,
    Data.MChain.strongWords[3]!, Data.MChain.strongWords[4]!, Data.LChain.strongWords[2]!,
    Data.LChain.strongWords[3]!]
  ws ++ ws.map fun w => w.reverse.map fun l => -l

meta def tStrongM : Array (Array Nat) := TStrong
meta def mStrongM : Array (Array Nat) := MStrong
meta def lStrongM : Array (Array Nat) := LStrong
meta def baseM : Array Nat := Data.TChain.base

end CertificateChecks.KernelSpor.ON3

#kon_table CertificateChecks.KernelSpor.ON3T.Z CertificateChecks.KernelSpor.ON3.zM
#kon_table CertificateChecks.KernelSpor.ON3T.Q CertificateChecks.KernelSpor.ON3.qM
#kon_table CertificateChecks.KernelSpor.ON3T.C CertificateChecks.KernelSpor.ON3.cM
#kon_table CertificateChecks.KernelSpor.ON3T.CI CertificateChecks.KernelSpor.ON3.ciM
#kon_table CertificateChecks.KernelSpor.ON3T.D1 CertificateChecks.KernelSpor.ON3.d1M
#kon_table CertificateChecks.KernelSpor.ON3T.D2 CertificateChecks.KernelSpor.ON3.d2M
#kon_table CertificateChecks.KernelSpor.ON3T.D3 CertificateChecks.KernelSpor.ON3.d3M
#kon_table CertificateChecks.KernelSpor.ON3T.D4 CertificateChecks.KernelSpor.ON3.d4M
#kon_table CertificateChecks.KernelSpor.ON3T.M2 CertificateChecks.KernelSpor.ON3.m2M
#kon_table CertificateChecks.KernelSpor.ON3T.M3 CertificateChecks.KernelSpor.ON3.m3M
#kon_table CertificateChecks.KernelSpor.ON3T.L1 CertificateChecks.KernelSpor.ON3.l1M
#kon_table CertificateChecks.KernelSpor.ON3T.L2 CertificateChecks.KernelSpor.ON3.l2M
#kon_table CertificateChecks.KernelSpor.ON3T.W CertificateChecks.KernelSpor.ON3.wM

#kon_words CertificateChecks.KernelSpor.ON3W CertificateChecks.KernelSpor.ON3.wordsM

#kon_levels CertificateChecks.KernelSpor.ON3LT CertificateChecks.KernelSpor.ON3.tStrongM
  CertificateChecks.KernelSpor.ON3.baseM 3

#kon_levels CertificateChecks.KernelSpor.ON3LM CertificateChecks.KernelSpor.ON3.mStrongM
  CertificateChecks.KernelSpor.ON3.baseM 3

#kon_levels CertificateChecks.KernelSpor.ON3LL CertificateChecks.KernelSpor.ON3.lStrongM
  CertificateChecks.KernelSpor.ON3.baseM 3
