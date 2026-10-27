module

public import Certificates.Kernel.Sporadic.SuzInv.Text1
public import Certificates.Kernel.LocalComp.B0SuzData
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.SuzRecog.LevelTwoCoverWCheck
meta import CFSG.Sporadic.SuzRecog.LevelTwoCoverWCheck
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib
meta import Mathlib

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzXS CFSG.Sporadic.SuzRecog.LevelTwoData.xStrongHex

#kmisc_hexflat CertificateChecks.KernelSpor.SuzXS CFSG.Sporadic.SuzRecog.LevelTwoData.xStrongHex
  3 1782 11 2

namespace CertificateChecks.KernelSpor.SuzW

open CFSG.Sporadic.SuzRecog.LevelTwo CFSG.Monster.B.Co2.Native

meta def cntM : Nat := 343

meta def giM : Array (Array Nat) := gensInv

meta def tM : Array (Array Nat) := aPts.extract 0 cntM

meta def vM : Array (Array Nat) :=
  (Array.range cntM).map fun i =>
    if i == 0 then idA 1782 else compA 1782 aPts[aPar[i]!]! gensInv[aLab[i]!]!

meta def plM : Array (Array Nat) :=
  (Array.range cntM).map fun i => #[2 * aPar[i]! + aLab[i]!]

meta def fpM : Array (Array Nat) := tM.map fun a => #[fp a]

meta def posM : Array (Array Nat) :=
  (Array.range (2 * aPar[cntM - 1]! + aLab[cntM - 1]! + 1)).map fun e =>
    #[aIdx.getD (fpConj gens[e % 2]! gensInv[e % 2]! aPts[e / 2]!) 2835]

meta def qfM : Array (Array Nat) :=
  (Array.range 128).map fun j =>
    let p := CFSG.ComponentClassification.AS81.SuzB0.qProd (j / 2)
    #[if j % 2 == 0 then fp p else fp (compA 1782 p t1Arr)]

meta def jM : Array (Array Nat) :=
  #[#[((List.range 128).find? fun j => (qfM[j]!)[0]! == fp aPts[p1]!).getD 128]]

meta def ciM : Array (Array Nat) := #[invCand 1782 WCheck.c3Arr, invCand 1782 WCheck.c6Arr]

meta def wcM : Array (Array Nat) :=
  let y1 := compA 1782 ciM[1]! ciM[0]!
  let y2 := compA 1782 (CFSG.ComponentClassification.AS81.SuzB0.qProd 1) y1
  let y3 := compA 1782 WCheck.c6Arr y2
  #[compA 1782 t1Arr aPts[p1]!, y1, y2, y3, compA 1782 WCheck.c3Arr y3]

end CertificateChecks.KernelSpor.SuzW

#kmisc_packarrs CertificateChecks.KernelSpor.SuzWGI CertificateChecks.KernelSpor.SuzW.giM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzWT CertificateChecks.KernelSpor.SuzW.tM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzWV CertificateChecks.KernelSpor.SuzW.vM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzWPL CertificateChecks.KernelSpor.SuzW.plM 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzWFP CertificateChecks.KernelSpor.SuzW.fpM 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzWPOS CertificateChecks.KernelSpor.SuzW.posM 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzWQF CertificateChecks.KernelSpor.SuzW.qfM 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzWJ CertificateChecks.KernelSpor.SuzW.jM 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzWCI CertificateChecks.KernelSpor.SuzW.ciM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzWC CertificateChecks.KernelSpor.SuzW.wcM 11

end
