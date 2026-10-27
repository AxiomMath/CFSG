module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.Sporadic.SuzRecog.TwistTests
import CFSG.Open.LocalVocabulary

namespace CertificateChecks.KernelSpor.SuzFb

open CFSG.Sporadic.SuzRecog CFSG.ComponentClassification.AS81.SuzB0 CFSG.PSL3Four.Native
  CFSG.Monster.B.Co2.Native

meta def idR : Array Nat := idTab 64

meta def mG : Array (Array Nat) := matTabs

meta def ipL : List Nat := invPos

meta def lifts : Array (Array Nat) := invPos.toArray.map liftTab

meta def commAt (x q : Array Nat) : Nat :=
  ((List.range 1782).find? fun y => !(x[q[w0Tab[y]!]!]! == w0Tab[x[q[y]!]!]!)).map (· + 1)
    |>.getD 0

meta def kindRow (x : Array Nat) : Array Nat :=
  (List.range 128).toArray.map fun j => kind x j + 4 * commAt x qElts[j]!

meta def kinds : Array (Array Nat) := lifts.map kindRow

meta def conjL : List Nat := invPos.map fun i =>
  ((List.range 25920).find? fun c => conjTest matEnum.tabs[i]! matEnum.tabs[c]! lBTab).map (· + 1)
    |>.getD 0

end CertificateChecks.KernelSpor.SuzFb

public section

set_option maxRecDepth 400000

#kpenum CertificateChecks.KernelSpor.SuzFbE 64 7 false CertificateChecks.KernelSpor.SuzFb.mG
  CertificateChecks.KernelSpor.SuzFb.mG CertificateChecks.KernelSpor.SuzFb.idR 25920

#knatlist CertificateChecks.KernelSpor.SuzFbIL CertificateChecks.KernelSpor.SuzFb.ipL
#knatlist CertificateChecks.KernelSpor.SuzFbCL CertificateChecks.KernelSpor.SuzFb.conjL

#kmisc_packarrs CertificateChecks.KernelSpor.SuzFbL CertificateChecks.KernelSpor.SuzFb.lifts 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzFbW CertificateChecks.KernelSpor.SuzFb.kinds 13

end
