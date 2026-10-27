module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.SuzRecog.RootTwistChecks
meta import CFSG.Sporadic.SuzRecog.RootTwistChecks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzRTX CFSG.Sporadic.SuzRecog.RootTwistData.xTwHex

#kmisc_hexflat CertificateChecks.KernelSpor.SuzRTX CFSG.Sporadic.SuzRecog.RootTwistData.xTwHex
  3 1782 11 1

#ks_chars CertificateChecks.KernelSpor.SuzRTY CFSG.Sporadic.SuzRecog.RootTwistData.yTwHex

#kmisc_hexflat CertificateChecks.KernelSpor.SuzRTY CFSG.Sporadic.SuzRecog.RootTwistData.yTwHex
  3 1782 11 1

namespace CertificateChecks.KernelSpor.SuzRT

open CFSG.Sporadic.SuzRecog.RootTwistCheck CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.SuzRecog.LevelTwo (fp actV Elt genP genQ)

meta def iM : Array (Array Nat) :=
  #[invCand 1782 CFSG.Sporadic.SuzRecog.RootTwistData.xTwArr,
    invCand 1782 CFSG.Sporadic.SuzRecog.RootTwistData.yTwArr]

meta def key (g : Array Nat) : Nat :=
  fp (CFSG.Sporadic.SuzRecog.ModelGroupsCheck.conjA g CFSG.Sporadic.SuzRecog.LevelTwoData.rhoArr)

meta def tM : Array (Array Nat) := cTr

meta def tiM : Array (Array Nat) := cTr.map (invCand 1782)

meta def plM : Array (Array Nat) := (Array.range cTr.size).map fun i => #[2 * cPar[i]! + cLab[i]!]

meta def fpM : Array (Array Nat) := cTr.map fun g => #[key g]

meta def posM : Array (Array Nat) :=
  (Array.range (2 * cTr.size)).map fun e =>
    #[cTab.getD (key (compA 1782 cGens[e % 2]! cTr[e / 2]!)) 960]

meta def srtL : Array Nat := (Array.range cTr.size).qsort fun x y => key cTr[x]! < key cTr[y]!

meta def srtM : Array (Array Nat) := srtL.map fun x => #[x]

meta def sriM : Array (Array Nat) :=
  (Array.range cTr.size).map fun i => #[(srtL.findIdx? (· == i)).getD 0]

meta def orb (gs : Array Elt) (b : Nat) : Array Nat × Array Nat × Array Nat := Id.run do
  let mut pts : Array Nat := #[b]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut seen : Std.HashSet Nat := (∅ : Std.HashSet Nat).insert b
  for h in [0:2997] do
    if h < pts.size then
      for s in [0:gs.size] do
        let y := actV gs[s]!.1 gs[s]!.2 pts[h]!
        if !seen.contains y then
          seen := seen.insert y
          pts := pts.push y
          par := par.push h
          lab := lab.push s
  return (pts, par, lab)

meta def orbs : Array (Array Nat × Array Nat × Array Nat) := #[orb genP 2835, orb genQ 0]

meta def otM : Array (Array Nat) := orbs.map fun o => o.1

meta def oplM : Array (Array Nat) :=
  orbs.map fun o => (Array.range o.1.size).map fun i => 6 * o.2.1[i]! + o.2.2[i]!

meta def oposM : Array (Array Nat) :=
  (Array.range 2).map fun j =>
    let o := orbs[j]!
    let gs := if j == 0 then genP else genQ
    (Array.range (6 * o.1.size)).map fun e =>
      o.1.idxOf (actV gs[e % 6]!.1 gs[e % 6]!.2 o.1[e / 6]!)

meta def ovpM : Array (Array Nat) :=
  orbs.map fun o => (Array.range 2997).map fun v => o.1.idxOf v

end CertificateChecks.KernelSpor.SuzRT

#kmisc_packarrs CertificateChecks.KernelSpor.SuzRTI CertificateChecks.KernelSpor.SuzRT.iM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRCT CertificateChecks.KernelSpor.SuzRT.tM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRCTI CertificateChecks.KernelSpor.SuzRT.tiM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRCPL CertificateChecks.KernelSpor.SuzRT.plM 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRCFP CertificateChecks.KernelSpor.SuzRT.fpM 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRCPOS CertificateChecks.KernelSpor.SuzRT.posM 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRCSRT CertificateChecks.KernelSpor.SuzRT.srtM 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRCSRI CertificateChecks.KernelSpor.SuzRT.sriM 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzROT CertificateChecks.KernelSpor.SuzRT.otM 12
#kmisc_packarrs CertificateChecks.KernelSpor.SuzROPL CertificateChecks.KernelSpor.SuzRT.oplM 15
#kmisc_packarrs CertificateChecks.KernelSpor.SuzROPOS CertificateChecks.KernelSpor.SuzRT.oposM 12
#kmisc_packarrs CertificateChecks.KernelSpor.SuzROVP CertificateChecks.KernelSpor.SuzRT.ovpM 12

end
