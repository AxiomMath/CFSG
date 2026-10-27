module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
import Certificates.Kernel.Sporadic.OddCore.RowsCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.L34OuterData
meta import Certificates.Kernel.L34Outer.Words

namespace CertificateChecks.KernelL34Outer

open CFSG.PSL3Four.Native Certificates.L34Outer

meta def tw (w : List Int) : Array Nat := Certificates.FusD2Perm.wordT 42 tGens tGensI w

meta def gpM : Array (Array Nat) := gTabs
meta def gpiM : Array (Array Nat) := gTabs.map (invTab 42)
meta def hpM : Array (Array Nat) := ((l34OuterData.es.drop 1).flatMap (·.hs)).toArray.map tw
meta def hpiM : Array (Array Nat) := hpM.map (invTab 42)
meta def pG : Array (Array Nat) := pGens l34OuterData
meta def e0G : Array (Array Nat) := eGens (l34OuterData.es[0]!)
meta def e1G : Array (Array Nat) := eGens (l34OuterData.es[1]!)
meta def e2G : Array (Array Nat) := eGens (l34OuterData.es[2]!)
meta def e3G : Array (Array Nat) := eGens (l34OuterData.es[3]!)
meta def idT : Array Nat := idTab 42

meta def eTabs : Array (Array (Array Nat)) :=
  #[e0G, e1G, e2G, e3G].map fun g => (enumBFS 42 g 9).tabs

meta def hintOf (t : Array Nat) : Nat := Id.run do
  for e in [0:4] do
    for j in [0:(eTabs[e]!).size] do
      if (eTabs[e]!)[j]! == t then return 16 * e + j
  return 0

meta def cvM : Array Nat := (enumBFS 42 pG 27).tabs.map hintOf
meta def phM : Array Nat :=
  let P := (enumBFS 42 pG 27).tabs
  (#[e0G, e1G, e2G, e3G].flatMap id).map fun t => (P.findIdx? (· == t)).getD 0

meta def yhM : Array Nat :=
  ((l34OuterData.es.drop 1).flatMap (·.ys)).toArray.map fun y => hintOf (tw y) % 16

meta def xpM : Array (Array Nat) :=
  xW.toArray.map (Certificates.FusD2Perm.wordT 42 gTabs rGensI)

end CertificateChecks.KernelL34Outer

public section

#kmisc_packarrs CertificateChecks.KernelL34Outer.GP CertificateChecks.KernelL34Outer.gpM 6
#kmisc_packarrs CertificateChecks.KernelL34Outer.GPI CertificateChecks.KernelL34Outer.gpiM 6
#kmisc_packarrs CertificateChecks.KernelL34Outer.HP CertificateChecks.KernelL34Outer.hpM 6
#kmisc_packarrs CertificateChecks.KernelL34Outer.HPI CertificateChecks.KernelL34Outer.hpiM 6
#kmisc_packarrs CertificateChecks.KernelL34Outer.XP CertificateChecks.KernelL34Outer.xpM 6
#krows CertificateChecks.KernelL34Outer.CV CertificateChecks.KernelL34Outer.cvM
#krows CertificateChecks.KernelL34Outer.YH CertificateChecks.KernelL34Outer.yhM
#krows CertificateChecks.KernelL34Outer.PH CertificateChecks.KernelL34Outer.phM

#kpenum CertificateChecks.KernelL34Outer.PE 42 6 false CertificateChecks.KernelL34Outer.pG
  CertificateChecks.KernelL34Outer.pG CertificateChecks.KernelL34Outer.idT 27
#kpenum CertificateChecks.KernelL34Outer.E0 42 6 false CertificateChecks.KernelL34Outer.e0G
  CertificateChecks.KernelL34Outer.e0G CertificateChecks.KernelL34Outer.idT 9
#kpenum CertificateChecks.KernelL34Outer.E1 42 6 false CertificateChecks.KernelL34Outer.e1G
  CertificateChecks.KernelL34Outer.e1G CertificateChecks.KernelL34Outer.idT 9
#kpenum CertificateChecks.KernelL34Outer.E2 42 6 false CertificateChecks.KernelL34Outer.e2G
  CertificateChecks.KernelL34Outer.e2G CertificateChecks.KernelL34Outer.idT 9
#kpenum CertificateChecks.KernelL34Outer.E3 42 6 false CertificateChecks.KernelL34Outer.e3G
  CertificateChecks.KernelL34Outer.e3G CertificateChecks.KernelL34Outer.idT 9

end
