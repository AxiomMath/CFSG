module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.Asc82FbarData
meta import Certificates.Data.Asc82FbarData
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelP1L43.FbarD

open CFSG.ComponentClassification.HarrisLit.P1.L43 CFSG.PSL3Four.Native Certificates.Asc82Fbar

meta def a (k : Nat) : Array Nat := tab80 k false

meta def idM : Array Nat := idTab 80

meta def iv (x : Array Nat) : Array Nat := CFSG.Monster.B.Co2.Native.invCand 80 x

meta def recOf (gs : Array (Array Nat)) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 80 idM gs[j]! t) gs.size idM 100000).tabs

meta def clOf (r gs : Array (Array Nat)) : Array (Array Nat) :=
  (r.map fun x => (gs ++ gs.map iv).map fun g => comp 80 x g).flatten

meta def witOf (r : Array (Array Nat)) (b : Array Nat) : Array (Array Nat) :=
  r.map fun x =>
    if comp 80 x x == idM && x != idM then
      (r.find? fun l => comp 80 x l == comp 80 l b).getD idM
    else idM

meta def gI : Array (Array Nat) := #[a 22222087, a 30806896]
meta def gO : Array (Array Nat) := #[a 28947042, a 5634355]
meta def gR : Array (Array Nat) := #[a 23098396, a 11712909]
meta def gM : Array (Array Nat) := #[a 18085123, a 27169507]

meta def codes : Array Nat :=
  #[15, 16, 17, 21, 22, 23, 28, 31, 34, 37, 41, 42, 46, 48, 53, 56, 59, 62, 65, 67, 69, 74, 75, 79]

meta def gK : Array (Array Nat) := codes.map fun c => a ((rhoPairs.lookup c).getD 0)

meta def idsI : Array (Array Nat) := #[idM, idM]
meta def idsK : Array (Array Nat) := gK.map fun _ => idM

meta def rI : Array (Array Nat) := recOf gI
meta def rO : Array (Array Nat) := recOf gO
meta def rR : Array (Array Nat) := recOf gR
meta def rM : Array (Array Nat) := recOf gM
meta def rK : Array (Array Nat) := recOf gK

meta def clI : Array (Array Nat) := clOf rI gI
meta def clO : Array (Array Nat) := clOf rO gO
meta def clR : Array (Array Nat) := clOf rR gR
meta def clK : Array (Array Nat) := clOf rK gK

meta def qI : Array (Array Nat) := #[a 37301281, a 23098396, a 11712909]
meta def qO : Array (Array Nat) := #[a 19250485]
meta def wI : Array (Array Nat) := witOf rI (a 37301281)
meta def wO : Array (Array Nat) := witOf rO (a 19250485)

meta def nK : Array (Array Nat) :=
  (rK.map fun x => gM.map fun g => comp 80 (comp 80 g x) (iv g)).flatten

meta def tK : Array (Array Nat) := (gK.map fun x => gK.map fun y => comp 80 x y).flatten

meta def sB : Array (Array Nat) :=
  #[a 37301281, a 38099616, iv (a 38099616), a 23098396, a 11712909, a 11821474,
    a 19250485, a 31901178, iv (a 31901178), a 38855539]

meta def iI : Array (Array Nat) := gI.map iv
meta def iO : Array (Array Nat) := gO.map iv
meta def iR : Array (Array Nat) := gR.map iv
meta def iM : Array (Array Nat) := gM.map iv
meta def iK : Array (Array Nat) := gK.map iv

end CertificateChecks.KernelP1L43.FbarD

#kmulh CertificateChecks.KernelP1L43.FI 80 7 CertificateChecks.KernelP1L43.FbarD.idsI
  CertificateChecks.KernelP1L43.FbarD.gI CertificateChecks.KernelP1L43.FbarD.idM 100000
#kmulh CertificateChecks.KernelP1L43.FO 80 7 CertificateChecks.KernelP1L43.FbarD.idsI
  CertificateChecks.KernelP1L43.FbarD.gO CertificateChecks.KernelP1L43.FbarD.idM 100000
#kmulh CertificateChecks.KernelP1L43.FR 80 7 CertificateChecks.KernelP1L43.FbarD.idsI
  CertificateChecks.KernelP1L43.FbarD.gR CertificateChecks.KernelP1L43.FbarD.idM 100000
#kmulh CertificateChecks.KernelP1L43.FM 80 7 CertificateChecks.KernelP1L43.FbarD.idsI
  CertificateChecks.KernelP1L43.FbarD.gM CertificateChecks.KernelP1L43.FbarD.idM 100000
#kmulh CertificateChecks.KernelP1L43.FK 80 7 CertificateChecks.KernelP1L43.FbarD.idsK
  CertificateChecks.KernelP1L43.FbarD.gK CertificateChecks.KernelP1L43.FbarD.idM 100000
#kfind CertificateChecks.KernelP1L43.FICl CertificateChecks.KernelP1L43.FbarD.rI
  CertificateChecks.KernelP1L43.FbarD.clI
#kfind CertificateChecks.KernelP1L43.FOCl CertificateChecks.KernelP1L43.FbarD.rO
  CertificateChecks.KernelP1L43.FbarD.clO
#kfind CertificateChecks.KernelP1L43.FRCl CertificateChecks.KernelP1L43.FbarD.rR
  CertificateChecks.KernelP1L43.FbarD.clR
#kfind CertificateChecks.KernelP1L43.FKCl CertificateChecks.KernelP1L43.FbarD.rK
  CertificateChecks.KernelP1L43.FbarD.clK
#kfind CertificateChecks.KernelP1L43.FIx CertificateChecks.KernelP1L43.FbarD.rI
  CertificateChecks.KernelP1L43.FbarD.qI
#kfind CertificateChecks.KernelP1L43.FOx CertificateChecks.KernelP1L43.FbarD.rO
  CertificateChecks.KernelP1L43.FbarD.qO
#kfind CertificateChecks.KernelP1L43.FIW CertificateChecks.KernelP1L43.FbarD.rI
  CertificateChecks.KernelP1L43.FbarD.wI
#kfind CertificateChecks.KernelP1L43.FOW CertificateChecks.KernelP1L43.FbarD.rO
  CertificateChecks.KernelP1L43.FbarD.wO
#kfind CertificateChecks.KernelP1L43.FMx CertificateChecks.KernelP1L43.FbarD.rM
  CertificateChecks.KernelP1L43.FbarD.gK
#kfind CertificateChecks.KernelP1L43.FKN CertificateChecks.KernelP1L43.FbarD.rK
  CertificateChecks.KernelP1L43.FbarD.nK
#kfind CertificateChecks.KernelP1L43.FKT CertificateChecks.KernelP1L43.FbarD.gK
  CertificateChecks.KernelP1L43.FbarD.tK
#kmisc_packarrs CertificateChecks.KernelP1L43.FB CertificateChecks.KernelP1L43.FbarD.sB 7
#kmisc_packarrs CertificateChecks.KernelP1L43.FII CertificateChecks.KernelP1L43.FbarD.iI 7
#kmisc_packarrs CertificateChecks.KernelP1L43.FOI CertificateChecks.KernelP1L43.FbarD.iO 7
#kmisc_packarrs CertificateChecks.KernelP1L43.FRI CertificateChecks.KernelP1L43.FbarD.iR 7
#kmisc_packarrs CertificateChecks.KernelP1L43.FMI CertificateChecks.KernelP1L43.FbarD.iM 7
#kmisc_packarrs CertificateChecks.KernelP1L43.FKI CertificateChecks.KernelP1L43.FbarD.iK 7

end
