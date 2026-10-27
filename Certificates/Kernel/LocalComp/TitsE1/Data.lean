module

public import Certificates.Data.CoreE1Tits
import Certificates.Kernel.LocalComp.BfsGen
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.CoreE1Tits
public import Certificates.Data.Kernel.BfsPin

namespace CertificateChecks.KernelLC.TitsE1Data

open CFSG.PSL3Four.Native Certificates.CoreE1Perm
open Certificates.FusD2Perm (powT wordT)

meta def D : Certificates.CoreE1Perm.Data := titsE1Data ()

meta def sG : List (Array Nat) := (sGens D).toList

meta def gM : Array (Array Nat) := gsT D

meta def giM : Array (Array Nat) := giT D

meta def gW (i j : Nat) : Array Nat := (gT D (D.es.getD i (default : Entry)))[j]!

meta def wM : Array (Array Nat) :=
  #[zT D, xT D 0, xT D 1, xT D 2, xT D 3] ++
    ((List.range 8).map fun k => gW (k / 2) (k % 2)).toArray

meta def wiM : Array (Array Nat) := ((List.range 8).map fun k => invTab 1755 (gW (k / 2) (k % 2))).toArray

meta def zxM : Array (Array Nat) :=
  ((List.range 36).map fun k => zx D (k / 9) (k % 9 / 3) (k % 3)).toArray ++
    ((List.range 3).map fun a => powT 1755 (zT D) a).toArray

meta def hT (i : Nat) : Array Nat :=
  let e : Entry := D.es.getD i default
  wordT 1755 (gT D e) (gTi D e) e.hW

meta def hcM : Array (Array Nat) :=
  ((List.range 12).map fun k =>
    let i := k / 3
    let h := hT i
    let hi := invTab 1755 h
    if k % 3 == 0 then h else if k % 3 == 1 then hi
    else comp 1755 (zT D) (comp 1755 (comp 1755 h (zT D)) hi)).toArray

end CertificateChecks.KernelLC.TitsE1Data

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelLC.TitsE1S CertificateChecks.KernelLC.TitsE1Data.sG 1755 11
#kmisc_packarrs CertificateChecks.KernelLC.TitsE1.GA CertificateChecks.KernelLC.TitsE1Data.gM 11
#kmisc_packarrs CertificateChecks.KernelLC.TitsE1.GI CertificateChecks.KernelLC.TitsE1Data.giM 11
#kmisc_packarrs CertificateChecks.KernelLC.TitsE1.W CertificateChecks.KernelLC.TitsE1Data.wM 11
#kmisc_packarrs CertificateChecks.KernelLC.TitsE1.WI CertificateChecks.KernelLC.TitsE1Data.wiM 11
#kmisc_packarrs CertificateChecks.KernelLC.TitsE1.ZX CertificateChecks.KernelLC.TitsE1Data.zxM 11
#kmisc_packarrs CertificateChecks.KernelLC.TitsE1.HC CertificateChecks.KernelLC.TitsE1Data.hcM 11

end
