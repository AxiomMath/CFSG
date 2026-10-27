module

public import Certificates.Kernel.Sporadic.OddCore.BTupCmd
public import Certificates.Kernel.Sporadic.RowsWCmd
public meta import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Sporadic.SuzRecog.SuzL34Cert.CheckModel
meta import CFSG.Sporadic.SuzRecog.C1ModelTests
import CFSG.Open.LocalVocabulary

namespace CertificateChecks.KernelSpor.SuzBtLD

open CFSG.Sporadic.SuzRecog.SuzL34Cert CFSG.PSL3Four.Native CFSG.Sporadic.SuzRecog
  CFSG.Sporadic.SuzRecog.C1Model

meta def bkey (x : Array Nat) : Nat := x[0]! + 2048 * x[2]! + 4194304 * x[1]!

meta def l1S : Array (Array Nat) := (l1Tabs ()).qsort fun a b => bkey a < bkey b

meta def rk (x : Array Nat) : Nat := (l1S.findIdx? fun y => bkey y == bkey x).getD 99

meta def sigG : Array (Array Nat) := (decs nl1Decs).map fun g =>
  let gi := invTab 1782 g
  (Array.range 16).map fun s => rk (conjTab 1782 g gi l1S[s]!)

meta def sB : Array Nat := (decs l1Decs).map rk

meta def ckey (g : Array Nat) : Array Nat :=
  let gi := invTab 1782 g
  (l1S.map fun x => bkey (conjTab 1782 g gi x)).qsort (· < ·)

meta def mn (w : List Nat) : Nat := (ckey (decTab (w, 0))).foldl (· + ·) 0

meta def conjW : Array (List Nat) := Id.run do
  let mut ws : Array (List Nat) := #[[]]
  let mut ks : Array (Array Nat) := #[ckey (decTab ([], 0))]
  let mut q := 0
  while q < ws.size && ws.size < 200 do
    for i in [0:10] do
      let w := i :: ws[q]!
      let k := ckey (decTab (w, 0))
      if !ks.contains k then
        ws := ws.push w
        ks := ks.push k
    q := q + 1
  return ws

meta def conjS : Array (List Nat) := conjW.qsort fun a b => mn a < mn b

open CFSG.KC.Eval in
meta def cWStep : Step := fun _ =>
  return #[(.anonymous, Val.list (conjS.map fun r => Val.list (r.toArray.map fun x => Val.nat x)))]

meta def cPre : Array Nat := (conjS.map fun w =>
  let gi := invTab 1782 (decTab (w, 0))
  #[gi[0]!, gi[2]!, gi[1]!]).flatten

meta def cSv : Array Nat := conjS.map mn

end CertificateChecks.KernelSpor.SuzBtLD

public section

set_option maxRecDepth 400000

#kbtup CertificateChecks.KernelSpor.SuzBtLS 16 4 CertificateChecks.KernelSpor.SuzBtLD.sigG
  CertificateChecks.KernelSpor.SuzBtLD.sB

#kc_eval CertificateChecks.KernelSpor SuzBtLC.W CertificateChecks.KernelSpor.SuzBtLD.cWStep

#krowsw CertificateChecks.KernelSpor.SuzBtLC.PRE 16 CertificateChecks.KernelSpor.SuzBtLD.cPre

#krowsw CertificateChecks.KernelSpor.SuzBtLC.SV 64 CertificateChecks.KernelSpor.SuzBtLD.cSv

end
