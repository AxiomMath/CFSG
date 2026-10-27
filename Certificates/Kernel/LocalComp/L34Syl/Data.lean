module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.CFSGNative.PSL3Four.L34Syl
meta import Certificates.Data.CFSGNative.PSL3Four.L34Syl

namespace CertificateChecks.KernelLC.L34Syl

open CFSG.PSL3Four.Native

meta def pM : Array (Array Nat) := pGens

meta def fM : Array (Array Nat) := fGens ()

meta def nM : Array (Array Nat) := #[nT, invTab 42 nT]

meta def id42 : Array Nat := idTab 42

meta def wM : Array (Array Nat) := Id.run do
  let E := (enumBFS 42 pGens 64).tabs
  let I := E.map (invTab 42)
  let mut out : Array (Array Nat) := #[]
  for i in [0:E.size] do
    let mut w : Array Nat := #[0, 0, 0]
    for j in [0:E.size] do
      if E[j]! == I[i]! then
        w := w.set! 2 j
    let central := (List.range E.size).all fun j => comp 42 E[i]! E[j]! == comp 42 E[j]! E[i]!
    if central then
      let mut done := false
      for a in [0:E.size] do
        for b in [0:E.size] do
          if !done && commTab 42 E[a]! E[b]! I[a]! I[b]! == E[i]! then
            w := (w.set! 0 a).set! 1 b
            done := true
    out := out.push w
  return out

end CertificateChecks.KernelLC.L34Syl

public section

set_option maxRecDepth 400000

#kpenum CertificateChecks.KernelLC.L34SyP 42 6 false CertificateChecks.KernelLC.L34Syl.pM
  CertificateChecks.KernelLC.L34Syl.pM CertificateChecks.KernelLC.L34Syl.id42 64
#kpenum CertificateChecks.KernelLC.L34SyF 42 6 false CertificateChecks.KernelLC.L34Syl.fM
  CertificateChecks.KernelLC.L34Syl.fM CertificateChecks.KernelLC.L34Syl.id42 16
#kmisc_packarrs CertificateChecks.KernelLC.L34SyN.N CertificateChecks.KernelLC.L34Syl.nM 6
#kmisc_packarrs CertificateChecks.KernelLC.L34SyW.W CertificateChecks.KernelLC.L34Syl.wM 6

end
