module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.RowsCmd
meta import Certificates.Data.HSFiveU35Check

namespace CertificateChecks.KernelMaxD2.HSU35E

open CFSG.PSL3Four.Native Certificates.MaxD2Perm Certificates.HSU35

meta def omM : Array Nat := Id.run do
  let gs := dataU.gT
  let mut m : Array Nat := Array.replicate 100 0
  m := m.set! 0 1
  for _ in [0:100] do
    for p in [0:100] do
      if m[p]! == 1 then
        for g in gs do
          m := m.set! g[p]! 1
  return m

end CertificateChecks.KernelMaxD2.HSU35E

public section

#krows CertificateChecks.KernelMaxD2.HSU35E.OM CertificateChecks.KernelMaxD2.HSU35E.omM

end
