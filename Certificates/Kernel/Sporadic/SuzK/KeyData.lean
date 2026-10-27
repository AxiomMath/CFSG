module

public import Certificates.Data.CFSGNative.Suz.Certificate
public import Certificates.Data.Kernel.Spor.Row
public import Certificates.Kernel.Sporadic.RowsWCmd
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public meta import Certificates.Data.CFSGNative.Suz.Certificate

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzK

open CFSG.Sporadic.Suz.Native

meta def keyN (X : Array W) : Nat :=
  (List.range 64).foldl (fun a i => a + X[i]!.p.toNat * 2 ^ (64 * i) +
    X[i]!.m.toNat * 2 ^ (4096 + 64 * i)) 0

meta def kdM : Array Nat := (orbitData ()).keys.map keyN

meta def soM : Array Nat := (List.range kdM.size).toArray.qsort fun i j => kdM[i]! < kdM[j]!

meta def soiM : Array Nat := Id.run do
  let mut r := Array.replicate soM.size 0
  for i in [0:soM.size] do
    r := r.set! soM[i]! i
  return r

end CertificateChecks.KernelSpor.SuzK

#krowsw CertificateChecks.KernelSpor.SuzK.KD 8192 CertificateChecks.KernelSpor.SuzK.kdM
#krows CertificateChecks.KernelSpor.SuzK.SO CertificateChecks.KernelSpor.SuzK.soM
#krows CertificateChecks.KernelSpor.SuzK.SOI CertificateChecks.KernelSpor.SuzK.soiM

end
