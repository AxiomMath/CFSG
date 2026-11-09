module

public import Certificates.Data.CFSGNative.ON.Certificate
public import Certificates.Kernel.SporSch.HN.GenNTree

public section

namespace CertificateChecks.KernelSpor.ONC

meta def mlM : List Nat :=
  (String.splitOn (include_str "Mats.0.txt") ",").map String.toNat!

meta def mvM : List Nat :=
  (String.splitOn (include_str "Mats.1.txt") ",").map String.toNat!

end CertificateChecks.KernelSpor.ONC

#kss_ntree CertificateChecks.KernelSpor.ONC.ML CertificateChecks.KernelSpor.ONC.mlM
#kss_ntree CertificateChecks.KernelSpor.ONC.MV CertificateChecks.KernelSpor.ONC.mvM

end
