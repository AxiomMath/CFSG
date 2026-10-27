module

public import Certificates.Kernel.A45Cls.Data

public section

namespace CertificateChecks.KernelA45

@[expose] def b0W : List (List ℕ) :=
  [[0], [1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 1], [1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2],
    [2, 1, 0, 1, 1, 2, 0, 1, 0, 1, 0, 1]]

@[expose] def b0Gen : Array (Array ℕ) := (b0W.map fun w => img (wv w)).toArray

@[expose] def cyIx0 : ℕ := 2461107089

@[expose] def cyIx1 : ℕ := 1122060593

@[expose] def cyIx2 : ℕ := 852567009

@[expose] def cyTab : ℕ := 7025641807245475840

end CertificateChecks.KernelA45

end
