
module

public import Certificates.Kernel.A45Cls.Data
public import Certificates.Data.ParrottPSp43

public section

namespace CertificateChecks.Parrott946

open CertificateChecks.KernelA45 CFSG.RankThree.GF2n.Parrott

@[expose] def rS1 : Array ℕ := img sigma1

@[expose] def rS12 : Array ℕ := img (sigma1 * sigma2)

@[expose] def rS12i : Array ℕ := img (sigma1 * sigma2⁻¹)

@[expose] def wA : List (List ℕ) :=
  [[0], [1, 1, 2, 0, 1, 0, 1, 1, 1, 1, 2, 0, 1, 1, 1], [2, 0],
    [1, 0, 1, 2, 1, 1, 2, 1, 0, 1, 0, 1, 1], [1, 1, 0, 1, 0, 1, 0, 1, 2, 1, 1, 1, 2, 0],
    [1, 1, 2, 0, 1, 2, 1, 1, 2, 1, 1, 2, 1], [2, 1, 2, 0, 1, 1, 1, 0, 1, 2, 1, 1, 2, 1, 1],
    [1, 1, 0, 1, 1, 0, 1, 2, 1, 1, 2, 1, 1, 1, 0], [1, 2, 0, 1, 1, 2, 1, 1],
    [2, 0, 1, 0, 1, 2, 1, 0, 1, 1, 1, 0], [1, 1, 0, 1, 1, 1, 0],
    [1, 2, 0, 1, 0, 1, 1, 2, 0, 1, 1, 0]]

@[expose] def wP : List (List ℕ) :=
  [[1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1],
    [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0],
    [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0],
    [1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
    [1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0],
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1],
    [0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1]]

@[expose] def zW : List (List ℕ) :=
  [[0], [1, 1, 1, 1, 0, 1], [1, 1, 0, 1, 1, 1], [2, 1, 1, 2, 1, 1, 1], [1, 2, 0, 1, 1, 2, 1, 1],
    [1, 0, 1, 1, 2, 1, 2, 1]]

@[expose] def zGen : Array (Array ℕ) := (zW.map fun w => img (wv w)).toArray

end CertificateChecks.Parrott946

end
