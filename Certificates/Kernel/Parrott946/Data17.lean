module

public import Certificates.Kernel.A45Cls.Data
public import Certificates.Data.ParrottPSp43L1
public import Certificates.Data.Kernel.PermCent.CV
public import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_nat_items_gz CertificateChecks.Parrott946.D17 "Certificates/Kernel/Parrott946/data/d17.items.gz" 5504 1276600529505692875 WT IT I[] CM[] CMT M[8]

namespace CertificateChecks.Parrott946

open CertificateChecks.KernelA45 CFSG.RankThree.GF2n.Parrott

@[expose] def wW : List (List ℕ) :=
  [[0], [1, 1, 2, 0, 1, 0, 1, 1, 1, 1, 2, 0, 1, 1, 1], [2, 0], [1, 0, 1, 2, 1, 1, 2, 1, 0, 1, 0, 1, 1],
    [1, 1, 0, 1, 0, 1, 0, 1, 2, 1, 1, 1, 2, 0], [1, 1, 2, 0, 1, 2, 1, 1, 2, 1, 1, 2, 1],
    [2, 1, 2, 0, 1, 1, 1, 0, 1, 2, 1, 1, 2, 1, 1], [1, 1, 0, 1, 1, 0, 1, 2, 1, 1, 2, 1, 1, 1, 0],
    [1, 2, 0, 1, 1, 2, 1, 1], [2, 0, 1, 0, 1, 2, 1, 0, 1, 1, 1, 0], [1, 1, 2, 1, 1, 2, 0, 1, 0, 1, 1],
    [1, 0, 1, 1, 1, 0, 1, 0], [], [1, 1, 1, 2, 1, 1], [1, 0, 1, 2, 1, 2, 1], [1, 2, 1, 2, 1, 2, 1],
    [1, 2, 1, 2, 1, 2, 1, 2], [1, 0, 1, 1, 1, 0, 1, 0, 1], [1, 2, 1, 0, 1, 1, 1, 0, 1],
    [1, 1, 1, 0, 1, 1, 0, 1, 1, 1], [1, 2, 1, 0, 1, 1, 0, 1, 0, 1], [], [1, 1, 1, 2, 1, 1],
    [2, 1, 0, 1, 1, 1, 2, 0, 1, 2, 1, 1, 1, 2, 0], [2, 1, 2, 1, 2, 1, 2, 1, 2],
    [1, 2, 1, 2, 1, 2, 1, 2], [2, 1, 0, 1, 1, 1, 0, 1, 0, 1, 2], [1, 2, 1, 0, 1, 1, 1, 0, 1],
    [1, 1, 0, 1, 1, 1, 0, 1, 1], [2, 1, 0, 1, 0, 1, 1, 2, 0, 1, 2, 1, 1, 1, 0], [1, 2, 1, 1, 1],
    [1, 1, 1, 0, 1, 2, 0, 1], [1, 0, 1, 1, 2, 1, 0, 1, 1], [2, 1, 2, 1, 1, 1], [],
    [1, 2, 1, 2, 0, 1, 2, 1], [], [1, 2, 0, 1, 2, 1, 2, 0, 1, 1], [1, 2, 0, 1, 1, 2, 1, 1],
    [1, 0, 1, 1, 2, 1, 2, 1, 2, 1], [1, 0, 1, 1, 0, 1, 0, 1, 1], [1, 0, 1, 1, 2, 1, 0, 1, 1],
    [1, 2, 1, 1, 1], [1, 1, 0, 1, 1, 2, 1, 1], [1, 1, 0, 1, 2, 1, 1, 2, 1],
    [1, 2, 0, 1, 1, 2, 1, 1, 2], [1, 1, 0, 1, 1, 2, 1, 1], [], [1, 2, 0, 1, 1, 2, 1, 1, 2]]

@[expose] def p3W : List (List ℕ) :=
  [[0, 1, 1, 0, 1, 1, 1], [0, 1, 1, 1, 1, 0, 1], [0, 1, 0, 1, 1, 2, 1, 2, 1]]

@[expose] def t0Gen17 : Array (Array ℕ) :=
  #[img u, img v, img alpha1, img beta1, img alpha2, img beta2]

@[expose] def rUV : Array ℕ := img (u * v)

@[expose] def p3Gen : Array (Array ℕ) := (p3W.map fun w => img (wv w)).toArray

@[expose] noncomputable def els17 : List (Equiv.Perm (Fin 45)) :=
  [t, u, v, sigma1, sigma2, alpha1, beta1, alpha2, beta2, beta, b5]

@[expose] noncomputable def pk17 (j : ℕ) : ℕ :=
  (CFSG.Certificates.Kernel.PkCV.cOf (els17.getD j 1)).1

@[expose] def t5R : List ℕ := [1 + 64 * 30, 6 + 64 * 31, 8 + 64 * 32, 15 + 64 * 33, 41 + 64 * 34]

@[expose] def f5R : List ℕ :=
  [0 + 64 * 35, 7 + 64 * 36, 9 + 64 * 37, 14 + 64 * 38, 18 + 64 * 39, 19 + 64 * 40, 20 + 64 * 41,
    21 + 64 * 42, 30 + 64 * 43, 31 + 64 * 44]

@[expose] def meetR : List ℕ := [0 + 64 * 45, 20 + 64 * 46, 7 + 64 * 47, 0 + 64 * 48]

@[expose] def eG : List (List ℕ) := [[6, 21, 31, 41], [25, 21, 38, 41], [11, 6, 41, 21], [12, 14, 41, 21]]

end CertificateChecks.Parrott946

end
