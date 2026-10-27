module

public import Certificates.Data.Kernel.E64CC
public import Certificates.Data.E64CenComm
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.E64CC.D "Certificates/Kernel/E64CC/data/e64cc.items" 314288 15950382338604836128

namespace CertificateChecks.KernelE64CC

open CFSG.ClassicalInvolution.Q3.AE Certificates.E64CenComm

@[expose] def img14 (a : Wr 7) : Array ℕ :=
  Array.ofFn (n := 14) fun x =>
    (a.perm ⟨x.val % 7, Nat.mod_lt _ (by norm_num)⟩).val +
      7 * ((x.val / 7 + (a.vec (a.perm ⟨x.val % 7, Nat.mod_lt _ (by norm_num)⟩)).val) % 2)

@[expose] def compA (f g : Array ℕ) : Array ℕ := Array.ofFn (n := 14) fun i => f[g[i.val]!]!

@[expose] def eM (k : ℕ) : Wr 7 := (memElts (memList ()) (k / 2)).getD (2 + 2 * (k % 2)) 1

@[expose] def mtG : Array (Array ℕ) :=
  #[compA (img14 (eM 0)) (img14 (eM 3)), compA (img14 (eM 4)) (img14 (eM 16))]

@[expose] def ps : List ℕ := [0, 1, 2, 3, 4, 5, 6]

end CertificateChecks.KernelE64CC

end
