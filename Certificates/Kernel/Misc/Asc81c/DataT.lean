module

public import CFSG.Quasithin.Background.Asc81cPfCheckT
public import Certificates.Kernel.Misc.Asc81c.Data
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_blocked_root CertificateChecks.KernelAsc81c.WT
  "Certificates/Kernel/Misc/Asc81c/data/witT.bin" 8 5 4294967295 85920 18279268221012562615

namespace CertificateChecks.KernelAsc81c

open CFSG.Quasithin.Asc81c.Pf.Check CFSG.Monster.B.Co2.Native CFSG.KGroups.Native

@[expose] def decC (n v : Nat) : List Nat := (List.range n).map fun k => v / (2 ^ n) ^ k % 2 ^ n

@[expose] noncomputable def P4 (i : Nat) : Array Nat := linA 4 (decC 4 (WT i))

@[expose] noncomputable def P3 (i : Nat) : Array Nat := linA 3 (decC 3 (WT (144 + i)))

@[expose] def ptW (N : Nat) (x a b : Array Nat) (w₁ w₂ v : List Bool) : Bool :=
  ord21A N (evalWA N x a w₁) &&
    (ord21A N (evalWA N x b w₂) &&
      !eqA N (compA N (conjA N (evalWA N x a w₁) x) (conjA N (evalWA N x b w₂) x))
        (compA N (conjA N (evalWA N x b w₂) x) (conjA N (evalWA N x a w₁) x)) &&
      !ord21A N (evalWA N (conjA N (evalWA N x a w₁) x) (conjA N (evalWA N x b w₂) x) v))

@[expose] def pairT (N : Nat) (x a b : Array Nat) (r : Nat) : Bool :=
  !meet3 N x a b ||
    (r % 4 == 1 && ptW N x a b (decW 2 (r / 4 % 8)) (decW 2 (r / 32 % 8)) (decW 2 (r / 256 % 8))) ||
    (r % 4 == 2 && eqA N (evalWA N x a (decW 6 (r / 4))) b)

end CertificateChecks.KernelAsc81c

end
