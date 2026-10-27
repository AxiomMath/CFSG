module

public import CFSG.Quasithin.Background.Asc81cPfCheck
public import CFSG.Certificates.Kernel.Bounds.Load
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_blocked_root CertificateChecks.KernelAsc81c.W
  "Certificates/Kernel/Misc/Asc81c/data/wit.bin" 8 5 4294967295 264192 7108362297077957558

namespace CertificateChecks.KernelAsc81c

open CFSG.Quasithin.Asc81c.Pf.Check CFSG.Monster.B.Co2.Native CFSG.KGroups.Native

@[expose] def decW : Nat → Nat → List Bool
  | 0, _ => []
  | f + 1, v => if v ≤ 1 then [] else (v % 2 == 1) :: decW f (v / 2)

@[expose] def genW2 (n : Nat) (x t t₁ : Array Nat) (w₂ w : List Bool) : Bool :=
  ord3A (2 ^ n) (evalWA (2 ^ n) x t w₂) &&
    decide (2 ≤ (fixL (2 ^ n) t₁ (evalWA (2 ^ n) x t w₂)).length) &&
    critA n t₁ (evalWA (2 ^ n) x t w₂) (evalWA (2 ^ n) t₁ (evalWA (2 ^ n) x t w₂) w)

@[expose] def genW (n : Nat) (x t : Array Nat) (w₁ w₂ w : List Bool) : Bool :=
  ord3A (2 ^ n) (evalWA (2 ^ n) x t w₁) && genW2 n x t (evalWA (2 ^ n) x t w₁) w₂ w

@[expose] def pairW (n : Nat) (x : Array Nat) (c : List Nat) (r : Nat) : Bool :=
  !ord3V n c ||
    let t := linA n c
    !(fixCount (2 ^ n) t == 2 ^ (n - 2) && meetTriv (2 ^ n) x t) ||
      eqA (2 ^ n) (compA (2 ^ n) x t) (compA (2 ^ n) t x) ||
      (r % 4 == 1 && critA n x t (evalWA (2 ^ n) x t (decW 10 (r / 4)))) ||
      (r % 4 == 2 && genW n x t (decW 4 (r / 4 % 32)) (decW 4 (r / 128 % 32))
        (decW 4 (r / 4096 % 32))) ||
      (n == 3 && f21OK n x t)

@[expose] noncomputable def chunk4 (d : Nat) : Bool :=
  allLt 16 fun a => allLt 16 fun b => allLt 16 fun c =>
    pairW 4 (x0 4) [a, b, c, d] (W (a + 16 * b + 256 * c + 4096 * d))

@[expose] noncomputable def chunk3 (c : Nat) : Bool :=
  allLt 8 fun a => allLt 8 fun b => pairW 3 (x0 3) [a, b, c] (W (65536 + a + 8 * b + 64 * c))

end CertificateChecks.KernelAsc81c

end
