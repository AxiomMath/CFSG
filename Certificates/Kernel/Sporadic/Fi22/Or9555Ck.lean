module

public import Certificates.Kernel.Sporadic.Fi22.Or9555D
public import Certificates.Kernel.Sporadic.Fi22.FivePin
public import Certificates.Data.Kernel.SetWalk

public section

namespace CertificateChecks.KernelSpor.Or9555

open CFSG.KC.Enum CFSG.KC.SetWalk CertificateChecks.KernelSpor
open CFSG.AGLEmbedding.KFactProofs.Fi22Five

@[expose] noncomputable def or9555ck (c : Nat) : Bool :=
  chunkOK (nat_lit 360) (nat_lit 12) (nat_lit 4095) (nat_lit 64) (nat_lit 18446744073709551615)
    (Or9555R (nat_lit 0)) (nat_lit 9) (nat_lit 45) (Fi22Pin.pin (nat_lit 6)) (Fi22Pin.pin (nat_lit 7))
    (nat_lit 61776) (nat_lit 128) Or9555T Or9555C (fun c => Or9555P c) c

@[expose] noncomputable def len (j : Nat) : Nat := nIf(Nat.blt j (nat_lit 15), nat_lit 4096, nat_lit 335)

@[expose] noncomputable def or9555sk (j : Nat) : Bool :=
  sortOK Or9555T Or9555K 61776 (Nat.mul j (nat_lit 4096)) (len j)

@[expose] noncomputable def rootOK : Bool :=
  listK 12 4095 s0List (Or9555C 0) &&
    Nat.beq (Or9555C 1) (pcomp 360 12 4095 (Fi22W.G 0) (Or9555C 0)) &&
    Nat.beq (Or9555C 2) (pcomp 360 12 4095 (Fi22W.G 1) (Or9555C 0)) &&
    Nat.beq (Or9555C 3) (pcomp 360 12 4095 (Fi22W.G 1) (pcomp 360 12 4095 (Fi22W.G 0) (Or9555C 0))) &&
    Nat.beq (Or9555P 0) (0 + 1 * 1048576) && Nat.beq (Or9555P 1) (1 + 1576 * 1048576) &&
    Nat.beq (Or9555P 2) (1576 + 23976 * 1048576) && Nat.beq (Or9555P 3) (23976 + 61776 * 1048576) &&
    fixOK 360 12 4095 (Fi22Pin.pin 6) (Or9555C 0) && fixOK 360 12 4095 (Fi22Pin.pin 7) (Or9555C 0)

end CertificateChecks.KernelSpor.Or9555

end
