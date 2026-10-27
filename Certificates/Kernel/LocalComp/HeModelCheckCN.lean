module

public import Certificates.Kernel.LocalComp.HeModelCheckDefs
public import Certificates.Kernel.LocalComp.HeModelCntData
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.HexaKSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeModelCheck

open CFSG.KC.HeModelK CertificateChecks.KernelLC.HeModel

@[expose] noncomputable def cnB (s : Nat) : Bool := Nat.beq (cntRange d32 (256 * s) 256) (CNV s)

@[expose] def sumTo (V : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => sumTo V m + V m

theorem cntRange_blocks (d : D32) (k : Nat) (V : Nat → Nat) :
    ∀ m, (∀ s < m, cntRange d (k * s) k = V s) → cntRange d 0 (k * m) = sumTo V m
  | 0, _ => rfl
  | m + 1, h => by
    rw [Nat.mul_succ, cntRange_add, Nat.zero_add,
      cntRange_blocks d k V m (fun s hs => h s (by omega)), h m (by omega)]
    rfl

end CertificateChecks.KernelLC.HeModelCheck

set_option Elab.async false

#kon_slices CertificateChecks.KernelLC.HeModelCheck.cnB 0 84
#kon_join CertificateChecks.KernelLC.HeModelCheck.cnAll CertificateChecks.KernelLC.HeModelCheck.cnB 84

namespace CertificateChecks.KernelLC.HeModelCheck

open CFSG.KC.HeModelK CertificateChecks.KernelLC.HeModel

theorem cnTotal : cntRange d32 0 d32.NC =
    3072 + 65536 * 3072 + 4294967296 * 64 + 281474976710656 * 64 +
      18446744073709551616 * 3072 + 1208925819614629174706176 * 3072 := by
  have hN : d32.NC = 256 * 84 := rfl
  rw [hN, cntRange_blocks d32 256 CNV 84 fun s hs => Nat.eq_of_beq_eq_true (cnAll s hs)]
  rfl

end CertificateChecks.KernelLC.HeModelCheck

end
