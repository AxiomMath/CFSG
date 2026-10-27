
module

public import Certificates.Kernel.Ly3085.DischargeBase

public import Certificates.Kernel.Ly3085.Squeeze

public noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Ly.Omega CFSG.KS.LyOm CFSG.KC.LyOm CFSG.KC.LL
open CertificateChecks.KernelSporSch CFSG.Sporadic.He.Native
open Matrix MulAction

theorem lyt_mem_lyH
    [LySeed] :
    lyt ∈ lyH := by
  rw [← F1.1]
  exact lyt_fix

theorem card_centralizer_t
    [LySeed] :
    Nat.card (Subgroup.centralizer ({⟨lyt, lyt_mem_lyH⟩} : Set lyH)) ≤ 14400 :=
  card_centralizer_t_le F1.2.1.le lyt_mem_lyH

theorem card_centralizer_yB
    [LySeed] :
    Nat.card (Subgroup.centralizer ({⟨lyYB, wordJ_mem _⟩} : Set lyH)) ≤ 720 :=
  card_centralizer_yB_le F1.2.1.le lyt_mem_lyH

end CertificateChecks.KernelLy.Omega

end
