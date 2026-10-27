module

public import Certificates.Data.Kernel.ON8138.Perm
public import CFSG.RankThree.Native.ONTripleAutSpInputs
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KD.ON8138.P81 "Certificates/Kernel/ON8138/data/p81.items" 543 12476901042828444166

namespace CertificateChecks.KernelON8138

open CFSG.KC.ON8138 CFSG.KD.ON8138 CFSG.RankThree.Native.ONTriple Equiv

@[expose] def penc (σ : Perm (Fin 6)) : ℕ :=
  (σ 0).val + 8 * ((σ 1).val + 8 * ((σ 2).val + 8 * ((σ 3).val + 8 * ((σ 4).val + 8 * (σ 5).val))))

theorem cubes : ∀ u : Perm (Fin 6), u ^ 3 = 1 →
    anyK (nat_lit 81) (fun k => Nat.beq (P81 k) (penc u)) = true := by
  decide +kernel

theorem a6K : a6OK P81 181826 120898 5475 180867 71709 Wy0 Wy1 Wt4 = true := by quickRfl

theorem cent : ∀ t : Perm (Fin 6), t * sY 0 = sY 0 * t → t * sY 1 = sY 1 * t →
    ∃ a < 3, ∃ b < 3, t = sY 0 ^ a * sY 1 ^ b := by
  decide +kernel

end CertificateChecks.KernelON8138

end
