module

public import Certificates.Kernel.Misc.Perm.J2EnumMain
public import CFSG.Certificates.Kernel.Misc.EnumBfsMem
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2En

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.RankThree.Native
open CFSG.ComponentClassification.J2Cover CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
open CFSG.KC.EnumBfs (enumBfs_mem any_congr_of_mem)
open CertificateChecks.KernelMisc.J2Fam (V1)

theorem memCNE : ∀ x, x ∈ cNE.pts ↔ x ∈ cNEL.pts := by
  unfold cNE
  exact enumBfs_mem enumNE (by rw [sizeNE]; norm_num)

theorem inCNE (t : Array ℕ) : inCert cNE t = inCert cNEL t := by
  unfold inCert
  exact any_congr_of_mem memCNE _

theorem chkE0N_true : chkE0N = true := by
  unfold chkE0N
  simp only [inCNE]
  exact chkE0N_lit

theorem chkE0_true : chkE0 = true := by
  unfold chkE0
  rw [chkE0N_true, chkE0C_true]
  rfl

theorem neg_inNE : (!memK 54 (lget NEP) V1) = true := by quickRfl

end CertificateChecks.KernelMisc.J2En

end
