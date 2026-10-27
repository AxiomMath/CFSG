
module

public import Certificates.Kernel.J4Hub.Struct
public import Certificates.Kernel.J4Q.Mat
public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Schreier.J4SNoCompData
public import CFSG.Sporadic.Schreier.J4SOrderBase

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp MulAction
open CFSG.Sporadic.SmallF2

theorem card_Kz : Nat.card CertificateChecks.KernelJ4Hub.Kz = 501397585920 := by
  have : Finite J := CertificateChecks.KernelJ4Hub.finite_J
  have : Fintype J := Fintype.ofFinite J
  obtain ⟨-, wr, hcov, hsz⟩ := CertificateChecks.KernelJ4Hub.dc_data
  have h := (CFSG.Sporadic.J4.Struct.dcF_exact (w := fun i => wr i.val) hcov hsz
    CertificateChecks.KernelJ4Hub.card_K_le).2.2
  rw [CertificateChecks.KernelJ4Hub.card_J', CertificateChecks.KernelJ4Hub.sum_nD] at h
  omega

theorem v_eq_root : v = toRow Native.rootV.toVec := by
  rw [v, toVecD_rootBits]

theorem Hj_le_stab : Hj ≤ stabilizer J v := fun g hg => by
  rw [mem_stabilizer_iff, v_eq_root]
  exact Hj_fix_root CertificateChecks.KernelJ4Q.matFacts g hg

theorem Kz_le_Hj : CertificateChecks.KernelJ4Hub.Kz ≤ Hj := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl)
  · exact CertificateChecks.KernelJ4Hub.X_mem_Hj
  · exact CertificateChecks.KernelJ4Hub.Y_mem_Hj
  · exact CertificateChecks.KernelJ4Hub.Z_mem_Hj

theorem Kz_le_stab : CertificateChecks.KernelJ4Hub.Kz ≤ stabilizer J v := Kz_le_Hj.trans Hj_le_stab

end CertificateChecks.KernelJ4Count

end
