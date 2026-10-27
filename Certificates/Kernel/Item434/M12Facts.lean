module

public import Certificates.Data.Item434SporGenMathieu
public import Certificates.Kernel.M12Cent.Check
public import CFSG.Certificates.Kernel.M12Cent

public section

namespace CertificateChecks.KernelItem434

open CFSG.RankThree.PartTwo.Sec4.Item434SporGen CFSG.GH74.M12.Hyp

theorem m12_genA : m12GenCheck sigAW sigAP genAa genAb = true := by decide +kernel

theorem m12_genA2 : m12GenCheck sigA2W sigA2P genA2a genA2b = true := by decide +kernel

theorem m12_fix : m12FixCheck = true := by decide +kernel

theorem m12_cent : ∀ v : G12, tbl v.1 ∈ CFSG.RankThree.PartTwo.Toolkit.M12.ET ++
    CFSG.RankThree.PartTwo.Toolkit.M12.FT → v ≠ 1 →
      Nat.card (Subgroup.centralizer ({v} : Set G12)) = 54 := by
  intro v hv hv1
  have h := KernelM12Cent.cent_ok
  rw [KernelM12Cent.t_eq, ← CFSG.RankThree.PartTwo.Toolkit.M12.tbl_z] at h
  rw [← KernelM12Cent.S_eq] at hv
  exact CFSG.KC.M12Cent.card_centralizer_of_centCheck h hv hv1

end CertificateChecks.KernelItem434

end
