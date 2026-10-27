module

public import Certificates.Kernel.SmithL6K.GlueT
public import Certificates.Kernel.SmithL6K.ChecksN
public import CFSG.Certificates.Kernel.SmithL6KNSound
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

#kc_forall_chunks ch38609N_all (fun k => ch38609N k = true) 21
  CertificateChecks.KernelSmithL6K.ch38609N 1

theorem reach_partners : Reach 1953 1953 (fun v => v == 31 || !isPartner v)
    (fun g u v => tvImg g 0 == 0 && tvImg g u == v && (!isPartner v || isPartner u)) :=
  partReach hC hI prc_ok

theorem four_orbit : ∃ L : List (Nat × Nat × Nat), L.length = 20160 ∧ L.Nodup ∧ ∀ t ∈ L,
    Relation.ReflTransGen
      (fun s t => ∃ g < 1953, tvImg g 0 = 0 ∧ tvImg g 31 = 31 ∧ t = fourStep g s) fourBase t := by
  have h := frt_ok
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact fourOrbit (key := keyAt fpkL) (rec := recAt frpL) (root := frt) hC hI fgm_ok
    ch38609N_all h.1

end CertificateChecks.KernelSmithL6K
