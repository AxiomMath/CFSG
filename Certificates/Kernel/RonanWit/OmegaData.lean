module

import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz
public import Certificates.Data.Kernel.Wit3K
meta import Certificates.Kernel.Misc.PackJson
import Certificates.Kernel.Misc.PackJson

public section

#kc_repo #kmisc_json_pack CertificateChecks.KernelRonanWit.Omega
  "Certificates/Kernel/RonanWit/data/omega.json.gz" 1364261 7451594581250029416
  (gens GS 9) (pG PG 9) (ppts PT 9) (pedges EP 12) (ppar PAR 0) (plab LAB 0) (pK K 0)
  (pso SO 0) (psi SI 0) (qG QG 9) (qpts QT 9) (qedges QEP 12) (qpar QPAR 0) (qlab QLAB 0)
  (qK QK 0) (qso QSO 0) (qsi QSI 0) (ys YS 9) (wit W 0)

#kc_repo #kc_json_gz CertificateChecks.KernelRonanWit.Omega
  "Certificates/Kernel/RonanWit/data/omega.json.gz" 1364261 7451594581250029416
  (pws : List (List Nat)) (pps : List Nat) (qws : List (List Nat)) (qps : List Nat)
  (yws : List (List Nat))

namespace CertificateChecks.KernelRonanWit.Omega

@[expose] noncomputable def P : CFSG.KC.Wit3.Cert :=
  ⟨5, PG, pws, 729, PT, EP, PAR, LAB, pps, K, SO, SI⟩

@[expose] noncomputable def Q : CFSG.KC.Wit3.Cert :=
  ⟨4, QG, qws, 243, QT, QEP, QPAR, QLAB, qps, QK, QSO, QSI⟩

end CertificateChecks.KernelRonanWit.Omega

end
