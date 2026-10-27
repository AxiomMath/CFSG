
module

public import Certificates.Kernel.SporSch.Co2M.ThEB

public section

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CFSG.Certificates.Native

theorem thirdE_check :
    eCheck co2PosTable witRec (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr uArr = true := by
  unfold eCheck
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]
  exact ⟨te_facts.1, te_gA_size, te_facts.2.1, te_gens, te_eShape, te_eRecord, te_eOrbits,
    te_qmats, te_enumOK, te_conjOK, te_qShape, te_qRecord, te_qOrbits⟩

end CertificateChecks.KernelSporSch.Co2M

end
