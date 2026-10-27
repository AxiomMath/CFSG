module

public import Certificates.Kernel.MatCert.Glue
public import Certificates.Kernel.MatCert.HeringF2

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.OpsHom CFSG.SectionRank.Native
open CFSG.RankThree.Asc83Table.Native CFSG.Blueprint

theorem j3A : (ops2 80).decode NativeSporadic.J3Seed1 = CFSG.KC.Co1F2.unpackR 80 KernelJ3L.JA.M := by
  rw [KernelJ3L.JA.eq]
  exact decode2 KernelJ3L.JA.bind

theorem j3B : (ops2 80).decode NativeSporadic.J3Seed2 = CFSG.KC.Co1F2.unpackR 80 KernelJ3L.JB.M := by
  rw [KernelJ3L.JB.eq]
  exact decode2 KernelJ3L.JB.bind

theorem ks12J3Mcert : mcertCheck (ops2fr 80) NativeSporadic.J3Seed1 NativeSporadic.J3Seed2
    CFSG.RankThree.PartTwo.KFacts.KS12J3.cert = true := by
  rw [CFSG.KC.OpsF2K.mcertCheck_fr_eq]
  exact mcertCheck_of_N (hom2 80 (by norm_num)) j3A j3B trivial trivial ks12J3_K

theorem fourRuMcert : mcertCheck (ops2fr 28) NativeSporadic.RuSeed1 NativeSporadic.RuSeed2
    CFSG.RankThree.PartTwo.Sec21.Hering214.FourRu.cert = true := by
  rw [CFSG.KC.OpsF2K.mcertCheck_fr_eq]
  exact mcertCheck_of_N (hom2 28 (by norm_num)) ruA ruB trivial trivial fourRu_K

end CertificateChecks.KernelMC

end
