module

public import Certificates.Kernel.Q8Wit.L34Checks
public import CFSG.Certificates.Kernel.Q8WitSound

public section

namespace CertificateChecks.KernelQ8W.L34

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.Misc.ArrEnum
open CFSG.KC.Q8Wit CFSG.KC.E81K Certificates.TwinPerpSmSp1

@[expose] noncomputable def pinQ : Pin 42 6 l34Wit.syl.qKeys :=
  ⟨Q.ng, Q.N, Q.G, Q.T, Q.E, Q.S, SK, Q.ok, keys⟩

theorem q8Wit_true : q8WitCheck l34Wit = true := by
  have bP := binds_of_check bindPG
  have bX := binds_of_check bindXG
  exact q8WitCheck_of_pins l34Wit rfl hw PG bP.1 bP.2 (allN_spec permPG) (by decide)
    lettersQ pinQ wordsQ rfl (by decide) XG bX.1 bX.2 (allN_spec permXG) lettersC C wordsC
    SQ I CI tabs invs free

end CertificateChecks.KernelQ8W.L34

end
