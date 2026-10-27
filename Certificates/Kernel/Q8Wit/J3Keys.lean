module

public import Certificates.Data.TwinPerpSmSp1WitJ3

public section

namespace CertificateChecks.KernelQ8W.J3

@[expose] def j3KeysArr : Array Nat := #[0, 1]

@[expose] def j3Gens : Array (Array Nat) :=
  CFSG.CGT.PushingUpLit.SolKNA.R4.Check.qGens Certificates.TwinPerpSmSp1.j3Wit.syl

theorem j3KeysArr_toList : j3KeysArr.toList = Certificates.TwinPerpSmSp1.j3Wit.syl.qKeys := rfl

end CertificateChecks.KernelQ8W.J3

end
