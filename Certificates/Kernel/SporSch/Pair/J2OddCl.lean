module

public import Certificates.Kernel.SporSch.Pair.J2Chain
public import Certificates.Kernel.SporSch.Pair.GenNF
public import CFSG.Certificates.Kernel.SporSch.PairClSound
public meta import Certificates.Data.SmithB45J2ClsData
public meta import CFSG.Sporadic.Schreier.PairJ2CheckInputs

public section

set_option maxRecDepth 400000

meta def CertificateChecks.KernelSporSch.j2OddCl4 :
    List (List (Array Nat) × Array (Array Nat) × Array Nat × Array Nat) :=
  [CFSG.Quasithin.J2Cls.w3A, CFSG.Sporadic.Schreier.PairJ2.wB, CFSG.Quasithin.J2Cls.w5A,
    CFSG.Quasithin.J2Cls.w5C].map fun w => (w, CFSG.Quasithin.J2Cls.closureOf w)

#kss_nfclos CertificateChecks.KernelSporSch.PJ2C260410 CertificateChecks.KernelSporSch.PJ2 315 9 3
  CFSG.Sporadic.Schreier.PairJ2.levels CFSG.Sporadic.Schreier.PairJ2.bs
  CFSG.Sporadic.Schreier.PairJ2.gens CFSG.Sporadic.Schreier.PairJ2.gensInv
  CertificateChecks.KernelSporSch.j2OddCl4 100000 10 16 32

end
