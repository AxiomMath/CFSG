module

public import CFSG.Monster.Existence.StdOdd.P5Inputs

public section

namespace CertificateChecks.MonsterExist.P5

open CFSG.Monster.Existence.StdOdd.P5

theorem orbitFin_norm : orbitFin 12 vNorm = (rkFibre 24).image encV := by decide +kernel

end CertificateChecks.MonsterExist.P5

end
