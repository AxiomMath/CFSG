module

public import CFSG.Monster.Existence.StdOdd.P5Inputs

public section

namespace CertificateChecks.MonsterExist.P5

open CFSG.Monster.Existence.StdOdd.P5

theorem orbitFin_sing : orbitFin 12 vSing = (rkFibre 18).image encV := by decide +kernel

end CertificateChecks.MonsterExist.P5

end
