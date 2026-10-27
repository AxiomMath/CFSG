module

public import CFSG.Monster.Existence.StdOdd.P5Inputs

public section

namespace CertificateChecks.MonsterExist.P5

open CFSG.Monster.Existence.StdOdd.P5

theorem orbitFin_root : orbitFin 12 vRoot = (rkFibre 30).image encV := by decide +kernel

end CertificateChecks.MonsterExist.P5

end
