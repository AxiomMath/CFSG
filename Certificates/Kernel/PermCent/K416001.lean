module

public import Certificates.Data.Kernel.PermCent.Sp6SqQ

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelPermCent

open CFSG.EvenSmallLie.Sp6 CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.Sp6B

theorem k416001_1H : sqCheckH (cOf sp6Rep1) (levelsC sp6CentQ1) = true := by decide +kernel

theorem k416001_2H : sqCheckH (cOf sp6Rep2) (levelsC sp6CentQ2) = true := by decide +kernel

theorem k416001_3H : sqCheckH (cOf sp6Rep3) (levelsC sp6CentQ3) = true := by decide +kernel

theorem k416001_4H : sqCheckH (cOf sp6Rep4) (levelsC sp6CentQ4) = true := by decide +kernel

theorem k416001_1 : sq1C = true :=
  (sqCheckQ_eq _ _).symm.trans ((sqCheckH_eq _ (levelsC sp6CentQ1)).symm.trans k416001_1H)

theorem k416001_2 : sq2C = true :=
  (sqCheckQ_eq _ _).symm.trans ((sqCheckH_eq _ (levelsC sp6CentQ2)).symm.trans k416001_2H)

theorem k416001_3 : sq3C = true :=
  (sqCheckQ_eq _ _).symm.trans ((sqCheckH_eq _ (levelsC sp6CentQ3)).symm.trans k416001_3H)

theorem k416001_4 : sq4C = true :=
  (sqCheckQ_eq _ _).symm.trans ((sqCheckH_eq _ (levelsC sp6CentQ4)).symm.trans k416001_4H)

end CertificateChecks.KernelPermCent
