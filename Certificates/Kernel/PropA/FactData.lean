module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
import Certificates.Kernel.Sporadic.OddCore.MulHCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.PropA.FactGen

public section

open CertificateChecks.KernelPropA.Gen

#kfind CertificateChecks.KernelPropA.pa450010PAB1a CertificateChecks.KernelPropA.Gen.tCDX
  CertificateChecks.KernelPropA.Gen.qAB1a
#kfind CertificateChecks.KernelPropA.pa450010PAB1b CertificateChecks.KernelPropA.Gen.tCDX
  CertificateChecks.KernelPropA.Gen.qAB1b
#kfind CertificateChecks.KernelPropA.pa450010PAB2a CertificateChecks.KernelPropA.Gen.tCDX
  CertificateChecks.KernelPropA.Gen.qAB2a
#kfind CertificateChecks.KernelPropA.pa450010PAB2b CertificateChecks.KernelPropA.Gen.tCDX
  CertificateChecks.KernelPropA.Gen.qAB2b
#kfind CertificateChecks.KernelPropA.pa450010PJP1a CertificateChecks.KernelPropA.Gen.tJ
  CertificateChecks.KernelPropA.Gen.qJP1a
#kfind CertificateChecks.KernelPropA.pa450010PJP1b CertificateChecks.KernelPropA.Gen.tJ
  CertificateChecks.KernelPropA.Gen.qJP1b
#kfind CertificateChecks.KernelPropA.pa450010PJP2a CertificateChecks.KernelPropA.Gen.tJ
  CertificateChecks.KernelPropA.Gen.qJP2a
#kfind CertificateChecks.KernelPropA.pa450010PJP2b CertificateChecks.KernelPropA.Gen.tJ
  CertificateChecks.KernelPropA.Gen.qJP2b
#kfind CertificateChecks.KernelPropA.pa450010PRP1a CertificateChecks.KernelPropA.Gen.tR
  CertificateChecks.KernelPropA.Gen.qRP1a
#kfind CertificateChecks.KernelPropA.pa450010PRP1b CertificateChecks.KernelPropA.Gen.tR
  CertificateChecks.KernelPropA.Gen.qRP1b
#kfind CertificateChecks.KernelPropA.pa450010PRP2a CertificateChecks.KernelPropA.Gen.tR
  CertificateChecks.KernelPropA.Gen.qRP2a
#kfind CertificateChecks.KernelPropA.pa450010PRP2b CertificateChecks.KernelPropA.Gen.tR
  CertificateChecks.KernelPropA.Gen.qRP2b
#kmisc_packarrs CertificateChecks.KernelPropA.pa450010G5K CertificateChecks.KernelPropA.Gen.gG5 5
#kmisc_packarrs CertificateChecks.KernelPropA.pa450010G5S CertificateChecks.KernelPropA.Gen.gS5 5
#kmisc_packarrs CertificateChecks.KernelPropA.pa450010G5SI CertificateChecks.KernelPropA.Gen.giS5 5

#kpenum CertificateChecks.KernelPropA.pa450010Y1 28 5 false CertificateChecks.KernelPropA.Gen.gY1
  CertificateChecks.KernelPropA.Gen.giY1 CertificateChecks.KernelPropA.Gen.idT 8
#kpenum CertificateChecks.KernelPropA.pa450010Y2 28 5 false CertificateChecks.KernelPropA.Gen.gY2
  CertificateChecks.KernelPropA.Gen.giY2 CertificateChecks.KernelPropA.Gen.idT 8
#kpenum CertificateChecks.KernelPropA.pa450010ZJ 28 5 true CertificateChecks.KernelPropA.Gen.gJ
  CertificateChecks.KernelPropA.Gen.giJ CertificateChecks.KernelPropA.Gen.rz 15

#kfind CertificateChecks.KernelPropA.pa450010PEJ CertificateChecks.KernelPropA.Gen.tJ
  CertificateChecks.KernelPropA.Gen.qEJ
#kfind CertificateChecks.KernelPropA.pa450010PEE CertificateChecks.KernelPropA.Gen.tJ
  CertificateChecks.KernelPropA.Gen.qEE
#kfind CertificateChecks.KernelPropA.pa450010PKJ1 CertificateChecks.KernelPropA.Gen.tJ
  CertificateChecks.KernelPropA.Gen.qKJ1
#kfind CertificateChecks.KernelPropA.pa450010PKJ2 CertificateChecks.KernelPropA.Gen.tJ
  CertificateChecks.KernelPropA.Gen.qKJ2
#kfind CertificateChecks.KernelPropA.pa450010PZJ CertificateChecks.KernelPropA.Gen.tZJ
  CertificateChecks.KernelPropA.Gen.tJ
#kfind CertificateChecks.KernelPropA.pa450010PY1 CertificateChecks.KernelPropA.Gen.tY1
  CertificateChecks.KernelPropA.Gen.tCK1
#kfind CertificateChecks.KernelPropA.pa450010PY2 CertificateChecks.KernelPropA.Gen.tY2
  CertificateChecks.KernelPropA.Gen.tCK2
#kfind CertificateChecks.KernelPropA.pa450010G3c1 CertificateChecks.KernelPropA.Gen.tCK1
  CertificateChecks.KernelPropA.Gen.qG3c1
#kfind CertificateChecks.KernelPropA.pa450010G3y1 CertificateChecks.KernelPropA.Gen.tY1
  CertificateChecks.KernelPropA.Gen.qG3y1
#kfind CertificateChecks.KernelPropA.pa450010G3c2 CertificateChecks.KernelPropA.Gen.tCK2
  CertificateChecks.KernelPropA.Gen.qG3c2
#kfind CertificateChecks.KernelPropA.pa450010G3y2 CertificateChecks.KernelPropA.Gen.tY2
  CertificateChecks.KernelPropA.Gen.qG3y2
#kfind CertificateChecks.KernelPropA.pa450010G1_10 CertificateChecks.KernelPropA.Gen.c10
  CertificateChecks.KernelPropA.Gen.qG1_10
#kfind CertificateChecks.KernelPropA.pa450010G1_11 CertificateChecks.KernelPropA.Gen.c11
  CertificateChecks.KernelPropA.Gen.qG1_11
#kfind CertificateChecks.KernelPropA.pa450010G1_12 CertificateChecks.KernelPropA.Gen.c12
  CertificateChecks.KernelPropA.Gen.qG1_12
#kfind CertificateChecks.KernelPropA.pa450010G1_13 CertificateChecks.KernelPropA.Gen.c13
  CertificateChecks.KernelPropA.Gen.qG1_13
#kfind CertificateChecks.KernelPropA.pa450010G1_14 CertificateChecks.KernelPropA.Gen.c14
  CertificateChecks.KernelPropA.Gen.qG1_14
#kfind CertificateChecks.KernelPropA.pa450010G1_15 CertificateChecks.KernelPropA.Gen.c15
  CertificateChecks.KernelPropA.Gen.qG1_15
#kfind CertificateChecks.KernelPropA.pa450010G1_20 CertificateChecks.KernelPropA.Gen.c20
  CertificateChecks.KernelPropA.Gen.qG1_20
#kfind CertificateChecks.KernelPropA.pa450010G1_21 CertificateChecks.KernelPropA.Gen.c21
  CertificateChecks.KernelPropA.Gen.qG1_21
#kfind CertificateChecks.KernelPropA.pa450010G1_22 CertificateChecks.KernelPropA.Gen.c22
  CertificateChecks.KernelPropA.Gen.qG1_22
#kfind CertificateChecks.KernelPropA.pa450010G1_23 CertificateChecks.KernelPropA.Gen.c23
  CertificateChecks.KernelPropA.Gen.qG1_23

end
