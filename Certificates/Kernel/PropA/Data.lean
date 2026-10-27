module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
import Certificates.Kernel.Sporadic.OddCore.MulHCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.PropA.Gen

public section

open CertificateChecks.KernelPropA.Gen

#kmisc_packarrs CertificateChecks.KernelPropA.pa450010S1 CertificateChecks.KernelPropA.Gen.gK1 5
#kmisc_packarrs CertificateChecks.KernelPropA.pa450010S1I CertificateChecks.KernelPropA.Gen.giK1 5
#kmisc_packarrs CertificateChecks.KernelPropA.pa450010S2 CertificateChecks.KernelPropA.Gen.gK2 5
#kmisc_packarrs CertificateChecks.KernelPropA.pa450010S2I CertificateChecks.KernelPropA.Gen.giK2 5

#kpenum CertificateChecks.KernelPropA.pa450010XD 28 5 true CertificateChecks.KernelPropA.Gen.gD
  CertificateChecks.KernelPropA.Gen.giD CertificateChecks.KernelPropA.Gen.rx 396
#kpenum CertificateChecks.KernelPropA.pa450010AD 28 5 true CertificateChecks.KernelPropA.Gen.gD
  CertificateChecks.KernelPropA.Gen.giD CertificateChecks.KernelPropA.Gen.rA 495
#kpenum CertificateChecks.KernelPropA.pa450010UD 28 5 true CertificateChecks.KernelPropA.Gen.gD
  CertificateChecks.KernelPropA.Gen.giD CertificateChecks.KernelPropA.Gen.ru 2640

#kpenum CertificateChecks.KernelPropA.pa450010C10 28 5 true CertificateChecks.KernelPropA.Gen.gK1
  CertificateChecks.KernelPropA.Gen.giK1 CertificateChecks.KernelPropA.Gen.r10 792
#kpenum CertificateChecks.KernelPropA.pa450010C11 28 5 true CertificateChecks.KernelPropA.Gen.gK1
  CertificateChecks.KernelPropA.Gen.giK1 CertificateChecks.KernelPropA.Gen.r11 792
#kpenum CertificateChecks.KernelPropA.pa450010C12 28 5 true CertificateChecks.KernelPropA.Gen.gK1
  CertificateChecks.KernelPropA.Gen.giK1 CertificateChecks.KernelPropA.Gen.r12 792
#kpenum CertificateChecks.KernelPropA.pa450010C13 28 5 true CertificateChecks.KernelPropA.Gen.gK1
  CertificateChecks.KernelPropA.Gen.giK1 CertificateChecks.KernelPropA.Gen.r13 792
#kpenum CertificateChecks.KernelPropA.pa450010C14 28 5 true CertificateChecks.KernelPropA.Gen.gK1
  CertificateChecks.KernelPropA.Gen.giK1 CertificateChecks.KernelPropA.Gen.r14 792
#kpenum CertificateChecks.KernelPropA.pa450010C15 28 5 true CertificateChecks.KernelPropA.Gen.gK1
  CertificateChecks.KernelPropA.Gen.giK1 CertificateChecks.KernelPropA.Gen.r15 792
#kpenum CertificateChecks.KernelPropA.pa450010C20 28 5 true CertificateChecks.KernelPropA.Gen.gK2
  CertificateChecks.KernelPropA.Gen.giK2 CertificateChecks.KernelPropA.Gen.r20 792
#kpenum CertificateChecks.KernelPropA.pa450010C21 28 5 true CertificateChecks.KernelPropA.Gen.gK2
  CertificateChecks.KernelPropA.Gen.giK2 CertificateChecks.KernelPropA.Gen.r21 792
#kpenum CertificateChecks.KernelPropA.pa450010C22 28 5 true CertificateChecks.KernelPropA.Gen.gK2
  CertificateChecks.KernelPropA.Gen.giK2 CertificateChecks.KernelPropA.Gen.r22 792
#kpenum CertificateChecks.KernelPropA.pa450010C23 28 5 true CertificateChecks.KernelPropA.Gen.gK2
  CertificateChecks.KernelPropA.Gen.giK2 CertificateChecks.KernelPropA.Gen.r23 792
#kpenum CertificateChecks.KernelPropA.pa450010C24 28 5 true CertificateChecks.KernelPropA.Gen.gK2
  CertificateChecks.KernelPropA.Gen.giK2 CertificateChecks.KernelPropA.Gen.r24 792
#kpenum CertificateChecks.KernelPropA.pa450010C25 28 5 true CertificateChecks.KernelPropA.Gen.gK2
  CertificateChecks.KernelPropA.Gen.giK2 CertificateChecks.KernelPropA.Gen.r25 792

#kpenum CertificateChecks.KernelPropA.pa450010J 28 5 false CertificateChecks.KernelPropA.Gen.gJ
  CertificateChecks.KernelPropA.Gen.giJ CertificateChecks.KernelPropA.Gen.idT 60
#kpenum CertificateChecks.KernelPropA.pa450010CDX 28 5 false
  CertificateChecks.KernelPropA.Gen.gCDX CertificateChecks.KernelPropA.Gen.giCDX
  CertificateChecks.KernelPropA.Gen.idT 240
#kpenum CertificateChecks.KernelPropA.pa450010CDU 28 5 false
  CertificateChecks.KernelPropA.Gen.gCDU CertificateChecks.KernelPropA.Gen.giCDU
  CertificateChecks.KernelPropA.Gen.idT 36
#kpenum CertificateChecks.KernelPropA.pa450010CDA 28 5 false
  CertificateChecks.KernelPropA.Gen.gCDA CertificateChecks.KernelPropA.Gen.giCDA
  CertificateChecks.KernelPropA.Gen.idT 192
#kpenum CertificateChecks.KernelPropA.pa450010CDG 28 5 false
  CertificateChecks.KernelPropA.Gen.gCDG CertificateChecks.KernelPropA.Gen.giCDG
  CertificateChecks.KernelPropA.Gen.idT 120
#kpenum CertificateChecks.KernelPropA.pa450010CKX1 28 5 false
  CertificateChecks.KernelPropA.Gen.gCKX1 CertificateChecks.KernelPropA.Gen.giCKX1
  CertificateChecks.KernelPropA.Gen.idT 960
#kpenum CertificateChecks.KernelPropA.pa450010CKX2 28 5 false
  CertificateChecks.KernelPropA.Gen.gCKX2 CertificateChecks.KernelPropA.Gen.giCKX2
  CertificateChecks.KernelPropA.Gen.idT 960
#kpenum CertificateChecks.KernelPropA.pa450010R 28 5 false CertificateChecks.KernelPropA.Gen.gR
  CertificateChecks.KernelPropA.Gen.giR CertificateChecks.KernelPropA.Gen.idT 60
#kpenum CertificateChecks.KernelPropA.pa450010SD 28 5 false CertificateChecks.KernelPropA.Gen.gSD
  CertificateChecks.KernelPropA.Gen.giSD CertificateChecks.KernelPropA.Gen.idT 64
#kpenum CertificateChecks.KernelPropA.pa450010SY1 28 5 false
  CertificateChecks.KernelPropA.Gen.gS1 CertificateChecks.KernelPropA.Gen.giS1
  CertificateChecks.KernelPropA.Gen.idT 256
#kpenum CertificateChecks.KernelPropA.pa450010SY2 28 5 false
  CertificateChecks.KernelPropA.Gen.gS2 CertificateChecks.KernelPropA.Gen.giS2
  CertificateChecks.KernelPropA.Gen.idT 256

#kfind CertificateChecks.KernelPropA.pa450010F10 CertificateChecks.KernelPropA.Gen.c10
  CertificateChecks.KernelPropA.Gen.tS1
#kfind CertificateChecks.KernelPropA.pa450010F11 CertificateChecks.KernelPropA.Gen.c11
  CertificateChecks.KernelPropA.Gen.tS1
#kfind CertificateChecks.KernelPropA.pa450010F12 CertificateChecks.KernelPropA.Gen.c12
  CertificateChecks.KernelPropA.Gen.tS1
#kfind CertificateChecks.KernelPropA.pa450010F13 CertificateChecks.KernelPropA.Gen.c13
  CertificateChecks.KernelPropA.Gen.tS1
#kfind CertificateChecks.KernelPropA.pa450010F14 CertificateChecks.KernelPropA.Gen.c14
  CertificateChecks.KernelPropA.Gen.tS1
#kfind CertificateChecks.KernelPropA.pa450010F15 CertificateChecks.KernelPropA.Gen.c15
  CertificateChecks.KernelPropA.Gen.tS1
#kfind CertificateChecks.KernelPropA.pa450010F20 CertificateChecks.KernelPropA.Gen.c20
  CertificateChecks.KernelPropA.Gen.tS2
#kfind CertificateChecks.KernelPropA.pa450010F21 CertificateChecks.KernelPropA.Gen.c21
  CertificateChecks.KernelPropA.Gen.tS2
#kfind CertificateChecks.KernelPropA.pa450010F22 CertificateChecks.KernelPropA.Gen.c22
  CertificateChecks.KernelPropA.Gen.tS2
#kfind CertificateChecks.KernelPropA.pa450010F23 CertificateChecks.KernelPropA.Gen.c23
  CertificateChecks.KernelPropA.Gen.tS2
#kfind CertificateChecks.KernelPropA.pa450010F24 CertificateChecks.KernelPropA.Gen.c24
  CertificateChecks.KernelPropA.Gen.tS2
#kfind CertificateChecks.KernelPropA.pa450010F25 CertificateChecks.KernelPropA.Gen.c25
  CertificateChecks.KernelPropA.Gen.tS2
#kfind CertificateChecks.KernelPropA.pa450010FD0 CertificateChecks.KernelPropA.Gen.cDX
  CertificateChecks.KernelPropA.Gen.tSD
#kfind CertificateChecks.KernelPropA.pa450010FD1 CertificateChecks.KernelPropA.Gen.cDA
  CertificateChecks.KernelPropA.Gen.tSD

end
