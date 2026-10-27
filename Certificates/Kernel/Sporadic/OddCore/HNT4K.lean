module

public import Certificates.Kernel.Sporadic.OddCore.HNT4D
public import Certificates.Kernel.Sporadic.OddCore.HN2088D
public import Certificates.Kernel.Sporadic.OddCore.HN2089D
public import Certificates.Kernel.LocalQT.Tc.Gen
public import Certificates.Data.Kernel.Spor.HNT4
public import Certificates.Data.Kernel.Spor.EnumBase
public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.LocalQT.Nats
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HNT4S

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.HNA CFSG.KS.HNT4 CFSG.KS.EnumBase
open CFSG.KC.LQT.NP CertificateChecks.KernelSpor

theorem pPool : natsOK HNT4T.Pool.chars (listUp HNT4T.QN 3200) = true := by quickRfl
theorem pWit : natsOK HNT4T.Wit.chars (listUp HNT4T.WN 18838) = true := by quickRfl

theorem posQ : poolPosK HNT4T.QN HNT4T.QP 3200 64 = true := by quickRfl
theorem posW : t4PosK HNT4T.WN HNT4T.WP 18838 16384 = true := by quickRfl

theorem letQ : allN 64 (fun f => poolLetK HNT4T.QN (HNT4T.QP f)) = true := by quickRfl

@[expose] noncomputable def qi (g : Nat) : Nat := pinvS 800 10 (mask 10) (HQS g)

@[expose] noncomputable def cmF (f : Nat) : Bool :=
  bAnd(wordEqK 800 10 (mask 10) (pidn 800 10) HQS qi 11 (poolComm HNT4T.QN (HNT4T.QP f))
      (HNT4C.P f),
    bAnd(wordEqK 800 10 (mask 10) (pidn 800 10) HQS qi 11
      (invWK (poolComm HNT4T.QN (HNT4T.QP f))) (HNT4C.Q f),
    bAnd(permOK 800 10 (mask 10) (800 * 10) (HNT4C.P f) (pinvS 800 10 (mask 10) (HNT4C.P f)),
      permOK 800 10 (mask 10) (800 * 10) (HNT4C.Q f) (pinvS 800 10 (mask 10) (HNT4C.Q f)))))

@[expose] noncomputable def cm (s : Nat) : Bool := sliceK 64 4 cmF s

@[expose] noncomputable def bp : List Nat := [0, 4, 3, 1, 2]

@[expose] noncomputable def wt (s : Nat) : Bool :=
  strictB (pidn 800 10) fun I =>
    sliceK 16384 64 (t4WK bp HNT4T.WN HNT4T.WP HPE.T HNT4C.P HNT4C.Q I 64) s

end CertificateChecks.KernelSpor.HNT4S

set_option Elab.async false

#kqb_range CertificateChecks.KernelSpor.HNT4S.cmK CertificateChecks.KernelSpor.HNT4S.cm 0 16
#kqb_all CertificateChecks.KernelSpor.HNT4S.cmK CertificateChecks.KernelSpor.HNT4S.cm 16
#kqb_range CertificateChecks.KernelSpor.HNT4S.wtK CertificateChecks.KernelSpor.HNT4S.wt 0 256
#kqb_all CertificateChecks.KernelSpor.HNT4S.wtK CertificateChecks.KernelSpor.HNT4S.wt 256

end
