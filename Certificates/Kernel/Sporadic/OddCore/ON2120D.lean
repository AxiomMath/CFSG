module

public import Certificates.Kernel.Sporadic.OddCore.ON2120G
public import Certificates.Kernel.Sporadic.OddCore.ON2121
public import Certificates.Kernel.Sporadic.OddCore.ON2123
public import Certificates.Kernel.Sporadic.OddCore.ONLitCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.Sporadic.ONOddCore.LiftCheckInputs
import CFSG.Certificates.Kernel.Misc.KernelRfl
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.ONOddCore.LiftCheckInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON2120

open CFSG.ONSchreier.Native hiding posArr
open CFSG.ONSchreier CFSG.Sporadic.ON.Native CFSG.Sporadic.ONOddCore

meta def bwM : Array (Array Nat) :=
  let hA := wordArrs Data.MWords
  let lws := (List.range 12).toArray.map fun k =>
    ((liftData.lw.getD k []).map (posArr nPts hA)).toArray
  ((List.range 36).toArray.map fun o => bTab (lws[o / 3]!)[o % 3]!) ++
    (List.range 3).toArray.map fun i => bTab hA[i]!

meta def cilM : Array (Array Nat) := #[pinvCand 120 Data.quotientConjugator]

end CertificateChecks.KernelSpor.ON2120

#kon_certlit CertificateChecks.KernelSpor.ON2120.CLit CFSG.Sporadic.ONOddCore.localCert
#kon_liftlit CertificateChecks.KernelSpor.ON2120.LLit CFSG.Sporadic.ONOddCore.liftData
#kmisc_packarrs CertificateChecks.KernelSpor.ON2120.BW CertificateChecks.KernelSpor.ON2120.bwM 7
#kmisc_packarrs CertificateChecks.KernelSpor.ON2120.CIP CertificateChecks.KernelSpor.ON2120.cilM 7

namespace CertificateChecks.KernelSpor.ON2120

open CFSG.ONSchreier.Native hiding posArr
open CFSG.ONSchreier CFSG.Sporadic.ON.Native CFSG.Sporadic.ONOddCore
open CFSG.KS.DecSL CFSG.KC.Enum CFSG.KS

theorem lift_dec : decodeLifts (natsSL LiftsT.chars) = LLit := by
  kernelRfl

theorem cert_dec : decodeCert (natsSL LocAutT.chars) = CLit := by
  kernelRfl

theorem liftData_eq : liftData = LLit := by
  rw [liftData, LiftsT.eq, natsOf_ofList ON2121.digits, lift_dec]

theorem localCert_eq : localCert = CLit := by
  rw [localCert, LocAutT.eq, natsOf_ofList ON2123.digits, cert_dec]

@[expose] noncomputable def bw (o i : Nat) : Nat := pg 7 (mask 7) (BW o) i

@[expose] noncomputable def cil (x : Nat) : Nat := pg 7 (mask 7) (CIP 0) x

end CertificateChecks.KernelSpor.ON2120

end
