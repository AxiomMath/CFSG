module

public import Certificates.Kernel.Sporadic.ON.Data
public meta import Certificates.Data.CFSGNative.ON.Certificate

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON2

meta def orbM : CFSG.Sporadic.ON.Native.VOrbit := CFSG.Sporadic.ON.Native.orbitData ()

meta def strongM : Array (Array Nat) := #[orbM.alpha.map (·.toNat), orbM.beta.map (·.toNat)]

meta def noWordsM : Array (List Int) := #[[], []]

end CertificateChecks.KernelSpor.ON2

#kon_data CertificateChecks.KernelSpor.ONW CertificateChecks.KernelSpor.ON2.orbM
  CertificateChecks.KernelSpor.ON2.strongM CertificateChecks.KernelSpor.ON.colsAM
  CertificateChecks.KernelSpor.ON.colsBM CertificateChecks.KernelSpor.ON2.noWordsM 240

namespace CertificateChecks.KernelSpor.ON2

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON

@[expose] noncomputable def mvS (s : Nat) : Bool :=
  mvRange ONW.K ONW.LA ONW.LB ONW.A ONW.B (nat_lit 245520) (Nat.mul s (nat_lit 240)) (nat_lit 240)

@[expose] noncomputable def ordS (s : Nat) : Bool :=
  Nat.beq (ordRun ONW.A ONW.B (Nat.mul s (nat_lit 240)) (nat_lit 240) (ONW.NX s)) (ONW.NX (Nat.succ s))

@[expose] noncomputable def sortS (s : Nat) : Bool :=
  sortRange ONW.K ONW.SO ONW.SOI (nat_lit 245520) (Nat.mul s (nat_lit 240)) (nat_lit 240)

end CertificateChecks.KernelSpor.ON2

end
