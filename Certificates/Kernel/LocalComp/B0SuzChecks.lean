module

public import Certificates.Kernel.LocalComp.B0SuzData
public import Certificates.Kernel.LocalComp.B0SuzMat
public import Certificates.Kernel.Sporadic.OddCore.Suz2302
public import Certificates.Data.Kernel.B0SuzK
public import Certificates.Data.Kernel.BfsPin
public import CFSG.Certificates.Kernel.LocalCompUnpack
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Q0SuzTests
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatTypeInputs
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.B0Suz

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.HexaK CFSG.KC.B0SuzK CFSG.KC.BfsPin
open CFSG.ComponentClassification.AS81.SuzB0 CFSG.Sporadic.SuzOddCore CFSG.PSL3Four.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelLC

@[expose] noncomputable def T : Nat := SuzInvT1.F 0

@[expose] noncomputable def C (k : Nat) : Nat := SuzInvT1.F (18 + k)

@[expose] noncomputable def OT : Nat := SuzInvT1.F 4

@[expose] noncomputable def OM : Nat := packA 7 outerMat.toList

theorem kInM : allN 6 (fun i => canonK 1782 11 (mask 11) (1782 * 11) (SuzB0Q.F i) &&
    OddCore.msift (SuzB0Q.F i)) = true := by quickRfl

theorem kBase : baseK T SuzB0Q.F SuzB0QP SuzB0QE = true := by quickRfl

theorem kDist : distK SuzB0QE = true := by quickRfl

theorem kConj : conjK T SuzB0Q.F C SuzB0QP act = true := by quickRfl

theorem kBindM : (Nat.beq matTabs.size SuzB0M.ng &&
    allN SuzB0M.ng fun k => bindArrK matTabs[k]! 64 7 (SuzB0M.G k)) = true := by quickRfl

theorem kOut : (canonK 1782 11 (mask 11) (1782 * 11) OT && !(OddCore.msift OT) &&
    bindArrK outerMat 64 7 OM && canonK 64 7 (mask 7) (64 * 7) OM) = true := by quickRfl

theorem kQ0 : q0K T OT SuzB0Q.F SuzB0QP oact SuzB0M.N SuzB0M.T OM = true := by quickRfl

theorem kShat : shatK T C SuzB0QP typeYWord typeY'Word typeA0 polarBit qMinusBit
    (fun v => typeTrans.lookup v) = true := by quickRfl

@[expose] noncomputable def rule (v : Nat) : Bool := ruleK T SuzB0QP gammaBit v

@[expose] def ts (a : Nat) : Bool :=
  allBelow 64 fun b => allBelow 64 fun c =>
    a == 0 || b == 0 || b == a || c == 0 || c == a || c == b || c == (a ^^^ b) ||
      [a, b, c, a ^^^ b, a ^^^ c, b ^^^ c, a ^^^ b ^^^ c].any fun u => qMinusBit u == 1

end CertificateChecks.KernelLC.B0Suz

#kon_slices CertificateChecks.KernelLC.B0Suz.rule 0 64
#kon_join CertificateChecks.KernelLC.B0Suz.ruleAll CertificateChecks.KernelLC.B0Suz.rule 64
#kon_slices CertificateChecks.KernelLC.B0Suz.ts 0 64
#kon_join CertificateChecks.KernelLC.B0Suz.tsAll CertificateChecks.KernelLC.B0Suz.ts 64

end
