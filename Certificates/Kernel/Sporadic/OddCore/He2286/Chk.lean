module

public import Certificates.Kernel.Sporadic.OddCore.HL
public import Certificates.Kernel.LocalComp.HeFixData
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.LocalCompUnpack
public import CFSG.Sporadic.SmallOddCore.HeldTwoAInputs
meta import CFSG.Sporadic.SmallOddCore.HeldTwoAInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.GroupTheory.LocalCores.Fitting

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.He2286

open CFSG.Sporadic.SmallOddCore

meta def uM : Array (Array Nat) := #[heU105Arr, CFSG.PSL3Four.Native.invTab 105 heU105Arr]

end CertificateChecks.KernelSpor.He2286

#kmisc_packarrs CertificateChecks.KernelSpor.He2286.U CertificateChecks.KernelSpor.He2286.uM 7

namespace CertificateChecks.KernelSpor.He2286

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Mathieu CertificateChecks.KernelSpor
open CertificateChecks.KernelLC.HeFix CFSG.Sporadic.SmallOddCore

@[expose] noncomputable def comK (f : Nat → Nat) (D : Nat) : Bool :=
  allN 105 (fun x => Nat.beq (f (pg 7 (mask 7) D x)) (pg 7 (mask 7) D (f x)))

@[expose] noncomputable def comD (f : Nat → Nat) : Bool := allN 5 (fun j => comK f (HDE.G j))

@[expose] noncomputable def ckB (i : Nat) : Bool :=
  strictB (HKE.T i) (fun t => bIf(comD (pg 7 (mask 7) t), Nat.beq t (pidn 105 7), true))

@[expose] noncomputable def ckC (i : Nat) : Bool :=
  strictB (HKE.T i) (fun t =>
    bIf(comD (fun x => pg 7 (mask 7) t (pg 7 (mask 7) (U 0) x)), false, true))

@[expose] noncomputable def slB (lo len : Nat) : Bool := allN len (fun d => ckB (Nat.add lo d))

@[expose] noncomputable def slC (lo len : Nat) : Bool := allN len (fun d => ckC (Nat.add lo d))

theorem kU : bAnd(bindArrK heU105Arr 105 7 (U 0), bAnd(invEqK 105 7 (mask 7) (105 * 7) (U 0) (U 1),
    bAnd(invEqK 105 7 (mask 7) (105 * 7) (U 1) (U 0), bAnd(canonK 105 7 (mask 7) (105 * 7) (U 0),
      Nat.beq HKE.cnt 40320)))) = true := by
  quickRfl

theorem kA : allN 105 (fun i => Nat.beq (nget HeL.omL (pg 7 (mask 7) (U 0) i))
    (pg 14 (mask 14) PU (nget HeL.omL i))) = true := by
  quickRfl

theorem kB0 : slB 0 5040 = true := by quickRfl
theorem kB1 : slB 5040 5040 = true := by quickRfl
theorem kB2 : slB 10080 5040 = true := by quickRfl
theorem kB3 : slB 15120 5040 = true := by quickRfl
theorem kB4 : slB 20160 5040 = true := by quickRfl
theorem kB5 : slB 25200 5040 = true := by quickRfl
theorem kB6 : slB 30240 5040 = true := by quickRfl
theorem kB7 : slB 35280 5040 = true := by quickRfl

theorem kC0 : slC 0 5040 = true := by quickRfl
theorem kC1 : slC 5040 5040 = true := by quickRfl
theorem kC2 : slC 10080 5040 = true := by quickRfl
theorem kC3 : slC 15120 5040 = true := by quickRfl
theorem kC4 : slC 20160 5040 = true := by quickRfl
theorem kC5 : slC 25200 5040 = true := by quickRfl
theorem kC6 : slC 30240 5040 = true := by quickRfl
theorem kC7 : slC 35280 5040 = true := by quickRfl

end CertificateChecks.KernelSpor.He2286

end
