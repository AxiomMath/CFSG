module

public import Certificates.Kernel.Sporadic.ON.Data
public import Certificates.Kernel.Sporadic.ON.GenF
import Certificates.Kernel.Sporadic.OrbRecGen
meta import Certificates.Kernel.Sporadic.ON.Data
meta import Certificates.Kernel.Sporadic.ON.Gen
meta import Certificates.Kernel.Sporadic.ON.GenF
meta import CFSG.Certificates.Kernel.Common.Eval

namespace CertificateChecks.KernelSpor.ON

open CFSG.KS.ONFGen

meta def chunksM (b : Nat) : List (List Nat) :=
  let L := ((if b == 1 then colsAM else colsBM).map CFSG.KS.ONGen.keyOf).toList
  chunks4 L.length L

open CFSG.KC.Eval in
meta def chunkStep : Step := fun args => do
  let #[.nat b] := args | throw "chunkStep: one number"
  return #[(.anonymous,
    Val.list ((chunksM b).toArray.map fun c => Val.list (c.toArray.map fun x => Val.nat x)))]

meta def leavesA : Array Nat := leavesOf 1 (chunksM 1)

meta def leavesB : Array Nat := leavesOf 2 (chunksM 2)

end CertificateChecks.KernelSpor.ON

public section

set_option maxRecDepth 400000

#kc_eval CertificateChecks.KernelSpor ONFA.CS CertificateChecks.KernelSpor.ON.chunkStep 1
#kc_nattree CertificateChecks.KernelSpor.ONFA.T CertificateChecks.KernelSpor.ON.leavesA
#kc_eval CertificateChecks.KernelSpor ONFB.CS CertificateChecks.KernelSpor.ON.chunkStep 2
#kc_nattree CertificateChecks.KernelSpor.ONFB.T CertificateChecks.KernelSpor.ON.leavesB

namespace CertificateChecks.KernelSpor.ON

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.ONF

theorem tabA : tabChk ONFA.T ONFA.CS 0 = true := by decide +kernel
theorem tabB : tabChk ONFB.T ONFB.CS 0 = true := by decide +kernel
theorem lensA : lensOK ONFA.CS = true := by decide +kernel
theorem lensB : lensOK ONFB.CS = true := by decide +kernel
theorem colsA : colsOK ONV.LA = true := by decide +kernel
theorem colsB : colsOK ONV.LB = true := by decide +kernel
theorem flatA : (ONFA.CS.flatten == ONV.LA) = true := by decide +kernel
theorem flatB : (ONFB.CS.flatten == ONV.LB) = true := by decide +kernel
theorem lenA : ONFA.CS.length = 39 := by decide +kernel
theorem lenB : ONFB.CS.length = 39 := by decide +kernel

@[expose] noncomputable def mvSF (s : Nat) : Bool :=
  mvRangeF ONV.K ONFA.T ONFB.T (nat_lit 39) ONV.A ONV.B (nat_lit 245520) (Nat.mul s (nat_lit 240))
    (nat_lit 240)

theorem mvS_of_F (s : Nat) (h : mvSF s = true) : mvS s = true :=
  mvRangeF_imp tabA lensA colsA flatA lenA tabB lensB colsB flatB lenB h

end CertificateChecks.KernelSpor.ON

end
