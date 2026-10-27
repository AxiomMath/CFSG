module

public import Certificates.Kernel.Sporadic.SuzK.Data
public import Certificates.Kernel.Sporadic.OddCore.SuzRelabel
public import Certificates.Kernel.Sporadic.OddCore.SuzCert
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzK

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.Row

@[expose] noncomputable def r15 (F : Nat → Nat) (o i : Nat) : Nat := rg (nat_lit 15) (mask (nat_lit 15)) F o i

@[expose] noncomputable def relAt (i : Nat) : Bool :=
  strictB (r15 SuzRelT.F 0 i) fun ri =>
    bAnd(Nat.beq (r15 SuzRelT.F 0 (r32 AL i)) (r15 SuzCertT.F 0 ri),
      Nat.beq (r15 SuzRelT.F 0 (r32 BE i)) (r15 SuzCertT.F (nat_lit 715) ri))

@[expose] noncomputable def relSl (s : Nat) : Bool :=
  strictB (Nat.mul s (nat_lit 2288)) fun lo => allN (nat_lit 2288) fun t => strictB (Nat.add lo t) fun i =>
    bIf(Nat.blt i (nat_lit 22880), relAt i, true)

set_option Elab.async false

theorem neg_rel : Bool.not (Nat.beq (r15 SuzRelT.F 0 (r32 AL 3)) (r15 SuzCertT.F 715 (r15 SuzRelT.F 0 3))) =
    true := by quickRfl

end CertificateChecks.KernelSpor.SuzK

#kon_slices CertificateChecks.KernelSpor.SuzK.relSl 0 10

end
