module

public import Certificates.Kernel.LocalComp.J4Rows
public import CFSG.Certificates.Kernel.OpsKSound
public import CFSG.Sporadic.GLQ.J4TwoRankInputs
import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGLQ.J4Two

open CFSG.SectionRank.Native CFSG.Sporadic.GLQ CFSG.Sporadic.GLQ.J4TwoRank CFSG.KC.OpsK
open CFSG.KC.OpsHom CertificateChecks.KernelLC.J4R

@[expose] noncomputable def outsK (R : Array (Nat × Nat)) : Bool :=
  forceL (List.ofFn fun i => R[j4Outs i]!.1) fun xs => elem2OK (opsF2K 112) xs [0]

theorem kLt : j4Prog.all (Instr.lt 50) = true := by decide +kernel

theorem kJ4 : forceB (powN (opsF2K 112) 4 JB.M 3) (fun B3 => runK (opsF2K 112) j4Prog
    (initRegsN (opsF2K 112) 50 (JA.M, JA.M) (JB.M, B3)) outsK) = true := by
  quickRfl

end CertificateChecks.KernelGLQ.J4Two

end
