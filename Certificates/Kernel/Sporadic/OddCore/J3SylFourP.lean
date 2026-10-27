module

public import Certificates.Kernel.Sporadic.OddCore.J3HypSyl
public import Certificates.Data.Kernel.Spor.FiveK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelSpor.J3SylFourP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.MulH CertificateChecks.KernelSpor

@[expose] noncomputable def cgP (l : Nat) : Nat := J3CentP (Nat.add l (nat_lit 10))

@[expose] noncomputable def cgPI (l : Nat) : Nat := J3CentI (Nat.add l (nat_lit 10))

@[expose] noncomputable def rowP (e s : Nat) : Bool :=
  strictB (pcomp 6156 13 (mask 13) s s) (fun s2 =>
    bIf(bAnd(Nat.beq (pcomp 6156 13 (mask 13) s2 s2) e,
        bAnd(bIf(Nat.beq s2 e, false, true), bIf(Nat.beq s e, false, true))),
      fiveTopK 6156 13 (mask 13) cgP cgPI 5 2 s, true))

@[expose] noncomputable def p0Row (i : Nat) : Bool :=
  strictB (pidn 6156 13) (fun e => strictB (J3HS.T i) (fun s => rowP e s))

theorem p0Five0 : slK 128 p0Row 0 16 = true := by quickRfl

theorem p0Five1 : slK 128 p0Row 16 16 = true := by quickRfl

theorem p0Five2 : slK 128 p0Row 32 16 = true := by quickRfl

theorem p0Five3 : slK 128 p0Row 48 16 = true := by quickRfl

theorem p0Five4 : slK 128 p0Row 64 16 = true := by quickRfl

theorem p0Five5 : slK 128 p0Row 80 16 = true := by quickRfl

theorem p0Five6 : slK 128 p0Row 96 16 = true := by quickRfl

theorem p0Five7 : slK 128 p0Row 112 16 = true := by quickRfl

end CertificateChecks.KernelSpor.J3SylFourP

end
