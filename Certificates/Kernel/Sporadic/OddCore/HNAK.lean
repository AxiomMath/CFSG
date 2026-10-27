module

public import Certificates.Kernel.Sporadic.OddCore.HNAD
public import Certificates.Kernel.Sporadic.OddCore.HN2092D
public import Certificates.Data.Kernel.Spor.HNAOrb
public import Certificates.Data.Kernel.BfsPinSlice
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Data.Kernel.LocalQT.Nats
public import Certificates.Kernel.LocalQT.Tc.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HNAS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KS.HNA
open CFSG.KC.LQT.NP CertificateChecks.KernelSpor

@[expose] noncomputable def pA (t : Nat) : Nat := HNAT.PN (Nat.mul 2 t)

@[expose] noncomputable def pB (t : Nat) : Nat := HNAT.PN (Nat.succ (Nat.mul 2 t))

theorem pProg : natsOK HNAT.Prog.chars (listUp HNAT.PN 5750) = true := by quickRfl
theorem pPool : natsOK HNAT.Pool.chars (listUp HNAT.QN 96) = true := by quickRfl
theorem pWit : natsOK HNAT.Wit.chars (listUp HNAT.WN 1597) = true := by quickRfl
theorem bWit : wbRun HNAW.C HNAW.F HNAW.M 1024 (listUp HNAT.WN 1597) 0 0 = true := by quickRfl

theorem kBase : allN 12 (fun s => bAnd(Nat.beq (HNAR.X s) (HSG s),
    Nat.beq (HNAR.X (Nat.add 12 s)) (pinvS 1100 11 (mask 11) (HSG s)))) = true := by quickRfl

@[expose] noncomputable def st (s : Nat) : Bool := stepSl 1100 11 24 HNAR.X pA pB 25 s

theorem kPool : allN 48 (fun f => poolK 1100 11 2899 HNAR.X HNAT.QN HNAC.C f) = true := by
  quickRfl

theorem kGens : bAnd(Nat.beq (HNAE.G 0) (HNAR.X 64), bAnd(Nat.beq (HNAE.G 1) (HNAR.X 1067),
    bAnd(Nat.beq (HNAE.G 2) (HNAR.X 1069), bAnd(Nat.beq (HNAE.G 3) (HNAR.X 1071),
      Nat.beq (HNAE.G 4) (HNAR.X 1074))))) = true := by quickRfl

@[expose] noncomputable def SK : List Nat := listUp HNAE.SKT 1024

theorem kHead : (szOK 1100 11 && allN 5 (fun k => canonK 1100 11 (mask 11) (Nat.mul 1100 11)
    (HNAE.G k)) && Nat.beq (HNAE.T 0) (pidn 1100 11) && Nat.beq (HNAE.C 0) 1 &&
    Nat.beq (HNAE.C 32) 1024) = true := by quickRfl

theorem kDist : distinctK 1024 HNAE.T HNAE.S = true := by quickRfl

theorem keys : keysSK 1100 11 [0, 1] 1024 HNAE.T SK = true := by quickRfl

@[expose] noncomputable def cs (s : Nat) : Bool := canonSl 1100 11 HNAE.T 32 s

@[expose] noncomputable def rs (s : Nat) : Bool := runSl 1100 11 5 HNAE.G HNAE.T HNAE.E 32 HNAE.C s

@[expose] noncomputable def wt (s : Nat) : Bool :=
  witSl 1100 11 HNAE.T HNAC.C HNAW.C HNAW.F HNAW.M 48 16 s

end CertificateChecks.KernelSpor.HNAS

set_option Elab.async false

#kqb_range CertificateChecks.KernelSpor.HNAS.stK CertificateChecks.KernelSpor.HNAS.st 0 115
#kqb_all CertificateChecks.KernelSpor.HNAS.stK CertificateChecks.KernelSpor.HNAS.st 115
#kqb_range CertificateChecks.KernelSpor.HNAS.csK CertificateChecks.KernelSpor.HNAS.cs 0 32
#kqb_all CertificateChecks.KernelSpor.HNAS.csK CertificateChecks.KernelSpor.HNAS.cs 32
#kqb_range CertificateChecks.KernelSpor.HNAS.rsK CertificateChecks.KernelSpor.HNAS.rs 0 32
#kqb_all CertificateChecks.KernelSpor.HNAS.rsK CertificateChecks.KernelSpor.HNAS.rs 32
#kqb_range CertificateChecks.KernelSpor.HNAS.wtK CertificateChecks.KernelSpor.HNAS.wt 0 64
#kqb_all CertificateChecks.KernelSpor.HNAS.wtK CertificateChecks.KernelSpor.HNAS.wt 64

end
