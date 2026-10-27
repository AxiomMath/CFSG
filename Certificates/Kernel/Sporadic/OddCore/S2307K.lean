module

public import Certificates.Kernel.Sporadic.OddCore.S2307D
public import Certificates.Kernel.LocalQT.Tc.Gen
public import Certificates.Data.Kernel.Spor.EnumBase
public import Certificates.Data.Kernel.Spor.EnumBaseLex
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Data.Kernel.Spor.HNAOrb
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S2307

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.BaseEq CFSG.KS.EnumBase
open CertificateChecks.KernelSpor

@[expose] noncomputable def bp : List Nat := [0, 1]

theorem cG : allN 11 (fun g => canonK 1782 11 (mask 11) (1782 * 11) (SSE.G g)) = true := by
  quickRfl
theorem pG : allN 11 (fun g => permOK 1782 11 (mask 11) (1782 * 11) (SSE.G g)
    (pinvS 1782 11 (mask 11) (SSE.G g))) = true := by quickRfl
theorem gI : allN 11 (fun g => Nat.beq (SSE.GI g) (pinvS 1782 11 (mask 11) (SSE.G g))) = true := by
  quickRfl
theorem cGI : allN 11 (fun g => canonK 1782 11 (mask 11) (1782 * 11) (SSE.GI g)) = true := by
  quickRfl
theorem cI : canonK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) = true := by quickRfl
theorem idk : idK 1782 11 (mask 11) = true := by quickRfl
theorem szk : szOK 1782 11 = true := by quickRfl

@[expose] noncomputable def rs (s : Nat) : Bool :=
  sliceK 16384 64 (recK 1782 11 (mask 11) 11 SSE.G SSE.T SSE.PL) s

@[expose] noncomputable def ls (s : Nat) : Bool :=
  sliceK 16384 64 (fun k => bAnd(leftK 11 (mask 11) bp 11 16384 SSE.G SSE.T SSE.POS k,
    lexPosK 11 16384 SSE.PL SSE.POS k)) s

@[expose] noncomputable def SK : List Nat := HNA.listUp SSK 16384

theorem pl0 : Nat.beq (r32 SSE.PL 0) 0 = true := by quickRfl

theorem keys : CFSG.KC.BfsPin.keysSK 1782 11 bp 16384 SSE.T SK = true := by quickRfl

theorem sqCnt : Nat.beq (cntN 16384 (fun k => bIf(Nat.beq k (nat_lit 0), false,
    sqFixK 11 (mask 11) bp (SSE.T k)))) 911 = true := by quickRfl

@[expose] noncomputable def cl (c : Nat) : Bool :=
  classK 11 (mask 11) bp 11 16384 SSE.G SSE.GI SSE.T (r32 SSF.L) (r32 SSF.P) (r32 SSF.G)
    (r32 SSF.Q) (r32 SSF.O) (r32 SSF.MK) (r32 SSF.PX) c

@[expose] noncomputable def cv (s : Nat) : Bool :=
  sliceK 16384 1024 (coverK 11 (mask 11) bp 22 SSE.T (r32 SSF.L) (r32 SSF.O) (r32 SSF.MK)
    (r32 SSF.PX)) s

theorem hpc : allN 11 (fun j => Nat.beq (SSE.G j) (SSC.S j)) = true := by quickRfl
theorem pPC : allN 14 (fun j => permOK 1782 11 (mask 11) (1782 * 11) (SSC.S j) (SSC.SI j)) =
    true := by quickRfl
theorem bPC : allN 2 (fun t => Nat.beq (pg 11 (mask 11) SSC.BP t) ([0, 1].getD t 0)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.S2307

set_option Elab.async false

#kqb_range CertificateChecks.KernelSpor.S2307.rsK CertificateChecks.KernelSpor.S2307.rs 0 256
#kqb_all CertificateChecks.KernelSpor.S2307.rsK CertificateChecks.KernelSpor.S2307.rs 256
#kqb_range CertificateChecks.KernelSpor.S2307.lsK CertificateChecks.KernelSpor.S2307.ls 0 256
#kqb_all CertificateChecks.KernelSpor.S2307.lsK CertificateChecks.KernelSpor.S2307.ls 256
#kqb_range CertificateChecks.KernelSpor.S2307.clK CertificateChecks.KernelSpor.S2307.cl 0 22
#kqb_all CertificateChecks.KernelSpor.S2307.clK CertificateChecks.KernelSpor.S2307.cl 22
#kqb_range CertificateChecks.KernelSpor.S2307.cvK CertificateChecks.KernelSpor.S2307.cv 0 16
#kqb_all CertificateChecks.KernelSpor.S2307.cvK CertificateChecks.KernelSpor.S2307.cv 16

end
