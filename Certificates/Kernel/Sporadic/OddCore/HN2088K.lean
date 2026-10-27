
module

public import Certificates.Kernel.Sporadic.OddCore.HN2088D
public import Certificates.Kernel.Sporadic.OddCore.HN2089D
public import Certificates.Kernel.Sporadic.OddCore.HND1
public import Certificates.Kernel.Sporadic.OddCore.HND4
public import Certificates.Kernel.Sporadic.OddCore.HN2093
public import Certificates.Kernel.LocalQT.Tc.Gen
public import Certificates.Data.Kernel.Spor.EnumBase
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Data.Kernel.Spor.HNAOrb
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HN2088

open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.HNOddCore.InvData
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.BaseEq CFSG.KS.EnumBase
open CertificateChecks.KernelSpor

@[expose] noncomputable def bp : List Nat := [0, 4, 3, 1, 2]

theorem pgb : allN 14 (fun g => bAnd(Nat.beq (HNT.PG.E.getD g []).length 800,
    listFK 10 (HPE.G g) (HNT.PG.E.getD g []) 0)) = true := by quickRfl

theorem cG : allN 14 (fun g => canonK 800 10 (mask 10) (800 * 10) (HPE.G g)) = true := by quickRfl
theorem pG : allN 14 (fun g => permOK 800 10 (mask 10) (800 * 10) (HPE.G g)
    (pinvS 800 10 (mask 10) (HPE.G g))) = true := by quickRfl
theorem gI : allN 14 (fun g => Nat.beq (HPE.GI g) (pinvS 800 10 (mask 10) (HPE.G g))) = true := by
  quickRfl
theorem cGI : allN 14 (fun g => canonK 800 10 (mask 10) (800 * 10) (HPE.GI g)) = true := by
  quickRfl

theorem wP : allN 14 (fun i => wordEqK 800 10 (mask 10) (pidn 800 10) HQS
    (fun g => pinvS 800 10 (mask 10) (HQS g)) 11 pWords[i]! (HPE.G i)) = true := by quickRfl

@[expose] noncomputable def rs (s : Nat) : Bool :=
  sliceK 16384 64 (recK 800 10 (mask 10) 14 HPE.G HPE.T HPE.PL) s

theorem parB : parRK HPE.PL HNT.PAR.E 0 = true := by quickRfl

@[expose] noncomputable def SK : List Nat := HNA.listUp HPSK 16384

theorem keys : CFSG.KC.BfsPin.keysSK 800 10 bp 16384 HPE.T SK = true := by quickRfl

@[expose] noncomputable def ls (s : Nat) : Bool :=
  sliceK 16384 64 (leftK 10 (mask 10) bp 14 16384 HPE.G HPE.T HPE.POS) s

theorem posB : allN 14 (fun g => posRK HPE.POS 14 g (HNT.PL.E.getD g []) 0) = true := by quickRfl

theorem sqCnt : Nat.beq (cntN 16384 (fun k => sqFixK 10 (mask 10) bp (HPE.T k))) 880 = true := by
  quickRfl

@[expose] noncomputable def cl (c : Nat) : Bool :=
  classK 10 (mask 10) bp 14 16384 HPE.G HPE.GI HPE.T (r32 HPF.L) (r32 HPF.P) (r32 HPF.G)
    (r32 HPF.Q) (r32 HPF.O) (r32 HPF.MK) (r32 HPF.PX) c

theorem reps : allN 29 (fun c => Nat.beq (r32 HPF.L (r32 HPF.O c))
    ((ClsT.E.getD c []).headD 0)) = true := by quickRfl

@[expose] noncomputable def cv (s : Nat) : Bool :=
  sliceK 16384 1024 (coverK 10 (mask 10) bp 29 HPE.T (r32 HPF.L) (r32 HPF.O) (r32 HPF.MK)
    (r32 HPF.PX)) s

theorem hpc : allN 14 (fun j => Nat.beq (HPE.G j) (HPC.S j)) = true := by quickRfl
theorem pPC : allN 19 (fun j => permOK 800 10 (mask 10) (800 * 10) (HPC.S j) (HPC.SI j)) = true := by
  quickRfl
theorem bPC : allN 5 (fun t => Nat.beq (pg 10 (mask 10) HPC.BP t)
    ((QData.pbarBase.map Fin.val).toArray[t]!)) = true := by quickRfl

end CertificateChecks.KernelSpor.HN2088

set_option Elab.async false

#kqb_range CertificateChecks.KernelSpor.HN2088.rsK CertificateChecks.KernelSpor.HN2088.rs 0 256
#kqb_all CertificateChecks.KernelSpor.HN2088.rsK CertificateChecks.KernelSpor.HN2088.rs 256
#kqb_range CertificateChecks.KernelSpor.HN2088.lsK CertificateChecks.KernelSpor.HN2088.ls 0 256
#kqb_all CertificateChecks.KernelSpor.HN2088.lsK CertificateChecks.KernelSpor.HN2088.ls 256
#kqb_range CertificateChecks.KernelSpor.HN2088.clK CertificateChecks.KernelSpor.HN2088.cl 0 29
#kqb_all CertificateChecks.KernelSpor.HN2088.clK CertificateChecks.KernelSpor.HN2088.cl 29
#kqb_range CertificateChecks.KernelSpor.HN2088.cvK CertificateChecks.KernelSpor.HN2088.cv 0 16
#kqb_all CertificateChecks.KernelSpor.HN2088.cvK CertificateChecks.KernelSpor.HN2088.cv 16

end
