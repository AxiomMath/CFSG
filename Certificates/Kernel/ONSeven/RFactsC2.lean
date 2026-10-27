module

public import Certificates.Kernel.ONSeven.RGlueE
public import Certificates.Kernel.ONSeven.RChkC2
import CFSG.Certificates.Kernel.BfsPinSliceSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONR

open CFSG.KC.ONR CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.RankThree.Native
open CertificateChecks.KernelSpor.ON8 (onP)

@[expose] noncomputable def comm2 : Bool :=
  allN 4 fun k => onP (fun y => cF 2 k (cF 2 4 y)) (fun y => cF 2 4 (cF 2 k y))

theorem comm2_ok : comm2 = true := by quickRfl

theorem cArrs2_size : (onSevenCArrs 2).size = 4 := by
  unfold onSevenCArrs
  rw [Array.size_map]
  rfl

theorem fArrs2_size : (onSevenFArrs 2).size = 3 := by
  unfold onSevenFArrs
  rw [Array.size_map]
  rfl

theorem cAll2_size : (cAll 2).size = 8 := by
  unfold cAll
  rw [cAll_eq (by omega), Array.size_map]
  rfl

theorem c2_res : ∀ s < (cAll 2).size, resK 2772 12 C2.T (cF 2 s) (C2.G s) = true := by
  intro s hs
  rw [← Nat.eq_of_beq_eq_true c2_N]
  exact c2Res_all s (lt8 (by rw [cAll2_size] at hs; exact hs))

theorem c2_orb' : orbK 2772 12 4 C2.T C2.G C2.D C2.S = true := by
  rw [← Nat.eq_of_beq_eq_true c2_N]
  exact c2_orb

theorem ec2_ok : bfsK 2772 12 4 EC2.G 1372 EC2.T EC2.E EC2.S = true := by
  rw [← Nat.eq_of_beq_eq_true c2_Eng, ← Nat.eq_of_beq_eq_true c2_EN]
  exact bfsK_of_slices (L := EC2.L) (K := EC2.K) (C := EC2.C) (by decide) (by decide) c2_w EC2.g
    EC2.csAll EC2.t0 EC2.dist (Nat.eq_of_beq_eq_true EC2.c0) (Nat.eq_of_beq_eq_true EC2.cK)
    EC2.rsAll

theorem ec2_keys : keysSK 2772 12 kbA.toList 1372 EC2.T EC2.SK = true := by
  rw [← Nat.eq_of_beq_eq_true c2_EN]
  exact EC2.keys

theorem ef2_ok : bfsK 2772 12 3 EF2.G 343 EF2.T EF2.E EF2.S = true := by
  rw [← Nat.eq_of_beq_eq_true c2_Fng, ← Nat.eq_of_beq_eq_true c2_FN]
  exact bfsK_of_slices (L := EF2.L) (K := EF2.K) (C := EF2.C) (by decide) (by decide) c2_w EF2.g
    EF2.csAll EF2.t0 EF2.dist (Nat.eq_of_beq_eq_true EF2.c0) (Nat.eq_of_beq_eq_true EF2.cK)
    EF2.rsAll

theorem ef2_keys : keysSK 2772 12 kbA.toList 343 EF2.T EF2.SK = true := by
  rw [← Nat.eq_of_beq_eq_true c2_FN]
  exact EF2.keys

theorem c_check2 : onSevenCCheck (onSevenCR 2) (onSevenRepArr 2) (onSevenCArrs 2)
    (onSevenCTabs 2) (onSevenCCert 2) 1372 = true := by
  have hc := comm2_ok
  unfold comm2 at hc
  exact ccheck_full (k := 4) (by omega) cArrs2_size c2_orb' c2_res
    (fun j hj => by rw [cArrs2_size] at hj ⊢; exact allN_spec hc j hj) c2_w
    (fun s hs => Nat.eq_of_beq_eq_true (allN_spec c2_EG s hs))
    (fun s hs => allN_spec c2_Gp s (by omega)) ec2_ok ec2_keys (by omega) rfl

theorem f_check2 : onSevenFCheck (onSevenCR 2) (onSevenCTabs 2) (onSevenCCert 2) (onSevenFArrs 2)
    (onSevenFTabs 2) (onSevenRepTab 2) (onSevenFCert 2) = true :=
  fcheck_full (k := 4) (nf := 3) (by omega) cArrs2_size fArrs2_size c2_orb' c2_res c2_w
    (fun s hs => Nat.eq_of_beq_eq_true (allN_spec c2_EG s hs))
    (fun s hs => allN_spec c2_Gp s (by omega)) ec2_ok ec2_keys (by omega)
    (fun l hl => Nat.eq_of_beq_eq_true (allN_spec c2_FG l hl)) ef2_ok ef2_keys rfl
    (Nat.eq_of_beq_eq_true c2_X) c2_px c2_f

end CertificateChecks.KernelSpor.ONR

end
