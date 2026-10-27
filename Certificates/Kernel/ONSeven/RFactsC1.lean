module

public import Certificates.Kernel.ONSeven.RGlueE
public import Certificates.Kernel.ONSeven.RChkC1
import CFSG.Certificates.Kernel.BfsPinSliceSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONR

open CFSG.KC.ONR CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.RankThree.Native
open CertificateChecks.KernelSpor.ON8 (onP)

@[expose] noncomputable def comm1 : Bool :=
  allN 4 fun k => onP (fun y => cF 1 k (cF 1 4 y)) (fun y => cF 1 4 (cF 1 k y))

theorem comm1_ok : comm1 = true := by quickRfl

theorem cArrs1_size : (onSevenCArrs 1).size = 4 := by
  unfold onSevenCArrs
  rw [Array.size_map]
  rfl

theorem fArrs1_size : (onSevenFArrs 1).size = 2 := by
  unfold onSevenFArrs
  rw [Array.size_map]
  rfl

theorem cAll1_size : (cAll 1).size = 7 := by
  unfold cAll
  rw [cAll_eq (by omega), Array.size_map]
  rfl

theorem c1_res : ∀ s < (cAll 1).size, resK 2746 12 C1.T (cF 1 s) (C1.G s) = true := by
  intro s hs
  rw [← Nat.eq_of_beq_eq_true c1_N]
  exact c1Res_all s (lt7 (by rw [cAll1_size] at hs; exact hs))

theorem c1_orb' : orbK 2746 12 4 C1.T C1.G C1.D C1.S = true := by
  rw [← Nat.eq_of_beq_eq_true c1_N]
  exact c1_orb

theorem ec1_ok : bfsK 2746 12 4 EC1.G 1372 EC1.T EC1.E EC1.S = true := by
  rw [← Nat.eq_of_beq_eq_true c1_Eng, ← Nat.eq_of_beq_eq_true c1_EN]
  exact bfsK_of_slices (L := EC1.L) (K := EC1.K) (C := EC1.C) (by decide) (by decide) c1_w EC1.g
    EC1.csAll EC1.t0 EC1.dist (Nat.eq_of_beq_eq_true EC1.c0) (Nat.eq_of_beq_eq_true EC1.cK)
    EC1.rsAll

theorem ec1_keys : keysSK 2746 12 kbA.toList 1372 EC1.T EC1.SK = true := by
  rw [← Nat.eq_of_beq_eq_true c1_EN]
  exact EC1.keys

theorem ef1_ok : bfsK 2746 12 2 EF1.G 343 EF1.T EF1.E EF1.S = true := by
  rw [← Nat.eq_of_beq_eq_true c1_Fng, ← Nat.eq_of_beq_eq_true c1_FN]
  exact bfsK_of_slices (L := EF1.L) (K := EF1.K) (C := EF1.C) (by decide) (by decide) c1_w EF1.g
    EF1.csAll EF1.t0 EF1.dist (Nat.eq_of_beq_eq_true EF1.c0) (Nat.eq_of_beq_eq_true EF1.cK)
    EF1.rsAll

theorem ef1_keys : keysSK 2746 12 kbA.toList 343 EF1.T EF1.SK = true := by
  rw [← Nat.eq_of_beq_eq_true c1_FN]
  exact EF1.keys

theorem c_check1 : onSevenCCheck (onSevenCR 1) (onSevenRepArr 1) (onSevenCArrs 1)
    (onSevenCTabs 1) (onSevenCCert 1) 1372 = true := by
  have hc := comm1_ok
  unfold comm1 at hc
  exact ccheck_full (k := 4) (by omega) cArrs1_size c1_orb' c1_res
    (fun j hj => by rw [cArrs1_size] at hj ⊢; exact allN_spec hc j hj) c1_w
    (fun s hs => Nat.eq_of_beq_eq_true (allN_spec c1_EG s hs))
    (fun s hs => allN_spec c1_Gp s (by omega)) ec1_ok ec1_keys (by omega) rfl

theorem f_check1 : onSevenFCheck (onSevenCR 1) (onSevenCTabs 1) (onSevenCCert 1) (onSevenFArrs 1)
    (onSevenFTabs 1) (onSevenRepTab 1) (onSevenFCert 1) = true :=
  fcheck_full (k := 4) (nf := 2) (by omega) cArrs1_size fArrs1_size c1_orb' c1_res c1_w
    (fun s hs => Nat.eq_of_beq_eq_true (allN_spec c1_EG s hs))
    (fun s hs => allN_spec c1_Gp s (by omega)) ec1_ok ec1_keys (by omega)
    (fun l hl => Nat.eq_of_beq_eq_true (allN_spec c1_FG l hl)) ef1_ok ef1_keys rfl
    (Nat.eq_of_beq_eq_true c1_X) c1_px c1_f

end CertificateChecks.KernelSpor.ONR

end
