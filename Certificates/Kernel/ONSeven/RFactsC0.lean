module

public import Certificates.Kernel.ONSeven.RGlueE
public import Certificates.Kernel.ONSeven.RChkC0
import CFSG.Certificates.Kernel.BfsPinSliceSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONR

open CFSG.KC.ONR CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.RankThree.Native
open CertificateChecks.KernelSpor.ON8 (onP)

@[expose] noncomputable def comm0 : Bool :=
  allN 4 fun k => onP (fun y => cF 0 k (cF 0 4 y)) (fun y => cF 0 4 (cF 0 k y))

theorem comm0_ok : comm0 = true := by quickRfl

theorem cArrs0_size : (onSevenCArrs 0).size = 4 := by
  unfold onSevenCArrs
  rw [Array.size_map]
  rfl

theorem fArrs0_size : (onSevenFArrs 0).size = 2 := by
  unfold onSevenFArrs
  rw [Array.size_map]
  rfl

theorem cAll0_size : (cAll 0).size = 7 := by
  unfold cAll
  rw [cAll_eq (by omega), Array.size_map]
  rfl

theorem c0_res : ∀ s < (cAll 0).size, resK 2746 12 C0.T (cF 0 s) (C0.G s) = true := by
  intro s hs
  rw [← Nat.eq_of_beq_eq_true c0_N]
  exact c0Res_all s (lt7 (by rw [cAll0_size] at hs; exact hs))

theorem c0_orb' : orbK 2746 12 4 C0.T C0.G C0.D C0.S = true := by
  rw [← Nat.eq_of_beq_eq_true c0_N]
  exact c0_orb

theorem ec0_ok : bfsK 2746 12 4 EC0.G 1372 EC0.T EC0.E EC0.S = true := by
  rw [← Nat.eq_of_beq_eq_true c0_Eng, ← Nat.eq_of_beq_eq_true c0_EN]
  exact bfsK_of_slices (L := EC0.L) (K := EC0.K) (C := EC0.C) (by decide) (by decide) c0_w EC0.g
    EC0.csAll EC0.t0 EC0.dist (Nat.eq_of_beq_eq_true EC0.c0) (Nat.eq_of_beq_eq_true EC0.cK)
    EC0.rsAll

theorem ec0_keys : keysSK 2746 12 kbA.toList 1372 EC0.T EC0.SK = true := by
  rw [← Nat.eq_of_beq_eq_true c0_EN]
  exact EC0.keys

theorem ef0_ok : bfsK 2746 12 2 EF0.G 343 EF0.T EF0.E EF0.S = true := by
  rw [← Nat.eq_of_beq_eq_true c0_Fng, ← Nat.eq_of_beq_eq_true c0_FN]
  exact bfsK_of_slices (L := EF0.L) (K := EF0.K) (C := EF0.C) (by decide) (by decide) c0_w EF0.g
    EF0.csAll EF0.t0 EF0.dist (Nat.eq_of_beq_eq_true EF0.c0) (Nat.eq_of_beq_eq_true EF0.cK)
    EF0.rsAll

theorem ef0_keys : keysSK 2746 12 kbA.toList 343 EF0.T EF0.SK = true := by
  rw [← Nat.eq_of_beq_eq_true c0_FN]
  exact EF0.keys

theorem c_check0 : onSevenCCheck (onSevenCR 0) (onSevenRepArr 0) (onSevenCArrs 0)
    (onSevenCTabs 0) (onSevenCCert 0) 1372 = true := by
  have hc := comm0_ok
  unfold comm0 at hc
  exact ccheck_full (k := 4) (by omega) cArrs0_size c0_orb' c0_res
    (fun j hj => by rw [cArrs0_size] at hj ⊢; exact allN_spec hc j hj) c0_w
    (fun s hs => Nat.eq_of_beq_eq_true (allN_spec c0_EG s hs))
    (fun s hs => allN_spec c0_Gp s (by omega)) ec0_ok ec0_keys (by omega) rfl

theorem f_check0 : onSevenFCheck (onSevenCR 0) (onSevenCTabs 0) (onSevenCCert 0) (onSevenFArrs 0)
    (onSevenFTabs 0) (onSevenRepTab 0) (onSevenFCert 0) = true :=
  fcheck_full (k := 4) (nf := 2) (by omega) cArrs0_size fArrs0_size c0_orb' c0_res c0_w
    (fun s hs => Nat.eq_of_beq_eq_true (allN_spec c0_EG s hs))
    (fun s hs => allN_spec c0_Gp s (by omega)) ec0_ok ec0_keys (by omega)
    (fun l hl => Nat.eq_of_beq_eq_true (allN_spec c0_FG l hl)) ef0_ok ef0_keys rfl
    (Nat.eq_of_beq_eq_true c0_X) c0_px c0_f

end CertificateChecks.KernelSpor.ONR

end
