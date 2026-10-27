module

public import Certificates.Kernel.ONSeven.RGlueE
public import Certificates.Kernel.ONSeven.RChkC34
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONR

open CFSG.KC.ONR CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.RankThree.Native
open CertificateChecks.KernelSpor.ON8 (onP)

@[expose] noncomputable def comm34 : Bool :=
  allN 2 (fun k => onP (fun y => cF 3 k (cF 3 2 y)) (fun y => cF 3 2 (cF 3 k y))) &&
    allN 2 (fun k => onP (fun y => cF 4 k (cF 4 2 y)) (fun y => cF 4 2 (cF 4 k y)))

theorem comm34_ok : comm34 = true := by quickRfl

theorem cArrs3_size : (onSevenCArrs 3).size = 2 := by
  unfold onSevenCArrs
  rw [Array.size_map]
  rfl

theorem cArrs4_size : (onSevenCArrs 4).size = 2 := by
  unfold onSevenCArrs
  rw [Array.size_map]
  rfl

theorem cAll3_size : (cAll 3).size = 3 := by
  unfold cAll
  rw [cAll_eq (by omega), Array.size_map]
  rfl

theorem cAll4_size : (cAll 4).size = 3 := by
  unfold cAll
  rw [cAll_eq (by omega), Array.size_map]
  rfl

theorem lt3 {s : Nat} (h : s < 3) : s < nat_lit 3 := h

theorem c_check3 : onSevenCCheck (onSevenCR 3) (onSevenRepArr 3) (onSevenCArrs 3)
    (onSevenCTabs 3) (onSevenCCert 3) 49 = true := by
  have hN := Nat.eq_of_beq_eq_true c3_N
  have hEN := Nat.eq_of_beq_eq_true c3_EN
  have hEng := Nat.eq_of_beq_eq_true c3_Eng
  have hc := comm34_ok
  unfold comm34 at hc
  rw [Bool.and_eq_true] at hc
  have bk := EC3.ok
  have kk := EC3.keys
  rw [hEng] at bk
  refine ccheck_full (N := 99) (w := 7) (k := 2) (hr5 := by omega) cArrs3_size
    (by rw [← hN]; exact c3_orb)
    (fun s hs => by rw [← hN]; exact c3Res_all s (lt3 (by rw [cAll3_size] at hs; exact hs)))
    (fun j hj => by rw [cArrs3_size] at hj ⊢; exact allN_spec hc.1 j hj) c34_w
    (fun s hs => Nat.eq_of_beq_eq_true (allN_spec c3_EG s hs)) (fun s hs => allN_spec c3_Gp s hs)
    bk kk (by rw [hEN]; omega) hEN

theorem c_check4 : onSevenCCheck (onSevenCR 4) (onSevenRepArr 4) (onSevenCArrs 4)
    (onSevenCTabs 4) (onSevenCCert 4) 49 = true := by
  have hN := Nat.eq_of_beq_eq_true c4_N
  have hEN := Nat.eq_of_beq_eq_true c4_EN
  have hEng := Nat.eq_of_beq_eq_true c4_Eng
  have hc := comm34_ok
  unfold comm34 at hc
  rw [Bool.and_eq_true] at hc
  have bk := EC4.ok
  have kk := EC4.keys
  rw [hEng] at bk
  refine ccheck_full (N := 99) (w := 7) (k := 2) (hr5 := by omega) cArrs4_size
    (by rw [← hN]; exact c4_orb)
    (fun s hs => by rw [← hN]; exact c4Res_all s (lt3 (by rw [cAll4_size] at hs; exact hs)))
    (fun j hj => by rw [cArrs4_size] at hj ⊢; exact allN_spec hc.2 j hj) c34_w
    (fun s hs => Nat.eq_of_beq_eq_true (allN_spec c4_EG s hs)) (fun s hs => allN_spec c4_Gp s hs)
    bk kk (by rw [hEN]; omega) hEN

end CertificateChecks.KernelSpor.ONR

end
