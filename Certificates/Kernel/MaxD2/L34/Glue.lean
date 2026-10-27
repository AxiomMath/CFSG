module

public import Certificates.Kernel.MaxD2.L34.Checks
public import CFSG.Certificates.Kernel.MaxD2.Max
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.L34

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open Certificates.MaxD2Perm

@[expose] noncomputable def KL : Pk where
  n := 42
  w := 6
  kG := 3
  Gp := GP
  GIp := GPI
  rcnt := RE.cnt
  RG := RE.G
  RGI := RE.GI
  RT := RE.T
  RPL := RE.PL
  RPOS := RE.POS
  RSRT := RE.SRT
  RSRI := RE.SRI
  kN := NE.k
  cnt := NE.cnt
  NG := NE.G
  NGI0 := NE.GI
  NT := NE.T
  NPL := NE.PL
  NPOS := NE.POS
  NSRT := NE.SRT
  NSRI := NE.SRI
  NGI := NGI
  nr := 8
  REP := REP
  REPI := REPI
  np := 2
  kw := 12
  PT := r32 PT
  FS := FS
  KS := KS
  RB := RB
  H := H
  CN := r32 CN
  TP := TT 0
  TPI := TT 1
  th := r32 MISC 0
  CH := CH
  NH := NH
  L := r32 L
  hi := 1
  cw := 6
  nl := r32 MISC 1
  MK := rg 128 (mask 128) MK 0
  mj := 0
  mi := 0
  RB2 := RB2
  H2 := H2
  PQ := fun i j => Nat.add (Nat.div (Nat.mul j (Nat.sub j 1)) 2) i

theorem gT_bind : ∀ k < 3, l34InnerData.gT[k]! = unpack 42 6 (GP k) := by
  intro k hk
  interval_cases k <;> decide +kernel

theorem hyps : Hyps l34InnerData KL := by
  constructor
  case hn => exact k_sz
  case hDn => exact rfl
  case hGs => exact rfl
  case hGb => exact gT_bind
  case hGp => exact k_gp
  case hRG =>
    intro j hj
    interval_cases j
    · exact ⟨k_rg0, (PK.allN_iff.1 k_rgc) 0 (by decide)⟩
    · exact ⟨k_rg1, (PK.allN_iff.1 k_rgc) 1 (by decide)⟩
  case hRh => exact k_rh
  case hRp => exact fun i hi => penumSl_spec k_rsl i (Nat.zero_le _) (by exact hi) hi
  case hRc => exact rfl
  case hNk => exact rfl
  case hNG => exact fun j hj => band_e ((PK.allN_iff.1 k_ng) j hj)
  case hNh => exact k_nh
  case hNp => exact fun i hi => penumSl_spec k_nsl i (Nat.zero_le _) (by exact hi) hi
  case hNc => exact rfl
  case hNI => exact fun j hj => (PK.allN_iff.1 k_ngi) j hj
  case hNorm => exact fun j hj i hi => band_e ((PK.allN_iff.1 ((PK.allN_iff.1 k_norm) j hj)) i hi)
  case hMj => exact (by decide : 0 < 3)
  case hMi => exact (by decide : 0 < 2)
  case hMv =>
    dsimp only [KL]
    exact k_mv
  case hTw => exact k_tw
  case hTp => exact k_tp
  case hTh => exact Nat.blt_eq.mp k_th1
  case hTn => exact Nat.eq_of_beq_eq_true k_th2
  case hTk => exact k_tk
  case hC => exact fun k hk => (PK.allN_iff.1 k_cent) k hk
  case hRn => exact rfl
  case hR0 => exact Nat.eq_of_beq_eq_true k_r0
  case hRw => exact fun i hi => (PK.allN_iff.1 k_rw) i hi
  case hRi => exact fun i hi => (PK.allN_iff.1 k_ri) i hi
  case hPts =>
    exact ⟨rfl, fun t ht => ⟨Nat.eq_of_beq_eq_true (band_e ((PK.allN_iff.1 k_pts) t ht)).1,
      Nat.blt_eq.mp (band_e ((PK.allN_iff.1 k_pts) t ht)).2⟩⟩
  case hS => exact fun s hs => (PK.allN_iff.1 k_srt) s hs
  case hTest =>
    intro i h0 hi
    have hi' : i < 8 := hi
    have h := (PK.allN_iff.1 k_test) (i - 1) (by omega)
    have e : Nat.succ (i - 1) = i := by omega
    rw [e] at h
    exact h
  case hCnt =>
    intro i h0 hi
    have hi' : i < 8 := hi
    have h := (PK.allN_iff.1 k_cnt) (i - 1) (by omega)
    have e : Nat.succ (i - 1) = i := by omega
    rw [e] at h
    exact Nat.eq_of_beq_eq_true h
  case hSum => exact Nat.eq_of_beq_eq_true k_sum
  case hL => exact k_lab
  case hM => exact (by decide : 42 ≤ 64 * 1)
  case hMK => exact fun i hi => Nat.eq_of_beq_eq_true ((PK.allN_iff.1 k_mk) i hi)
  case hMd =>
    intro i hi j hj hij
    exact Or.inr (bif_t (Nat.blt_eq.mpr hij) ((PK.allN_iff.1 ((PK.allN_iff.1 k_pair) i hi)) j hj))
  case hGl => exact rfl
  case hGen =>
    exact fun i hi => ⟨Nat.eq_of_beq_eq_true (band_e ((PK.allN_iff.1 k_gen) i hi)).1,
      fun j hj => (PK.allN_iff.1 (band_e ((PK.allN_iff.1 k_gen) i hi)).2) j hj⟩

theorem l34_check : check l34InnerData = true := check_of hyps

end CertificateChecks.KernelMaxD2.L34

end
