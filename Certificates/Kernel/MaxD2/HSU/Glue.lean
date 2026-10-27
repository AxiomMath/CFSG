module

public import Certificates.Kernel.MaxD2.HSU.Checks
public import Certificates.Kernel.MaxD2.HSU.Comm
public import Certificates.Kernel.MaxD2.HSP.Glue
public import CFSG.Certificates.Kernel.MaxD2.Heis

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.HSU

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open Certificates.MaxD2Perm Certificates.MaxD2Heis Certificates.HSU35
open Certificates.HSOver (hsOverDataP)

@[expose] noncomputable def KH : Pk where
  n := 100
  w := 7
  kG := 2
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
  nr := 2
  REP := REP
  REPI := REPI
  np := 100
  kw := 700
  PT := r32 PT
  FS := FS
  KS := KS
  RB := RB
  H := H
  CN := r32 CN
  TP := TT 0
  TPI := TT 1
  th := r32 MISC 2
  CH := CH
  NH := NH
  L := r32 L
  hi := 2
  cw := 7
  nl := r32 MISC 0
  MK := rg 64 (mask 64) MK 0
  mj := r32 MISC 3
  mi := r32 MISC 4

theorem gT_bind : ∀ k < 2, dataU.gT[k]! = unpack 100 7 (GP k) := by
  intro k hk
  have e : dataU.gT[k]! = wT hsOverDataP (uWords[k]!) := by
    interval_cases k <;> rfl
  rw [e]
  exact c_wT_u HSP.hypsC ((PK.allN_iff.1 k_xy) k hk)

theorem n_pt {i : Nat} (hi : i < NE.cnt) : penumPtK 100 7 (mask 7) (100 * 7) false NE.G NE.GI
    NE.k NE.cnt NE.T NE.PL NE.POS NE.SRT NE.SRI i = true := by
  have e : NE.cnt = 1000 := rfl
  have sl : ∀ lo, lo < 2 → penumSlK 100 7 (mask 7) (100 * 7) false NE.G NE.GI NE.k NE.cnt
      NE.T NE.PL NE.POS NE.SRT NE.SRI (500 * lo) 500 = true := by
    intro lo hlo
    interval_cases lo
    exacts [n_sl0, n_sl500]
  exact penumSl_spec (sl (i / 500) (by omega)) i (by omega) (by omega) hi

theorem comm_of {lo m : Nat} (h : commsK lo m = true) : ∀ k, lo ≤ k → k < lo + m →
    ∀ l < k + 1, commK 100 7 RE.cnt 5 RE.T (r32 ZP) (r32 CZ) k l = true := by
  intro k h1 h2 l hl
  unfold commsK at h
  have e : Nat.add lo (k - lo) = k := by
    change lo + (k - lo) = k
    omega
  have h' := (PK.allN_iff.1 ((PK.allN_iff.1 h) (k - lo) (by omega))) l (by rw [e]; omega)
  rw [e] at h'
  exact h'

theorem cn_if (i : Nat) :
    nIf(Nat.beq i 0, NE.cnt, r32 CN i) = if i = 0 then NE.cnt else r32 CN i := by
  cases i <;> rfl

theorem mv_j : r32 MISC 3 < 2 := by
  have h := k_mvi
  cases e : Nat.blt (r32 MISC 3) 2
  · rw [e] at h
    exact absurd h (by decide)
  · exact Nat.blt_eq.mp e

theorem mv_i : r32 MISC 4 < 2 := by
  have h := k_mvi
  rw [Nat.blt_eq.mpr mv_j] at h
  exact Nat.blt_eq.mp h

theorem pair_none : ∀ q < r32 MISC 1, pairK 100 7 100 700 NE.cnt (r32 PT) NE.T FS KS REP REPI
    (fun _ => 0) (fun _ => 0) q ((fun _ => 0) q) ((fun _ => 0) q) = true := by
  intro q hq
  rw [Nat.eq_of_beq_eq_true k_np0] at hq
  exact absurd hq (Nat.not_lt_zero q)

theorem hypsH : HypsH dataU KH (r32 ZP) (r32 ZX) (r32 CZ) where
  hn := k_sz
  hDn := rfl
  hGs := rfl
  hGb := gT_bind
  hGp := k_gp
  hNk := rfl
  hNG := fun j hj => band_e ((PK.allN_iff.1 k_ng) j hj)
  hNh := k_nh
  hNp := fun i hi => n_pt hi
  hNc := rfl
  hNI := fun j hj => (PK.allN_iff.1 k_ngi) j hj
  hRn := rfl
  hR0 := Nat.eq_of_beq_eq_true k_r0
  hRw := fun i hi => (PK.allN_iff.1 k_rw) i hi
  hRi := fun i hi => (PK.allN_iff.1 k_ri) i hi
  hPts := ⟨rfl, fun t ht => ⟨Nat.eq_of_beq_eq_true (band_e ((PK.allN_iff.1 k_pts) t ht)).1,
      Nat.blt_eq.mp (band_e ((PK.allN_iff.1 k_pts) t ht)).2⟩⟩
  hS := fun s hs => (PK.allN_iff.1 k_srt) s hs
  hTest := by
    intro i h0 hi
    have hi' : i < 2 := hi
    have e : i = 1 := by omega
    rw [e]
    exact k_rep
  hCnt := by
    intro i h0 hi
    have hi' : i < 2 := hi
    have e : i = 1 := by omega
    rw [e]
    exact Nat.eq_of_beq_eq_true k_cnt
  hSum := Nat.eq_of_beq_eq_true k_sum
  hL := k_lab
  hM := (by decide : 100 ≤ 64 * 2)
  hMK := fun i hi => Nat.eq_of_beq_eq_true ((PK.allN_iff.1 k_mk) i hi)
  hMd := by
    intro i hi j hj hij
    rcases md_of_sel k_sel pair_none i hi j hj hij with h | h | h
    · exact Or.inl h
    · refine Or.inr (Or.inl ?_)
      rw [cn_if, cn_if] at h
      exact h
    · exact Or.inr (Or.inr h)
  hRG := by
    intro j hj
    interval_cases j
    · exact ⟨k_rg0, (PK.allN_iff.1 k_rgc) 0 (by decide)⟩
    · exact ⟨k_rg1, (PK.allN_iff.1 k_rgc) 1 (by decide)⟩
  hRh := k_rh
  hRp := fun i hi => penumSl_spec k_rsl i (Nat.zero_le _) (by exact hi) hi
  hRc := rfl
  hNorm := fun j hj i hi => band_e ((PK.allN_iff.1 ((PK.allN_iff.1 k_norm) j hj)) i hi)
  hMj := mv_j
  hMi := mv_i
  hMv := k_mv
  hZ := k_z
  hUV := k_uv
  hExp := k_exp
  hComm := by
    intro k hk l hl
    have hk' : k < 125 := hk
    by_cases a0 : k < 56
    · exact comm_of k_comm0 k (by omega) (by omega) l hl
    by_cases a1 : k < 79
    · exact comm_of k_comm1 k (by omega) (by omega) l hl
    by_cases a2 : k < 97
    · exact comm_of k_comm2 k (by omega) (by omega) l hl
    by_cases a3 : k < 112
    · exact comm_of k_comm3 k (by omega) (by omega) l hl
    · exact comm_of k_comm4 k (by omega) (by omega) l hl
  hTw := k_tw
  hTp := k_tp
  hTh := Nat.blt_eq.mp k_th1
  hTn := Nat.eq_of_beq_eq_true k_th2
  hTk := k_tk
  hC := fun k hk => (PK.allN_iff.1 k_cent) k hk
  hGl := rfl
  hGen := fun i hi => ⟨Nat.eq_of_beq_eq_true (band_e ((PK.allN_iff.1 k_gen) i hi)).1,
    fun j hj => (PK.allN_iff.1 (band_e ((PK.allN_iff.1 k_gen) i hi)).2) j hj⟩

theorem hsU_heis : checkHeis dataU = true := checkHeis_of hypsH

end CertificateChecks.KernelMaxD2.HSU

end
