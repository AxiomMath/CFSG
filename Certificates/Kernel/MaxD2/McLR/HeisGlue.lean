module

public import Certificates.Kernel.MaxD2.McLR.Glue
public import Certificates.Kernel.MaxD2.McLR.HeisChecks
public import Certificates.Kernel.MaxD2.McLR.HeisComm
public import Certificates.Kernel.MaxD2.McLR.HeisPairs
public import CFSG.Certificates.Kernel.MaxD2.Heis

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.McLR

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open Certificates.MaxD2Perm Certificates.MaxD2Heis

@[expose] noncomputable def KH : Pk where
  n := 275
  w := 9
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
  nr := 69
  REP := REP
  REPI := REPI
  np := 2
  kw := 18
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
  hi := 5
  cw := 9
  nl := r32 MISC 0
  MK := rg 64 (mask 64) MK 0
  mj := r32 MISC 3
  mi := r32 MISC 4
  RB2 := RB2
  H2 := H2
  PQ := fun i j => r32 PQ (j * (j - 1) / 2 + i)

theorem comm_of {lo m : Nat} (h : commsK lo m = true) : ∀ k, lo ≤ k → k < lo + m →
    ∀ l < k + 1, commK 275 9 RE.cnt 5 RE.T (r32 ZP) (r32 CZ) k l = true := by
  intro k h1 h2 l hl
  unfold commsK at h
  have e : Nat.add lo (k - lo) = k := by
    change lo + (k - lo) = k
    omega
  have h' := (PK.allN_iff.1 ((PK.allN_iff.1 h) (k - lo) (by omega))) l (by rw [e]; omega)
  rw [e] at h'
  exact h'

theorem pair_all : ∀ c < 13, pairsK c = true := by
  intro c hc
  interval_cases c
  exacts [k_pair0, k_pair1, k_pair2, k_pair3, k_pair4, k_pair5, k_pair6, k_pair7, k_pair8,
    k_pair9, k_pair10, k_pair11, k_pair12]

theorem pair_of : ∀ q < r32 MISC 1, pairK 275 9 2 18 NE.cnt (r32 PT) NE.T FS KS REP REPI RB2 H2 q
    (r32 PI q) (r32 PJ q) = true := by
  intro q hq
  rw [Nat.eq_of_beq_eq_true k_np2] at hq
  have h0 := pair_all (q / 21) (by omega)
  unfold pairsK at h0
  have h := (PK.allN_iff.1 h0) (q % 21) (by omega)
  rw [PK.strictB_eq] at h
  have e : Nat.add (Nat.mul 21 (q / 21)) (q % 21) = q := by
    change 21 * (q / 21) + q % 21 = q
    omega
  rw [e] at h
  exact h

theorem cn_if (i : Nat) :
    nIf(Nat.beq i 0, NE.cnt, r32 CN i) = if i = 0 then NE.cnt else r32 CN i := by
  cases i <;> rfl

theorem mv_j : r32 MISC 3 < 3 := by
  have h := k_mvi
  cases e : Nat.blt (r32 MISC 3) 3
  · rw [e] at h
    exact absurd h (by decide)
  · exact Nat.blt_eq.mp e

theorem mv_i : r32 MISC 4 < 2 := by
  have h := k_mvi
  rw [Nat.blt_eq.mpr mv_j] at h
  exact Nat.blt_eq.mp h

theorem hypsH : HypsH mclFiveDataR KH (r32 ZP) (r32 ZX) (r32 CZ) where
  hn := hypsC.hn
  hDn := hypsC.hDn
  hGs := hypsC.hGs
  hGb := hypsC.hGb
  hGp := hypsC.hGp
  hNk := hypsC.hNk
  hNG := hypsC.hNG
  hNh := hypsC.hNh
  hNp := hypsC.hNp
  hNc := hypsC.hNc
  hNI := hypsC.hNI
  hRn := hypsC.hRn
  hR0 := hypsC.hR0
  hRw := hypsC.hRw
  hRi := hypsC.hRi
  hPts := hypsC.hPts
  hS := hypsC.hS
  hTest := hypsC.hTest
  hCnt := hypsC.hCnt
  hSum := Nat.eq_of_beq_eq_true k_sum
  hL := k_lab
  hM := (by decide : 275 ≤ 64 * 5)
  hMK := fun i hi => Nat.eq_of_beq_eq_true ((PK.allN_iff.1 k_mk) i hi)
  hMd := by
    intro i hi j hj hij
    rcases md_of_sel k_sel pair_of i hi j hj hij with h | h | h
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

theorem mcl_heis : checkHeis mclFiveDataR = true := checkHeis_of hypsH

end CertificateChecks.KernelMaxD2.McLR

end
