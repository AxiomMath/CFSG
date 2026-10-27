module

public import Certificates.Kernel.MaxD2.TitsA.Checks
public import Certificates.Kernel.MaxD2.TitsA.Tests
public import Certificates.Kernel.MaxD2.TitsA.N0
public import Certificates.Kernel.MaxD2.TitsA.N1
public import Certificates.Kernel.MaxD2.TitsA.N2
public import Certificates.Kernel.MaxD2.TitsA.N3
public import Certificates.Kernel.MaxD2.TitsA.N4
public import Certificates.Kernel.MaxD2.TitsA.N5
public import Certificates.Kernel.MaxD2.TitsA.N6
public import Certificates.Kernel.MaxD2.TitsA.N7
public import Certificates.Kernel.MaxD2.TitsA.N8
public import Certificates.Kernel.MaxD2.TitsA.N9
public import Certificates.Kernel.MaxD2.TitsA.N10
public import Certificates.Kernel.MaxD2.TitsA.N11
public import CFSG.Certificates.Kernel.MaxD2.Max
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Kernel.EvenBN.DWord

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.TitsA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelEvenBN Certificates.MaxD2Perm
open CFSG.Sporadic.Schreier.Tits

@[expose] noncomputable def KA : Pk where
  n := 1755
  w := 11
  kG := 6
  Gp := GA
  GIp := GIA
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
  nr := 16
  REP := REP
  REPI := REPI
  np := 6
  kw := 66
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
  hi := 28
  cw := 11
  nl := r32 MISC 1
  MK := rg 512 (mask 512) MK 0
  mj := 0
  mi := 0

theorem gTA_bind : titsAData.gT.size = 6 ∧ ∀ k < 6, titsAData.gT[k]! = unpack 1755 11 (GA k) := by
  have hg : titsAData.gT = List.toArray [titsDArr 0, titsDArr 1, titsGenArrs[0]!, titsGenArrs[1]!,
      titsGenArrs[2]!, titsGenArrs[3]!] := rfl
  refine ⟨rfl, fun k hk => ?_⟩
  rw [hg, List.getElem!_toArray]
  interval_cases k
  · rw [List.getElem!_cons_zero]
    exact titsDArr_eq (by decide)
  · rw [List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact titsDArr_eq (by decide)
  · rw [List.getElem!_cons_succ, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact gens_bind.2 0 (by decide)
  · rw [List.getElem!_cons_succ, List.getElem!_cons_succ, List.getElem!_cons_succ,
      List.getElem!_cons_zero]
    exact gens_bind.2 1 (by decide)
  · rw [List.getElem!_cons_succ, List.getElem!_cons_succ, List.getElem!_cons_succ,
      List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact gens_bind.2 2 (by decide)
  · rw [List.getElem!_cons_succ, List.getElem!_cons_succ, List.getElem!_cons_succ,
      List.getElem!_cons_succ, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact gens_bind.2 3 (by decide)

theorem n_pt {i : Nat} (hi : i < NE.cnt) : penumPtK 1755 11 (mask 11) (1755 * 11) false NE.G NE.GI
    NE.k NE.cnt NE.T NE.PL NE.POS NE.SRT NE.SRI i = true := by
  have e : NE.cnt = 2400 := rfl
  have sl : ∀ lo, lo < 24 → penumSlK 1755 11 (mask 11) (1755 * 11) false NE.G NE.GI NE.k NE.cnt
      NE.T NE.PL NE.POS NE.SRT NE.SRI (100 * lo) 100 = true := by
    intro lo hlo
    interval_cases lo
    exacts [n_sl0, n_sl100, n_sl200, n_sl300, n_sl400, n_sl500, n_sl600, n_sl700, n_sl800,
      n_sl900, n_sl1000, n_sl1100, n_sl1200, n_sl1300, n_sl1400, n_sl1500, n_sl1600, n_sl1700,
      n_sl1800, n_sl1900, n_sl2000, n_sl2100, n_sl2200, n_sl2300]
  exact penumSl_spec (sl (i / 100) (by omega)) i (by omega) (by omega) hi

theorem rep_all : ∀ q < 5, allN 3 (fun d => repK 1755 11 6 66 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add (Nat.add 1 (Nat.mul 3 q)) d)) = true := by
  intro q hq
  interval_cases q
  exacts [rep_t0, rep_t1, rep_t2, rep_t3, rep_t4]

theorem hyps : Hyps titsAData KA := by
  constructor
  case hn => exact szOK1755
  case hDn => exact rfl
  case hGs => exact rfl
  case hGb => exact gTA_bind.2
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
  case hNp => exact fun i hi => n_pt hi
  case hNc => exact rfl
  case hNI => exact fun j hj => (PK.allN_iff.1 k_ngi) j hj
  case hNorm => exact fun j hj i hi => band_e ((PK.allN_iff.1 ((PK.allN_iff.1 k_norm) j hj)) i hi)
  case hMj => exact (by decide : 0 < 6)
  case hMi => exact (by decide : 0 < 2)
  case hMv =>
    dsimp only [KA]
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
    have h := (PK.allN_iff.1 (rep_all ((i - 1) / 3) (by change i < 16 at hi; omega)))
      ((i - 1) % 3) (by omega)
    have e : Nat.add (Nat.add 1 (Nat.mul 3 ((i - 1) / 3))) ((i - 1) % 3) = i := by
      change 1 + 3 * ((i - 1) / 3) + (i - 1) % 3 = i
      omega
    rw [e] at h
    exact h
  case hCnt =>
    intro i h0 hi
    have h := (PK.allN_iff.1 k_cnt) (i - 1) (by change i < 16 at hi; omega)
    have e : Nat.succ (i - 1) = i := by omega
    rw [e] at h
    exact Nat.eq_of_beq_eq_true h
  case hSum => exact Nat.eq_of_beq_eq_true k_sum
  case hL => exact k_lab
  case hM => exact (by decide : 1755 ≤ 64 * 28)
  case hMK => exact fun i hi => Nat.eq_of_beq_eq_true ((PK.allN_iff.1 k_mk) i hi)
  case hMd =>
    intro i hi j hj hij
    refine Or.inl fun e => ?_
    have h := bnot_e (bif_t (Nat.blt_eq.mpr hij) ((PK.allN_iff.1 ((PK.allN_iff.1 k_mkd) i hi)) j hj))
    change (rg 512 (mask 512) MK 0 i).beq (rg 512 (mask 512) MK 0 j) = false at h
    change rg 512 (mask 512) MK 0 i = rg 512 (mask 512) MK 0 j at e
    rw [e, Nat.beq_refl] at h
    exact absurd h (by decide)
  case hGl => exact rfl
  case hGen =>
    exact fun i hi => ⟨Nat.eq_of_beq_eq_true (band_e ((PK.allN_iff.1 k_gen) i hi)).1,
      fun j hj => (PK.allN_iff.1 (band_e ((PK.allN_iff.1 k_gen) i hi)).2) j hj⟩

theorem titsA_check : check titsAData = true := check_of hyps

end CertificateChecks.KernelMaxD2.TitsA

end
