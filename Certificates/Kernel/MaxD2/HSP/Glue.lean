module

public import Certificates.Kernel.MaxD2.HSP.Checks
public import Certificates.Kernel.MaxD2.HSP.Tests
public import Certificates.Kernel.MaxD2.HSP.Pairs
public import Certificates.Kernel.MaxD2.HSP.Closed
public import Certificates.Kernel.MaxD2.HSP.N0
public import CFSG.Certificates.Kernel.MaxD2.Count
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.HSP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open Certificates.MaxD2Perm Certificates.HSOver

@[expose] noncomputable def KP : Pk where
  n := 100
  w := 7
  kG := 2
  Gp := GP
  GIp := GPI
  rcnt := 0
  RG := fun _ => 0
  RGI := fun _ => 0
  RT := fun _ => 0
  RPL := fun _ => 0
  RPOS := fun _ => 0
  RSRT := fun _ => 0
  RSRI := fun _ => 0
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
  nr := 20
  REP := REP
  REPI := REPI
  np := 3
  kw := 21
  PT := r32 PT
  FS := FS
  KS := KS
  RB := RB
  H := H
  CN := r32 CN
  TP := 0
  TPI := 0
  th := 0
  CH := fun _ => 0
  NH := fun _ => 0
  L := fun _ => 0
  hi := 2
  cw := 7
  nl := 1
  MK := fun i => mkeyK 100 7 2 7 1 (fun _ => 0) (REP i)
  mj := 0
  mi := 0
  RB2 := RB2
  H2 := H2
  PQ := fun i j => Nat.add (Nat.div (Nat.mul j (Nat.sub j 1)) 2) i

theorem gT_bind : ∀ k < 2, hsOverDataP.gT[k]! = unpack 100 7 (GP k) := by
  intro k hk
  interval_cases k <;> decide +kernel

theorem n_pt {i : Nat} (hi : i < NE.cnt) : penumPtK 100 7 (mask 7) (100 * 7) false NE.G NE.GI
    NE.k NE.cnt NE.T NE.PL NE.POS NE.SRT NE.SRI i = true := by
  have e : NE.cnt = 2000 := rfl
  have sl : ∀ lo, lo < 2 → penumSlK 100 7 (mask 7) (100 * 7) false NE.G NE.GI NE.k NE.cnt
      NE.T NE.PL NE.POS NE.SRT NE.SRI (1000 * lo) 1000 = true := by
    intro lo hlo
    interval_cases lo
    exacts [n_sl0, n_sl1000]
  exact penumSl_spec (sl (i / 1000) (by omega)) i (by omega) (by omega) hi

theorem pair_all {i j : Nat} (hij : i < j) (hj : j < 20) :
    pairK 100 7 3 21 NE.cnt (r32 PT) NE.T FS KS REP REPI RB2 H2
      (Nat.add (Nat.div (Nat.mul j (Nat.sub j 1)) 2) i) i j = true := by
  have hp : ∀ lo m, pairsK lo m = true → lo ≤ j → j < lo + m →
      pairK 100 7 3 21 NE.cnt (r32 PT) NE.T FS KS REP REPI RB2 H2
        (Nat.add (Nat.div (Nat.mul j (Nat.sub j 1)) 2) i) i j = true := by
    intro lo m h hl hm
    have h1 := (PK.allN_iff.1 h) (j - lo) (by omega)
    have e : Nat.add lo (j - lo) = j := by
      change lo + (j - lo) = j
      omega
    rw [e] at h1
    exact (PK.allN_iff.1 h1) i hij
  by_cases h1 : j < 10
  · exact hp 1 9 k_pair0 (by omega) (by omega)
  · by_cases h2 : j < 14
    · exact hp 10 4 k_pair1 (by omega) (by omega)
    · by_cases h3 : j < 17
      · exact hp 14 3 k_pair2 (by omega) (by omega)
      · exact hp 17 3 k_pair3 (by omega) (by omega)

theorem hypsC : HypsC hsOverDataP KP := by
  constructor
  case hn => exact k_sz
  case hDn => exact rfl
  case hGs => exact rfl
  case hGb => exact gT_bind
  case hGp => exact k_gp
  case hNk => exact rfl
  case hNG => exact fun j hj => band_e ((PK.allN_iff.1 k_ng) j hj)
  case hNh => exact k_nh
  case hNp => exact fun i hi => n_pt hi
  case hNc => exact rfl
  case hNI => exact fun j hj => (PK.allN_iff.1 k_ngi) j hj
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
    have hi' : i < 20 := hi
    by_cases h8 : i < 8
    · have h := (PK.allN_iff.1 rep_t0) (i - 1) (by omega)
      have e : Nat.add 1 (i - 1) = i := by
        change 1 + (i - 1) = i
        omega
      rw [e] at h
      exact h
    · by_cases h14 : i < 14
      · have h := (PK.allN_iff.1 rep_t1) (i - 8) (by omega)
        have e : Nat.add 8 (i - 8) = i := by
          change 8 + (i - 8) = i
          omega
        rw [e] at h
        exact h
      · have h := (PK.allN_iff.1 rep_t2) (i - 14) (by omega)
        have e : Nat.add 14 (i - 14) = i := by
          change 14 + (i - 14) = i
          omega
        rw [e] at h
        exact h
  case hCnt =>
    intro i h0 hi
    have hi' : i < 20 := hi
    have h := (PK.allN_iff.1 k_cnt) (i - 1) (by omega)
    have e : Nat.succ (i - 1) = i := by omega
    rw [e] at h
    exact Nat.eq_of_beq_eq_true h

theorem hypsB : HypsB hsOverDataP KP := by
  refine ⟨hypsC, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.eq_of_beq_eq_true k_sum
  · exact k_lab
  · exact (by decide : 100 ≤ 64 * 2)
  · intro i _
    dsimp only [KP]
  · intro i hi j hj hij
    exact Or.inr (pair_all hij hj)

theorem hypsO : HypsO hsOverDataP KP hsOverPairW := by
  refine ⟨hypsB, rfl, fun i hi => ?_, Nat.eq_of_beq_eq_true k_pl, fun j hj => ?_⟩
  · have h := band_e ((PK.allN_iff.1 k_gen) i hi)
    exact ⟨Nat.eq_of_beq_eq_true h.1, fun j hj => (PK.allN_iff.1 h.2) j hj⟩
  · have h := (PK.allN_iff.1 k_pw) j hj
    exact h

theorem hsOverP_over : Certificates.OverD2Perm.checkOver hsOverDataP hsOverPairW = true :=
  c_checkOver_of hypsO

theorem hsOverP_closed : Certificates.OverD2Perm.checkClosedPair hsOverDataP 16 = true := by
  have h1 : KP.CN 1 = 16 := Nat.eq_of_beq_eq_true k_c16a
  have h2 : KP.CN 2 = 16 := Nat.eq_of_beq_eq_true k_c16b
  exact c_checkClosedPair_of hypsB (by decide) h1 h2 (fun k hk => (PK.allN_iff.1 k_clos1) k hk)
    (fun k hk => (PK.allN_iff.1 k_clos2) k hk)

end CertificateChecks.KernelMaxD2.HSP

end
