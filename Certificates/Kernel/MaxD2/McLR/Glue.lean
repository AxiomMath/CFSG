module

public import Certificates.Kernel.MaxD2.McLR.Checks
public import Certificates.Kernel.MaxD2.McLR.Tests
public import Certificates.Kernel.MaxD2.McLR.N0
public import Certificates.Kernel.MaxD2.McLR.N1
public import Certificates.Kernel.MaxD2.McLR.N2
public import CFSG.Certificates.Kernel.MaxD2.Count
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.McLR

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open Certificates.MaxD2Perm Certificates.MaxD2Heis

@[expose] noncomputable def KM : Pk where
  n := 275
  w := 9
  kG := 3
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
  TP := 0
  TPI := 0
  th := 0
  CH := fun _ => 0
  NH := fun _ => 0
  L := fun _ => 0
  hi := 0
  cw := 0
  nl := 0
  MK := fun _ => 0
  mj := 0
  mi := 0

theorem gT_bind : ∀ k < 3, mclFiveDataR.gT[k]! = unpack 275 9 (GP k) := by
  intro k hk
  interval_cases k <;> decide +kernel

theorem n_pt {i : Nat} (hi : i < NE.cnt) : penumPtK 275 9 (mask 9) (275 * 9) false NE.G NE.GI
    NE.k NE.cnt NE.T NE.PL NE.POS NE.SRT NE.SRI i = true := by
  have e : NE.cnt = 6000 := rfl
  have sl : ∀ lo, lo < 12 → penumSlK 275 9 (mask 9) (275 * 9) false NE.G NE.GI NE.k NE.cnt
      NE.T NE.PL NE.POS NE.SRT NE.SRI (500 * lo) 500 = true := by
    intro lo hlo
    interval_cases lo
    exacts [n_sl0, n_sl500, n_sl1000, n_sl1500, n_sl2000, n_sl2500, n_sl3000, n_sl3500, n_sl4000,
      n_sl4500, n_sl5000, n_sl5500]
  exact penumSl_spec (sl (i / 500) (by omega)) i (by omega) (by omega) hi

theorem rep_all : ∀ q < 4, repsK q = true := by
  intro q hq
  interval_cases q
  exacts [rep_t0, rep_t1, rep_t2, rep_t3]

theorem hypsC : HypsC mclFiveDataR KM where
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
    have hi' : i < 69 := hi
    have h := (PK.allN_iff.1 (rep_all ((i - 1) / 17) (by omega))) ((i - 1) % 17) (by omega)
    have e : Nat.add (Nat.add 1 (Nat.mul 17 ((i - 1) / 17))) ((i - 1) % 17) = i := by
      change 1 + 17 * ((i - 1) / 17) + (i - 1) % 17 = i
      omega
    rw [e] at h
    exact h
  hCnt := by
    intro i h0 hi
    have hi' : i < 69 := hi
    have h := (PK.allN_iff.1 k_cnt) (i - 1) (by omega)
    have e : Nat.succ (i - 1) = i := by omega
    rw [e] at h
    exact Nat.eq_of_beq_eq_true h

theorem mcl_ti : Certificates.MaxD2TI.checkTI mclFiveDataR = true := by
  refine c_checkTI_of hypsC fun i h0 hi => ?_
  have hi' : i < 69 := hi
  have h := (PK.allN_iff.1 k_ti) (i - 1) (by omega)
  have e : Nat.succ (i - 1) = i := by omega
  rw [e] at h
  intro hm
  change Nat.mod (r32 CN i) 5 = 0 at hm
  rw [hm] at h
  exact absurd h (by decide)

end CertificateChecks.KernelMaxD2.McLR

end
