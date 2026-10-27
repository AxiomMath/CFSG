module

public import Certificates.Data.Fi24Rank.KCheck
import Certificates.Kernel.Fi24Rk.Checks
import Certificates.Kernel.Fi24Rk.ChecksStab
import Certificates.Kernel.Sporadic.Fi24K.C2077
import CFSG.Certificates.Kernel.Fi22Rk.PbChecksN
import CFSG.Certificates.Kernel.Fi22Rk.Uniq
import CFSG.Certificates.Kernel.Spor.HexNumsSound
import CFSG.Certificates.Kernel.Spor.RawSound
import Certificates.Kernel.Sporadic.ON.Gen
import Mathlib.Tactic.IntervalCases
import CFSG.Sporadic.FischerOddCore.LabelSpec

#kon_join CertificateChecks.KernelFi24Rk.K.lay0All CertificateChecks.KernelFi24Rk.K.lay0 16
#kon_join CertificateChecks.KernelFi24Rk.K.conj0All CertificateChecks.KernelFi24Rk.K.conj0 16
#kon_join CertificateChecks.KernelFi24Rk.K.conj1All CertificateChecks.KernelFi24Rk.K.conj1 16
#kon_join CertificateChecks.KernelFi24Rk.K.stabAll CertificateChecks.KernelFi24Rk.K.stab 8
#kon_join CertificateChecks.KernelFi24Rk.K.uniqAll CertificateChecks.KernelFi24Rk.K.uniq 8

namespace CertificateChecks.KernelFi24Rk.A

open CFSG.KC.Enum CFSG.KC.Fi22Rk CFSG.KC.Fi22RkS CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative
open CFSG.Sporadic.FischerOddCore (fi24KStrong fi24KBase)
open CertificateChecks.KernelFi24Rk CertificateChecks.KernelLC CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Fi24C (kS bindsK permK)

theorem chunk {m : Nat} {f : Nat → Bool} {g : Nat → Bool} (hm : 0 < m)
    (hg : ∀ c, g c = allN m fun r => f (Nat.add (Nat.mul m c) r)) {K : Nat}
    (h : ∀ c < K, g c = true) : ∀ i < K * m, f i = true := by
  intro i hi
  have hc : i / m < K := by
    rw [Nat.div_lt_iff_lt_mul hm]
    exact hi
  have a := allN_spec ((hg _).symm.trans (h _ hc)) (i % m) (Nat.mod_lt _ hm)
  have e : Nat.add (Nat.mul m (i / m)) (i % m) = i := by
    simp only [Nat.add_eq, Nat.mul_eq]
    exact Nat.div_add_mod i m
  rwa [e] at a

theorem bIf_lt {a n : Nat} {b : Bool} (h : bIf(Nat.blt a n, b, true) = true) (ha : a < n) :
    b = true := by
  rwa [Nat.blt_eq.mpr ha] at h

theorem szA : szOK 504 9 = true := by decide
theorem szM : szOK 243 8 = true := by decide

theorem rowsA_facts : (rowsOf 504 (unpack (504 * 5) 9 Fi24PlT.A.F)).size = 5 ∧
    ∀ k < 5, (rowsOf 504 (unpack (504 * 5) 9 Fi24PlT.A.F))[k]! = unpack 504 9 (D.AK k) ∧
      PP 504 9 (D.AK k) := rows_of (by decide) szA K.rowsA
theorem rowsG_facts : (rowsOf 504 (unpack (504 * 2) 9 T.G.F)).size = 2 ∧
    ∀ k < 2, (rowsOf 504 (unpack (504 * 2) 9 T.G.F))[k]! = unpack 504 9 (D.GK k) ∧
      PP 504 9 (D.GK k) := rows_of (by decide) szA K.rowsG
theorem rowsM_facts : (rowsOf 243 (unpack (243 * 2) 8 T.M.F)).size = 2 ∧
    ∀ k < 2, (rowsOf 243 (unpack (243 * 2) 8 T.M.F))[k]! = unpack 243 8 (D.MUK k) ∧
      PP 243 8 (D.MUK k) := rows_of (by decide) szM K.rowsM

theorem hexNums_same (d : Nat) (s : String) :
    hexNums d s = CFSG.Sporadic.FischerOddCore.hexNums d s := rfl

theorem ra_eq : kRA () = rowsOf 504 (unpack (504 * 5) 9 Fi24PlT.A.F) := by
  unfold kRA
  rw [hexNums_same, CFSG.KS.HexNums.hexNums_of Fi24PlT.A.eq Fi24PlT.A.ok]

theorem rg_eq : kRG () = rowsOf 504 (unpack (504 * 2) 9 T.G.F) := by
  unfold kRG
  rw [hexNums_same, CFSG.KS.HexNums.hexNums_of T.G.eq T.G.ok]

theorem rm_eq : kRMu () = rowsOf 243 (unpack (243 * 2) 8 T.M.F) := by
  unfold kRMu
  rw [hexNums_same, CFSG.KS.HexNums.hexNums_of T.M.eq T.M.ok]

theorem A_size : (kRA ()).size = 5 := by
  rw [ra_eq]
  exact rowsA_facts.1

theorem G_size : (kRG ()).size = 2 := by
  rw [rg_eq]
  exact rowsG_facts.1

theorem M_size : (kRMu ()).size = 2 := by
  rw [rm_eq]
  exact rowsM_facts.1

theorem A_get {k : Nat} (hk : k < 5) : (kRA ())[k]! = unpack 504 9 (D.AK k) ∧
    PP 504 9 (D.AK k) := by
  rw [ra_eq]
  exact rowsA_facts.2 k hk

theorem G_get {l : Nat} (hl : l < 2) : (kRG ())[l]! = unpack 504 9 (D.GK l) ∧
    PP 504 9 (D.GK l) := by
  rw [rg_eq]
  exact rowsG_facts.2 l hl

theorem M_get {l : Nat} (hl : l < 2) : (kRMu ())[l]! = unpack 243 8 (D.MUK l) ∧
    PP 243 8 (D.MUK l) := by
  rw [rm_eq]
  exact rowsM_facts.2 l hl

theorem lay0_all : ∀ i < 243, D.IK i = pc 504 9 (D.PW (i % 3)) (D.J1 (i / 3)) := by
  intro i hi
  have h := chunk (m := 16) (K := 16) (f := fun i => bIf(Nat.blt i (nat_lit 243), Nat.beq (D.IK i)
      (pc 504 9 (D.PW (Nat.mod i (nat_lit 3))) (D.J1 (Nat.div i (nat_lit 3)))), true))
    (g := K.lay0) (by decide) (fun c => by
      unfold K.lay0
      congr 1
      funext r
      rw [CFSG.KC.Fi22RkS.strictB_eq]) K.lay0All i (by omega)
  exact Nat.eq_of_beq_eq_true (bIf_lt h hi)

theorem iota_get {i : Nat} (hi : i < 243) :
    (iotas 504 (kRA ()))[i]! = unpack 504 9 (D.IK i) ∧
      canonK 504 9 (mask 9) (504 * 9) (D.IK i) = true := by
  have e : (iotas 504 (kRA ()))[i]! = iotaA 504 (kRA ()) i := by
    unfold iotas
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  rw [e]
  exact iotaA_of szA (fun k hk => (A_get hk).1) (fun k hk => (A_get hk).2.1) K.pow K.lay3 K.lay2
    K.lay1 lay0_all hi

theorem iota_pt {i x : Nat} (hi : i < 243) (hx : x < 504) :
    ((iotas 504 (kRA ()))[i]!)[x]! = pg 9 (mask 9) (D.IK i) x := by
  rw [(iota_get hi).1, get_unpack hx]

theorem iota_lt {i x : Nat} (hi : i < 243) (hx : x < 504) : pg 9 (mask 9) (D.IK i) x < 504 := by
  have h := (iota_get hi).2
  unfold canonK at h
  simp only [bAnd_iff] at h
  exact Nat.blt_eq.mp (allN_spec h.2.2 x hx)

theorem mus_facts : ∀ l < 2, (kRMu ())[l]! = unpack 243 8 (D.MUK l) := fun l hl =>
  (M_get hl).1

theorem musc : ∀ l < 2, canonK 243 8 (mask 8) (243 * 8) (D.MUK l) = true := fun l hl =>
  (M_get hl).2.1

theorem side : sideOK 504 (kRA ()) (kRG ()) (kRMu ()) kRP0 9 = true := by
  unfold sideOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨permsOK_of A_size G_size M_size (fun k hk => A_get hk) (fun l hl => G_get hl)
    (fun l hl => M_get hl), by decide⟩, multOK_of szA (fun k hk => (A_get hk).1)
    (fun k hk => (A_get hk).2.1) K.mult⟩, injOK_of (by decide) (fun i hi => (iota_get hi).1)
    K.inj⟩, conjOK_of szA (fun i hi => iota_get hi) (fun l hl => G_get hl) mus_facts
    (fun l hl c hc => ?_)⟩, pbOK_ofN M_size mus_facts musc K.run K.tree K.mt (by decide)
    (by decide)⟩, fixOK_ofN M_size mus_facts musc K.run K.tree K.mt (by decide) (by decide)
    (fun k hk => allN_spec K.fix k hk)⟩
  interval_cases l
  · exact K.conj0All c hc
  · exact K.conj1All c hc

theorem S_get {k : Nat} (hk : k < 7) :
    (kRA () ++ kRG ())[k]! = unpack 504 9 (K.SK k) ∧ PP 504 9 (K.SK k) := by
  have hs : (kRA () ++ kRG ()).size = 7 := by rw [Array.size_append, A_size, G_size]
  have hk' : k < (kRA () ++ kRG ()).size := by
    rw [hs]
    exact hk
  rw [getElem!_pos _ k hk']
  by_cases h5 : k < 5
  · have h5' : k < (kRA ()).size := by
      rw [A_size]
      exact h5
    rw [Array.getElem_append_left h5', ← getElem!_pos (kRA ()) k h5']
    have e : K.SK k = D.AK k := by
      unfold K.SK
      rw [Nat.blt_eq.mpr h5]
    rw [e]
    exact A_get h5
  · have h5' : (kRA ()).size ≤ k := by
      rw [A_size]
      omega
    have h6 : k - (kRA ()).size < (kRG ()).size := by
      rw [A_size, G_size]
      omega
    rw [Array.getElem_append_right h5', ← getElem!_pos (kRG ()) _ h6, A_size]
    have e : K.SK k = D.GK (k - 5) := by
      unfold K.SK
      rw [show Nat.blt k 5 = false from by
        cases h : Nat.blt k 5
        · rfl
        · exact absurd (Nat.blt_eq.mp h) h5]
      rfl
    rw [e]
    exact G_get (by omega)

theorem mem_ok : kMemOK () = true := by
  unfold kMemOK
  rw [allLt_iff]
  intro k hk
  obtain ⟨e, hp⟩ := S_get hk
  rw [e, kS]
  exact siftK_sound bindsK permK Fi24KC.hl rfl (range_of_canonK hp.1) (allN_spec K.sift k hk)

theorem stab_all : ∀ q < 504, stabAt 9 D.IK D.SMK q = true := by
  intro q hq
  have h := chunk (m := 64) (K := 8) (f := fun q => bIf(Nat.blt q (nat_lit 504),
      stabAt 9 D.IK D.SMK q, true)) (g := K.stab) (by decide) (fun c => by
      unfold K.stab
      congr 1
      funext r
      rw [CFSG.KC.Fi22RkS.strictB_eq]) K.stabAll q (by omega)
  exact bIf_lt h hq

theorem uniq_all : ∀ q < 504, uniqAtK 9 D.IK D.CLK D.POK D.STK D.WK q = true := by
  intro q hq
  have h := chunk (m := 64) (K := 8) (f := fun q => bIf(Nat.blt q (nat_lit 504),
      uniqAtK 9 D.IK D.CLK D.POK D.STK D.WK q, true)) (g := K.uniq) (by decide) (fun c => by
      unfold K.uniq
      congr 1
      funext r
      rw [CFSG.KC.Fi22RkS.strictB_eq]) K.uniqAll q (by omega)
  exact bIf_lt h hq

theorem uniq_ok : kUniqOK () = true := by
  unfold kUniqOK
  rw [allLt_iff]
  intro q hq
  exact uniqAt_of (fun i hi x hx => iota_pt hi hx) (fun i hi x hx => iota_lt hi hx) stab_all
    K.cls K.blk hq (uniq_all q hq)

end CertificateChecks.KernelFi24Rk.A

public section

namespace CertificateChecks.KernelFi24Rk.A

open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative

theorem rank : kRankOK () = true := by
  unfold kRankOK
  simp only [Bool.and_eq_true]
  exact ⟨⟨side, mem_ok⟩, uniq_ok⟩

end CertificateChecks.KernelFi24Rk.A

end
