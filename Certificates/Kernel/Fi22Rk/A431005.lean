module

public import Certificates.Data.Fi24Rank.Fi22Check
import Certificates.Kernel.Fi22Rk.Checks
import Certificates.Kernel.Fi22Rk.ChecksConj
import Certificates.Kernel.Fi22Rk.ChecksStab
import Certificates.Kernel.Fi22Rk.ChecksTau
import Certificates.Kernel.Fi22Nfp.Final
import Certificates.Kernel.Fi22Core.OrbData
import Certificates.Kernel.Fi22Cent.Final
import CFSG.Certificates.Kernel.Fi22Rk.Uniq
import CFSG.Certificates.Kernel.Spor.HexNumsSound
import CFSG.Certificates.Kernel.Spor.RawOrbGrp
import Certificates.Kernel.Sporadic.ON.Gen
import Mathlib.Tactic.IntervalCases
import CFSG.Sporadic.FischerOddCore.LabelSpec

#kon_join CertificateChecks.KernelFi22Rk.K.lay0All CertificateChecks.KernelFi22Rk.K.lay0 16
#kon_join CertificateChecks.KernelFi22Rk.K.mtcAll CertificateChecks.KernelFi22Rk.K.mtc 9
#kon_join CertificateChecks.KernelFi22Rk.K.fixcAll CertificateChecks.KernelFi22Rk.K.fixc 9
#kon_join CertificateChecks.KernelFi22Rk.K.conj0All CertificateChecks.KernelFi22Rk.K.conj0 16
#kon_join CertificateChecks.KernelFi22Rk.K.conj1All CertificateChecks.KernelFi22Rk.K.conj1 16
#kon_join CertificateChecks.KernelFi22Rk.K.stabAll CertificateChecks.KernelFi22Rk.K.stab 55
#kon_join CertificateChecks.KernelFi22Rk.K.uniqAll CertificateChecks.KernelFi22Rk.K.uniq 55
#kon_join CertificateChecks.KernelFi22Rk.K.tauAll CertificateChecks.KernelFi22Rk.K.tau 42
#kon_join CertificateChecks.KernelFi22Rk.K.chainAll CertificateChecks.KernelFi22Rk.K.chain 55

namespace CertificateChecks.KernelFi22Rk.A

open CFSG.KC.Enum CFSG.KC.Fi22Rk CFSG.KC.Fi22RkS CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative
open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.KS.Fi22Cent
open CertificateChecks.KernelFi22Rk
open CFSG.KLie.CT (orB notB)

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

theorem szA : szOK 3510 12 = true := by decide
theorem szM : szOK 243 8 = true := by decide

theorem rowsA_facts : (rowsOf 3510 (unpack (3510 * 5) 12 T.A.F)).size = 5 ∧
    ∀ k < 5, (rowsOf 3510 (unpack (3510 * 5) 12 T.A.F))[k]! = unpack 3510 12 (D.AK k) ∧
      PP 3510 12 (D.AK k) := rows_of (by decide) szA K.rowsA
theorem rowsG_facts : (rowsOf 3510 (unpack (3510 * 2) 12 T.G.F)).size = 2 ∧
    ∀ k < 2, (rowsOf 3510 (unpack (3510 * 2) 12 T.G.F))[k]! = unpack 3510 12 (D.GK k) ∧
      PP 3510 12 (D.GK k) := rows_of (by decide) szA K.rowsG
theorem rowsM_facts : (rowsOf 243 (unpack (243 * 2) 8 T.M.F)).size = 2 ∧
    ∀ k < 2, (rowsOf 243 (unpack (243 * 2) 8 T.M.F))[k]! = unpack 243 8 (D.MUK k) ∧
      PP 243 8 (D.MUK k) := rows_of (by decide) szM K.rowsM

theorem hexNums_same (d : Nat) (s : String) :
    hexNums d s = CFSG.Sporadic.FischerOddCore.hexNums d s := rfl

theorem ra_eq : fi22RA () = rowsOf 3510 (unpack (3510 * 5) 12 T.A.F) := by
  unfold fi22RA
  rw [hexNums_same, CFSG.KS.HexNums.hexNums_of T.A.eq T.A.ok]

theorem rg_eq : fi22RG () = rowsOf 3510 (unpack (3510 * 2) 12 T.G.F) := by
  unfold fi22RG
  rw [hexNums_same, CFSG.KS.HexNums.hexNums_of T.G.eq T.G.ok]

theorem rm_eq : fi22RMu () = rowsOf 243 (unpack (243 * 2) 8 T.M.F) := by
  unfold fi22RMu
  rw [hexNums_same, CFSG.KS.HexNums.hexNums_of T.M.eq T.M.ok]

theorem rc_eq : fi22RChain () = unpack 1458 12 T.C.F := by
  unfold fi22RChain
  rw [hexNums_same, CFSG.KS.HexNums.hexNums_of T.C.eq T.C.ok]

theorem A_size : (fi22RA ()).size = 5 := by rw [ra_eq]; exact rowsA_facts.1
theorem G_size : (fi22RG ()).size = 2 := by rw [rg_eq]; exact rowsG_facts.1
theorem M_size : (fi22RMu ()).size = 2 := by rw [rm_eq]; exact rowsM_facts.1

theorem A_get {k : Nat} (hk : k < 5) : (fi22RA ())[k]! = unpack 3510 12 (D.AK k) ∧
    PP 3510 12 (D.AK k) := by
  rw [ra_eq]
  exact rowsA_facts.2 k hk

theorem G_get {l : Nat} (hl : l < 2) : (fi22RG ())[l]! = unpack 3510 12 (D.GK l) ∧
    PP 3510 12 (D.GK l) := by
  rw [rg_eq]
  exact rowsG_facts.2 l hl

theorem M_get {l : Nat} (hl : l < 2) : (fi22RMu ())[l]! = unpack 243 8 (D.MUK l) ∧
    PP 243 8 (D.MUK l) := by
  rw [rm_eq]
  exact rowsM_facts.2 l hl

theorem lay0_all : ∀ i < 243, D.IK i = pc 3510 12 (D.PW (i % 3)) (D.J1 (i / 3)) := by
  intro i hi
  have h := chunk (m := 16) (K := 16) (f := fun i => bIf(Nat.blt i (nat_lit 243), Nat.beq (D.IK i)
      (pc 3510 12 (D.PW (Nat.mod i (nat_lit 3))) (D.J1 (Nat.div i (nat_lit 3)))), true))
    (g := K.lay0) (by decide) (fun c => by
      unfold K.lay0
      congr 1
      funext r
      rw [CFSG.KC.Fi22RkS.strictB_eq]) K.lay0All i (by omega)
  exact Nat.eq_of_beq_eq_true (bIf_lt h hi)

theorem iota_get {i : Nat} (hi : i < 243) :
    (iotas 3510 (fi22RA ()))[i]! = unpack 3510 12 (D.IK i) ∧
      canonK 3510 12 (mask 12) (3510 * 12) (D.IK i) = true := by
  have e : (iotas 3510 (fi22RA ()))[i]! = iotaA 3510 (fi22RA ()) i := by
    unfold iotas
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  rw [e]
  exact iotaA_of szA (fun k hk => (A_get hk).1) (fun k hk => (A_get hk).2.1) K.pow K.lay3 K.lay2
    K.lay1 lay0_all hi

theorem iota_pt {i x : Nat} (hi : i < 243) (hx : x < 3510) :
    ((iotas 3510 (fi22RA ()))[i]!)[x]! = pg 12 (mask 12) (D.IK i) x := by
  rw [(iota_get hi).1, get_unpack hx]

theorem iota_lt {i x : Nat} (hi : i < 243) (hx : x < 3510) : pg 12 (mask 12) (D.IK i) x < 3510 := by
  have h := (iota_get hi).2
  unfold canonK at h
  simp only [bAnd_iff] at h
  exact Nat.blt_eq.mp (allN_spec h.2.2 x hx)

theorem mt_all : ∀ c < 9, mtC D.LK D.MTK c = true := fun c hc => K.mtcAll c hc

theorem mus_facts : ∀ l < 2, (fi22RMu ())[l]! = unpack 243 8 (D.MUK l) := fun l hl =>
  (M_get hl).1

theorem musc : ∀ l < 2, canonK 243 8 (mask 8) (243 * 8) (D.MUK l) = true := fun l hl =>
  (M_get hl).2.1

theorem side : sideOK 3510 (fi22RA ()) (fi22RG ()) (fi22RMu ()) fi22RP0 81 = true := by
  unfold sideOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨permsOK_of A_size G_size M_size (fun k hk => A_get hk) (fun l hl => G_get hl)
    (fun l hl => M_get hl), by decide⟩, multOK_of szA (fun k hk => (A_get hk).1)
    (fun k hk => (A_get hk).2.1) K.mult⟩, injOK_of (by decide) (fun i hi => (iota_get hi).1)
    K.inj⟩, conjOK_of szA (fun i hi => iota_get hi) (fun l hl => G_get hl) mus_facts
    (fun l hl c hc => ?_)⟩, pbOK_of M_size mus_facts musc K.run K.tree mt_all⟩,
    fixOK_of M_size mus_facts musc K.run K.tree mt_all (fun c hc => K.fixcAll c hc)⟩
  interval_cases l
  · exact K.conj0All c hc
  · exact K.conj1All c hc

theorem nonab : nonabOK (fi22RMu ()) 81 = true :=
  nonabOK_of M_size mus_facts musc K.run K.tree mt_all K.nonab

theorem S_get {k : Nat} (hk : k < 7) :
    (fi22RA () ++ fi22RG ())[k]! = unpack 3510 12 (K.SK k) ∧ PP 3510 12 (K.SK k) := by
  have hs : (fi22RA () ++ fi22RG ()).size = 7 := by rw [Array.size_append, A_size, G_size]
  have hk' : k < (fi22RA () ++ fi22RG ()).size := by rw [hs]; exact hk
  rw [getElem!_pos _ k hk']
  by_cases h5 : k < 5
  · have h5' : k < (fi22RA ()).size := by rw [A_size]; exact h5
    rw [Array.getElem_append_left h5', ← getElem!_pos (fi22RA ()) k h5']
    have e : K.SK k = D.AK k := by
      unfold K.SK
      rw [Nat.blt_eq.mpr h5]
    rw [e]
    exact A_get h5
  · have h5' : (fi22RA ()).size ≤ k := by rw [A_size]; omega
    have h6 : k - (fi22RA ()).size < (fi22RG ()).size := by rw [A_size, G_size]; omega
    rw [Array.getElem_append_right h5', ← getElem!_pos (fi22RG ()) _ h6, A_size]
    have e : K.SK k = D.GK (k - 5) := by
      unfold K.SK
      rw [show Nat.blt k 5 = false from by
        cases h : Nat.blt k 5
        · rfl
        · exact absurd (Nat.blt_eq.mp h) h5]
      rfl
    rw [e]
    exact G_get (by omega)

theorem nb_eq {j : Nat} (hj : j < 6) : nfpBase[j]! = K.NB j := by
  interval_cases j <;> rfl

theorem ap_tab {c x : Nat} (hc : c < 3510) (hx : x < 3510) :
    ap (tabOf (orbitData ()) c) x = cK c x := by
  rw [CertificateChecks.KernelFi22C.orbitData_eq]
  exact CertificateChecks.KernelFi22N.tabOf_ap hc hx

theorem tau_ok : fi22TauOK () = true := by
  unfold fi22TauOK
  rw [allLt_iff]
  intro k hk
  rw [allLt_iff]
  intro j hj
  obtain ⟨hS, hP⟩ := S_get hk
  have h := K.tauAll (6 * k + j) (by change 6 * k + j < 42; omega)
  unfold K.tau at h
  have ed : Nat.div (6 * k + j) 6 = k := by
    change (6 * k + j) / 6 = k
    omega
  have em : Nat.mod (6 * k + j) 6 = j := by
    change (6 * k + j) % 6 = j
    omega
  rw [ed, em] at h
  unfold tauAt at h
  rw [CFSG.KC.Fi22RkS.strictB_eq, CFSG.KC.Fi22RkS.strictB_eq] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hv := Nat.blt_eq.mp h1
  have hb : K.NB j < 3510 := by interval_cases j <;> decide
  have hri : ∀ x < 3510, pg 12 (mask 12) (pinvS 3510 12 (mask 12) (K.SK k)) x < 3510 := by
    intro x hx
    have c := (PP.inv hP).1
    unfold canonK at c
    simp only [bAnd_iff] at c
    exact Nat.blt_eq.mp (allN_spec c.2.2 x hx)
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [nb_eq hj, hS, get_unpack hb]
  refine ⟨hv, ?_⟩
  rw [allLt_iff]
  intro x hx
  rw [invCand_PP hP, get_unpack hx, ap_tab hb (hri x hx),
    get_unpack (CertificateChecks.KernelFi22Cent.cK_lt _ (hri x hx)), ap_tab hv hx]
  have := allN_spec h2 x hx
  rw [beq_iff_eq]
  exact Nat.eq_of_beq_eq_true this

theorem pos_facts : (∀ c < 486, D.PK (pg 12 (mask 12) T.C.F (3 * c)) = c + 1) ∧
    ∀ q < 3510, D.PK q = 0 ∨ (D.PK q ≤ 486 ∧ pg 12 (mask 12) T.C.F (3 * (D.PK q - 1)) = q) := by
  have h := K.pos
  unfold posChk at h
  rw [bAnd_eq', Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun c hc => Nat.eq_of_beq_eq_true (allN_spec h1 c hc), fun q hq => ?_⟩
  have a := allN_spec h2 q hq
  rw [CFSG.KC.Fi22RkS.strictB_eq, orB_eq', Bool.or_eq_true, nbeq'] at a
  rcases a with a | a
  · exact Or.inl (by simpa using a)
  · obtain ⟨b1, b2⟩ := (bAnd_iff _ _).1 a
    exact Or.inr ⟨Nat.ble_eq.mp b1, Nat.eq_of_beq_eq_true b2⟩

theorem ch_get {i : Nat} (hi : i < 1458) : (fi22RChain ())[i]! = pg 12 (mask 12) T.C.F i := by
  rw [rc_eq, get_unpack hi]

theorem pos_get : (fi22RPos ()).size = 3510 ∧ ∀ q < 3510, (fi22RPos ())[q]! = D.PK q := by
  obtain ⟨p1, p2⟩ := pos_facts
  have hcs : (fi22RChain ()).size = 1458 := by rw [rc_eq]; exact Array.size_ofFn
  have key := CFSG.Sporadic.FischerOddCore.SearchSpec.forIn_range_yield
    (fun c (pos : Array Nat) => pos.size = 3510 ∧
      ∀ q < 3510, pos[q]! = if 0 < D.PK q ∧ D.PK q ≤ c then D.PK q else 0)
    (fun c (pos : Array Nat) => (ForInStep.yield (pos.set! (fi22RChain ())[3 * c]! (c + 1)) :
      Id (ForInStep (Array Nat)))) 486 (Array.replicate 3510 0) (fun c pos hc hI => ?_) ?_
  · have e : fi22RPos () = forIn (m := Id) [:486] (Array.replicate 3510 0)
        (fun c (pos : Array Nat) => (ForInStep.yield (pos.set! (fi22RChain ())[3 * c]! (c + 1)) :
          Id (ForInStep (Array Nat)))) := by
      unfold fi22RPos
      dsimp only
      rw [hcs]
      rfl
    rw [e]
    refine ⟨key.1, fun q hq => ?_⟩
    rw [key.2 q hq]
    rcases p2 q hq with a | ⟨a, -⟩
    · rw [a]
      simp
    · by_cases h0 : D.PK q = 0
      · rw [h0]
        simp
      · rw [if_pos ⟨Nat.pos_of_ne_zero h0, a⟩]
  · obtain ⟨hs, hv⟩ := hI
    refine ⟨_, rfl, ?_, fun q hq => ?_⟩
    · rw [CFSG.Sporadic.FischerOddCore.SearchSpec.size_set!', hs]
    · rw [CFSG.Sporadic.FischerOddCore.SearchSpec.get!_set!_eq _ _ _ _ (by rw [hs]; exact hq),
        ch_get (by omega), hv q hq]
      by_cases hz : pg 12 (mask 12) T.C.F (3 * c) = q
      · rw [if_pos hz, ← hz, p1 c hc]
        simp
      · rw [if_neg hz]
        by_cases hpc : D.PK q = c + 1
        · exfalso
          rcases p2 q hq with a | ⟨-, a⟩
          · omega
          · rw [hpc, Nat.add_sub_cancel] at a
            exact hz a
        · by_cases h1 : 0 < D.PK q ∧ D.PK q ≤ c
          · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]
          · rw [if_neg h1, if_neg (by omega)]
  · refine ⟨by simp, fun q hq => ?_⟩
    rw [if_neg (by omega)]
    rw [getElem!_pos _ q (by simpa using hq)]
    simp

theorem stab_all : ∀ q < 3510, stabAt 12 D.IK D.SMK q = true := by
  intro q hq
  have h := chunk (m := 64) (K := 55) (f := fun q => bIf(Nat.blt q (nat_lit 3510),
      stabAt 12 D.IK D.SMK q, true)) (g := K.stab) (by decide) (fun c => by
      unfold K.stab
      congr 1
      funext r
      rw [CFSG.KC.Fi22RkS.strictB_eq]) K.stabAll q (by omega)
  exact bIf_lt h hq

theorem uniq_all : ∀ q < 3510, D.PK q = 0 → uniqAtK 12 D.IK D.CLK D.POK D.STK D.WK q = true := by
  intro q hq h0
  have h := chunk (m := 64) (K := 55) (f := fun q => bIf(Nat.blt q (nat_lit 3510),
      bIf(Nat.beq (D.PK q) (nat_lit 0), uniqAtK 12 D.IK D.CLK D.POK D.STK D.WK q, true), true))
    (g := K.uniq) (by decide) (fun c => by
      unfold K.uniq
      congr 1
      funext r
      rw [CFSG.KC.Fi22RkS.strictB_eq]) K.uniqAll q (by omega)
  have h2 := bIf_lt h hq
  rwa [h0] at h2

theorem chain_all : ∀ q < 3510, chainAt T.C.F D.PK q = true := by
  intro q hq
  have h := chunk (m := 64) (K := 55) (f := fun q => bIf(Nat.blt q (nat_lit 3510),
      chainAt T.C.F D.PK q, true)) (g := K.chain) (by decide) (fun c => by
      unfold K.chain
      congr 1
      funext r
      rw [CFSG.KC.Fi22RkS.strictB_eq]) K.chainAll q (by omega)
  exact bIf_lt h hq

theorem pos_ok : fi22PosOK () = true := by
  obtain ⟨hps, hpg⟩ := pos_get
  obtain ⟨-, p2⟩ := pos_facts
  unfold fi22PosOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨hps, CFSG.KS.Raw.Orb.parLt_of_forall fun q hq => ?_⟩
  rw [hpg q hq]
  by_cases h0 : D.PK q = 0
  · rw [if_pos h0]
    exact uniqAt_of (fun i hi x hx => iota_pt hi hx) (fun i hi x hx => iota_lt hi hx) stab_all
      K.cls K.blk hq (uniq_all q hq h0)
  · rw [if_neg h0]
    rcases p2 q hq with a | ⟨hle, hz⟩
    · exact absurd a h0
    have hc := chain_all q hq
    unfold chainAt at hc
    rw [CFSG.KC.Fi22RkS.strictB_eq, orB_eq', nbeq', beq_eq_false_iff_ne.mpr h0, Bool.false_or, CFSG.KC.Fi22RkS.strictB_eq,
      CFSG.KC.Fi22RkS.strictB_eq, CFSG.KC.Fi22RkS.strictB_eq] at hc
    simp only [bAnd_iff, Nat.blt_eq, Nat.ble_eq] at hc
    obtain ⟨hx, hy, hpx, hpy, he⟩ := hc
    change pg 12 (mask 12) T.C.F ((Nat.mul 3 (D.PK q - 1)).add 1) < 3510 at hx
    change pg 12 (mask 12) T.C.F ((Nat.mul 3 (D.PK q - 1)).add 2) < 3510 at hy
    change D.PK (pg 12 (mask 12) T.C.F ((Nat.mul 3 (D.PK q - 1)).add 1)) ≤ D.PK q - 1 at hpx
    change D.PK (pg 12 (mask 12) T.C.F ((Nat.mul 3 (D.PK q - 1)).add 2)) ≤ D.PK q - 1 at hpy
    change Nat.beq (cK (pg 12 (mask 12) T.C.F ((Nat.mul 3 (D.PK q - 1)).add 1))
      (pg 12 (mask 12) T.C.F ((Nat.mul 3 (D.PK q - 1)).add 2))) q = true at he
    have hx1 : 3 * (D.PK q - 1) + 1 < 1458 := by omega
    have hx2 : 3 * (D.PK q - 1) + 2 < 1458 := by omega
    have hcs : (fi22RChain ()).size = 1458 := by rw [rc_eq]; exact Array.size_ofFn
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    change Nat.add (Nat.mul 3 (D.PK q - 1)) 1 < 1458 at hx1
    rw [ch_get (by omega : 3 * (D.PK q - 1) < 1458), hz,
      ch_get (show 3 * (D.PK q - 1) + 1 < 1458 by omega),
      ch_get (show 3 * (D.PK q - 1) + 2 < 1458 by omega), hcs]
    have ex : pg 12 (mask 12) T.C.F (3 * (D.PK q - 1) + 1) =
        pg 12 (mask 12) T.C.F (Nat.add (Nat.mul 3 (D.PK q - 1)) 1) := rfl
    have ey : pg 12 (mask 12) T.C.F (3 * (D.PK q - 1) + 2) =
        pg 12 (mask 12) T.C.F (Nat.add (Nat.mul 3 (D.PK q - 1)) 2) := rfl
    rw [ex, ey]
    refine ⟨⟨⟨⟨⟨⟨by omega, rfl⟩, hx⟩, hy⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [hpg _ hx]
      exact hpx
    · rw [hpg _ hy]
      exact hpy
    · rw [ap_tab hx hy]
      exact Nat.eq_of_beq_eq_true he

end CertificateChecks.KernelFi22Rk.A

public section

namespace CertificateChecks.KernelFi22Rk.A

open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative

theorem rank : fi22RankOK () = true := by
  unfold fi22RankOK
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨side, nonab⟩, tau_ok⟩, pos_ok⟩

end CertificateChecks.KernelFi22Rk.A

end
