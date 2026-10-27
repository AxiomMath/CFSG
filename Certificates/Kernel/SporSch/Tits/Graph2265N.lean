module

public import Certificates.Kernel.SporSch.Tits.Graph2265K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsGraph

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelSporSch.TitsAction

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem nat_beq (a b : Nat) : (a == b) = Nat.beq a b := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]

theorem hL : ∀ j < 3 * 2925, titsLinePtArr[j]! = lpK j := fun _ hj => lp_get (by omega)

theorem nbr_eq : titsNbr = Array.ofFn (n := 1755)
    (fun u => Array.ofFn (n := 10) fun i => pgW 11 TitsGN.NB (10 * u + i)) := by
  rw [titsNbr_eq, titsNbrData_eq]
  exact (nbrK_sound hL kN).1

theorem line_eq : titsNbrLine = Array.ofFn (n := 1755)
    (fun u => Array.ofFn (n := 10) fun i => pgW 12 TitsGN.NL (10 * u + i)) := by
  rw [titsNbrLine_eq, titsNbrData_eq]
  exact (nbrK_sound hL kN).2

theorem nbr_get {u : Nat} (hu : u < 1755) :
    titsNbr[u]! = Array.ofFn (n := 10) fun i => pgW 11 TitsGN.NB (10 * u + i) := by
  rw [nbr_eq, getElem!_pos _ u (by simpa using hu), Array.getElem_ofFn]

theorem line_get {u : Nat} (hu : u < 1755) :
    titsNbrLine[u]! = Array.ofFn (n := 10) fun i => pgW 12 TitsGN.NL (10 * u + i) := by
  rw [line_eq, getElem!_pos _ u (by simpa using hu), Array.getElem_ofFn]

theorem ofFn_get {w P u i : Nat} (hi : i < 10) :
    (Array.ofFn (n := 10) fun j => pgW w P (10 * u + j))[i]! = pgW w P (10 * u + i) := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := by
  rwa [Nat.blt_eq] at h

theorem kN_parts : (∀ u < 1755, ∀ i < 10, nbrRowK 1755 2925 10 11 12 TitsGN.NB TitsGN.NL u i =
      true) ∧ ∀ v < 2925, nbrLineK 1755 10 11 12 lpK TitsGN.NB TitsGN.NL TitsGN.PW v = true := by
  have h : bAnd(allN 1755 (fun u => allN 10 (nbrRowK 1755 2925 10 11 12 TitsGN.NB TitsGN.NL u)),
      allN 2925 (nbrLineK 1755 10 11 12 lpK TitsGN.NB TitsGN.NL TitsGN.PW)) = true := kN
  obtain ⟨hr, hl⟩ := (bAnd_iff
    (allN 1755 (fun u => allN 10 (nbrRowK 1755 2925 10 11 12 TitsGN.NB TitsGN.NL u)))
    (allN 2925 (nbrLineK 1755 10 11 12 lpK TitsGN.NB TitsGN.NL TitsGN.PW))).1 h
  exact ⟨fun u hu i hi => allN_spec (allN_spec hr u hu) i hi, fun v hv => allN_spec hl v hv⟩

theorem row_facts {u i : Nat} (hu : u < 1755) (hi : i < 10) :
    pgW 11 TitsGN.NB (10 * u + i) < 1755 ∧ pgW 12 TitsGN.NL (10 * u + i) < 2925 ∧
      (i + 1 < 10 → pgW 11 TitsGN.NB (10 * u + i) < pgW 11 TitsGN.NB (10 * u + i + 1)) := by
  have h := kN_parts.1 u hu i hi
  unfold nbrRowK at h
  rw [strictB_eq] at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  refine ⟨lt_of_blt h1, lt_of_blt h2, fun hs => ?_⟩
  have hb : Nat.blt (Nat.succ i) 10 = true := by rwa [Nat.blt_eq]
  rw [hb] at h3
  exact lt_of_blt h3

theorem row_mono {u : Nat} (hu : u < 1755) :
    ∀ {i j : Nat}, i < j → j < 10 → pgW 11 TitsGN.NB (10 * u + i) < pgW 11 TitsGN.NB (10 * u + j)
  | _, 0, h, _ => absurd h (Nat.not_lt_zero _)
  | i, j + 1, h, hj => by
    have hs := (row_facts hu (by omega : j < 10)).2.2 hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
    · exact lt_trans (row_mono hu h' (by omega)) hs
    · rw [h']
      exact hs

theorem e_facts {u i : Nat} (hu : u < 1755) (hi : i < 10) :
    pgW 11 TitsGN.NB (10 * u + i) ≠ u ∧ ptsK (pgW 12 TitsGN.NL (10 * u + i)) u = true ∧
      ptsK (pgW 12 TitsGN.NL (10 * u + i)) (pgW 11 TitsGN.NB (10 * u + i)) = true := by
  have h := allN_spec (allN_spec kE u hu) i hi
  rw [strictB_eq, strictB_eq] at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  refine ⟨fun he => ?_, h2, h3⟩
  rw [he, Nat.beq_refl] at h1
  exact Bool.false_ne_true h1

theorem pts_eq {v u : Nat} (hv : v < 2925) : ptsHas v u = ptsK v u := by
  unfold ptsHas ptsK
  rw [lp_get (by omega), lp_get (by omega), lp_get (by omega), nat_beq, nat_beq, nat_beq]
  cases Nat.beq (lpK (3 * v)) u <;> cases Nat.beq (lpK (3 * v + 1)) u <;> rfl

theorem line_facts {v : Nat} (hv : v < 2925) :
    lpK (3 * v) < 1755 ∧ lpK (3 * v + 1) < 1755 ∧ lpK (3 * v + 2) < 1755 ∧
      ∀ kk < 6, ∃ p < 10, pgW 11 TitsGN.NB (10 * lpK (3 * v + pairFst kk) + p) =
        lpK (3 * v + pairSnd kk) := by
  have h := kN_parts.2 v hv
  unfold nbrLineK at h
  rw [strictB_eq, strictB_eq, strictB_eq] at h
  obtain ⟨h0, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
  refine ⟨lt_of_blt h0, lt_of_blt h1, lt_of_blt h2,
    fun kk hk => ?_⟩
  have hp := allN_spec h kk hk
  unfold nbrPairK at hp
  rw [strictB_eq, strictB_eq, strictB_eq] at hp
  obtain ⟨hp1, hp⟩ := (bAnd_iff _ _).1 hp
  exact ⟨_, lt_of_blt hp1, Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 hp).1⟩

theorem mem_nbr {a b p : Nat} (ha : a < 1755) (hp : p < 10)
    (h : pgW 11 TitsGN.NB (10 * a + p) = b) : (titsNbr[a]!).contains b = true := by
  rw [nbr_get ha]
  exact Array.contains_eq_true_of_mem (Array.mem_ofFn.2 ⟨⟨p, hp⟩, h⟩)

theorem graphFacts : (∀ u < 1755, (titsNbr[u]!).size = 10 ∧ (titsNbrLine[u]!).size = 10 ∧
      (titsNbr[u]!).toList.Pairwise (· < ·) ∧
      ∀ i < 10, (titsNbr[u]!)[i]! < 1755 ∧ (titsNbr[u]!)[i]! ≠ u ∧ (titsNbrLine[u]!)[i]! < 2925 ∧
        ptsHas (titsNbrLine[u]!)[i]! u = true ∧
        ptsHas (titsNbrLine[u]!)[i]! (titsNbr[u]!)[i]! = true) ∧
    (∀ v < 2925, ∀ k < 3, ∀ k' < 3, k ≠ k' →
      (titsNbr[titsLinePtArr[3 * v + k]!]!).contains titsLinePtArr[3 * v + k']! = true) ∧
    (titsNbr[0]!).contains 1 = true := by
  refine ⟨fun u hu => ⟨?_, ?_, ?_, fun i hi => ?_⟩, fun v hv k hk k' hk' hkk => ?_, ?_⟩
  · rw [nbr_get hu, Array.size_ofFn]
  · rw [line_get hu, Array.size_ofFn]
  · rw [nbr_get hu, Array.toList_ofFn, List.pairwise_ofFn]
    intro i j hij
    exact row_mono hu hij j.2
  · rw [nbr_get hu, line_get hu, ofFn_get hi, ofFn_get hi]
    obtain ⟨r1, r2, -⟩ := row_facts hu hi
    obtain ⟨e1, e2, e3⟩ := e_facts hu hi
    exact ⟨r1, e1, r2, by rw [pts_eq r2]; exact e2, by rw [pts_eq r2]; exact e3⟩
  · obtain ⟨l0, l1, l2, hpair⟩ := line_facts hv
    have key : ∀ kk < 6, pairFst kk = k → pairSnd kk = k' →
        (titsNbr[titsLinePtArr[3 * v + k]!]!).contains titsLinePtArr[3 * v + k']! = true := by
      intro kk hkk e1 e2
      obtain ⟨p, hp, he⟩ := hpair kk hkk
      rw [e1, e2] at he
      rw [lp_get (by omega), lp_get (by omega)]
      refine mem_nbr ?_ hp he
      interval_cases k
      · exact l0
      · exact l1
      · exact l2
    interval_cases k <;> interval_cases k'
    all_goals first
      | exact absurd rfl hkk
      | exact key 0 (by norm_num) rfl rfl
      | exact key 1 (by norm_num) rfl rfl
      | exact key 2 (by norm_num) rfl rfl
      | exact key 3 (by norm_num) rfl rfl
      | exact key 4 (by norm_num) rfl rfl
      | exact key 5 (by norm_num) rfl rfl
  · rw [nbr_get (by norm_num)]
    exact k01

end CertificateChecks.KernelSporSch.TitsGraph

end
