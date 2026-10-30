module

public import Certificates.Kernel.K133.GBarChecks
public import Certificates.Kernel.Sporadic.OddCore.HN2089
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelK133

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.RankThree.PartOne.K133Spor CFSG.Monster.B.Co2.Native CFSG.Sporadic.HNOddCore.Native
open CFSG.Monster.B.Fischer
open CFSG.Monster.B.Co2 (allLt_iff)

abbrev P9 (p : Nat) : Prop := PP 256 9 p

theorem hsz : szOK 256 9 = true := by quickRfl

theorem bq {a b : Nat} : Nat.beq a b = true ↔ a = b := ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem bqf {a b : Nat} : Nat.beq a b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, bq]

theorem gbN' : GB.N = 14400 := Nat.eq_of_beq_eq_true gbN

theorem gk : allN 11 (fun k => Nat.beq (GB.G k) (CertificateChecks.KernelSpor.HQK k)) = true := by
  quickRfl

theorem gens_eq : colPerms.size = GB.ng ∧ ∀ k < GB.ng, colPerms[k]! = unpack 256 9 (GB.G k) := by
  refine ⟨CertificateChecks.KernelSpor.HN2089.k_get.1, fun k hk => ?_⟩
  have hk' : k < 11 := hk
  rw [CertificateChecks.KernelSpor.HN2089.k_get.2 k hk', Nat.eq_of_beq_eq_true (allN_spec gk k hk')]

theorem hkeys : ∀ p ∈ gbarKeys, p < 256 := by decide

theorem enum_ok : CFSG.RankThree.Native.enumOK 256 colPerms gbarKeys gbarCert = true :=
  enumOK_of_bfsK_base gens_eq.1 gens_eq.2 (fun k hk => allN_spec gbPerm k hk) GB.ok hkeys gbKeys
    (by rw [gbN']; norm_num)

theorem pts_eq : gbarCert.pts = Array.ofFn (n := GB.N) fun i => unpack 256 9 (GB.T i.val) :=
  enumBfs_pts_base gens_eq.1 gens_eq.2 GB.ok hkeys gbKeys (by rw [gbN']; norm_num)

theorem pp_X {i : Nat} (hi : i < GB.N) : P9 (X i) :=
  PP_pts GB.ok (fun k hk => allN_spec gbPerm k hk) i hi

theorem mem_pts {x : Array Nat} (hx : x ∈ gbarCert.pts) : ∃ i < GB.N, x = unpack 256 9 (X i) := by
  rw [pts_eq] at hx
  obtain ⟨⟨i, hi⟩, rfl⟩ := Array.mem_ofFn.1 hx
  exact ⟨i, hi, rfl⟩

theorem get_unpack {P m : Nat} (hm : m < 256) : (unpack 256 9 P)[m]! = ap9 P m :=
  by rw [unpack_getElem!, if_pos hm]; rfl

theorem ap9_lt {P m : Nat} (hP : P9 P) (hm : m < 256) : ap9 P m < 256 := hP.2.1 m hm

theorem ap9_pc {P Q m : Nat} (hm : m < 256) : ap9 (pc P Q) m = ap9 P (ap9 Q m) :=
  CFSG.KS.PF.pg_pcomp (by norm_num) hm

theorem ap9_id {m : Nat} (hm : m < 256) : ap9 (pidn 256 9) m = m :=
  CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) hm

theorem isFive_eq {P : Nat} (hP : P9 P) :
    isFiveA 256 (unpack 256 9 P) =
      (Nat.beq (pc P (pc P (pc P (pc P P)))) (pidn 256 9) && !Nat.beq P (pidn 256 9)) := by
  unfold isFiveA powA5
  rw [compA_PP hP hP, compA_PP hP (hP.mul hP), compA_PP hP (hP.mul (hP.mul hP)),
    compA_PP hP (hP.mul (hP.mul (hP.mul hP))), idA_eq hsz,
    eqA_PP (hP.mul (hP.mul (hP.mul (hP.mul hP)))) (PP.id hsz), eqA_PP hP (PP.id hsz)]
  rfl

theorem isTwo_eq {P : Nat} (hP : P9 P) :
    isTwoA 256 (unpack 256 9 P) = (Nat.beq (pc P P) (pidn 256 9) && !Nat.beq P (pidn 256 9)) := by
  unfold isTwoA
  rw [compA_PP hP hP, idA_eq hsz, eqA_PP (hP.mul hP) (PP.id hsz), eqA_PP hP (PP.id hsz)]
  rfl

theorem five_listed {i : Nat} (hi : i < GB.N) (hc : coverK i = true)
    (h5 : isFiveA 256 (unpack 256 9 (X i)) = true) :
    GB.P5 i < 624 ∧ GB.FI (GB.P5 i) = i := by
  rw [isFive_eq (pp_X hi)] at h5
  simp only [Bool.and_eq_true, Bool.not_eq_true', bq, bqf] at h5
  obtain ⟨h1, h2⟩ := h5
  unfold coverK at hc
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, bq, bqf,
    Bool.not_eq_true'] at hc
  rcases hc.1 with (h | h) | ⟨hq, hq'⟩
  · exact h
  · rw [h] at h2
    simp at h2
  · have e := congrArg (fun Y => ap9 Y (GB.Q5 i)) h1
    simp only [ap9_pc hq, ap9_id hq] at e
    rw [e] at hq'
    simp at hq'

theorem two_listed {i : Nat} (hi : i < GB.N) (hc : coverK i = true)
    (h2 : isTwoA 256 (unpack 256 9 (X i)) = true) :
    GB.P2 i < 475 ∧ GB.WI (GB.P2 i) = i := by
  rw [isTwo_eq (pp_X hi)] at h2
  simp only [Bool.and_eq_true, Bool.not_eq_true', bq, bqf] at h2
  obtain ⟨h1, h3⟩ := h2
  unfold coverK at hc
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, bq, bqf,
    Bool.not_eq_true'] at hc
  rcases hc.2 with (h | h) | ⟨hq, hq'⟩
  · exact h
  · rw [h] at h3
    simp at h3
  · have e := congrArg (fun Y => ap9 Y (GB.Q2 i)) h1
    simp only [ap9_pc hq, ap9_id hq] at e
    rw [e] at hq'
    simp at hq'

theorem comm_ap {P Q : Nat} (hP : P9 P) (hQ : P9 Q)
    (h : commA 256 (unpack 256 9 P) (unpack 256 9 Q) = true) :
    ∀ m < 256, ap9 P (ap9 Q m) = ap9 Q (ap9 P m) := by
  intro m hm
  have h' := allLt_iff.1 h m hm
  rw [get_unpack hm, get_unpack hm, get_unpack (ap9_lt hQ hm), get_unpack (ap9_lt hP hm)] at h'
  exact beq_iff_eq.1 h'

theorem nc_comm {P Q : Nat} (hP : P9 P) (hQ : P9 Q) (h : ncK P Q = true) :
    commA 256 (unpack 256 9 P) (unpack 256 9 Q) = false := by
  by_contra hc
  rw [Bool.not_eq_false] at hc
  have hm := comm_ap hP hQ hc
  unfold ncK at h
  obtain ⟨e, he, hne⟩ := List.any_eq_true.1 h
  have hle : e < 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    omega
  rw [Bool.not_eq_true', bqf] at hne
  exact hne (hm e hle)

theorem line_mem {k Q : Nat} (hk : k < 624) (hA : P9 (A k)) (hQ : P9 Q) (hl : lineK k Q = true) :
    memLineA 256 (unpack 256 9 (A k)) (unpack 256 9 Q) = true := by
  have hp := allN_spec pows k hk
  unfold powK at hp
  simp only [Bool.and_eq_true, bq, bqf] at hp
  obtain ⟨⟨⟨-, e2⟩, e3⟩, e4⟩ := hp
  unfold memLineA
  rw [compA_PP hA hA, compA_PP hA (hA.mul hA), compA_PP hA (hA.mul (hA.mul hA)), idA_eq hsz,
    eqA_PP hQ (PP.id hsz), eqA_PP hQ hA, eqA_PP hQ (hA.mul hA), eqA_PP hQ (hA.mul (hA.mul hA)),
    eqA_PP hQ (hA.mul (hA.mul (hA.mul hA)))]
  have f2 : pcomp 256 9 (mask 9) (A k) (A k) = GB.L2 k := e2.symm
  have f3 : pcomp 256 9 (mask 9) (A k) (pcomp 256 9 (mask 9) (A k) (A k)) = GB.L3 k := by
    rw [f2]
    exact e3.symm
  have f4 : pcomp 256 9 (mask 9) (A k) (pcomp 256 9 (mask 9) (A k)
      (pcomp 256 9 (mask 9) (A k) (A k))) = GB.L4 k := by
    rw [f3]
    exact e4.symm
  rw [f4, f3, f2]
  exact hl

theorem ff_free {P Q : Nat} (h : ffK P Q = true) :
    fixFreeA 256 (unpack 256 9 P) (unpack 256 9 Q) = true := by
  unfold fixFreeA
  rw [allLt_iff]
  intro m hm
  have h' := allN_spec h m hm
  rw [get_unpack hm, get_unpack hm]
  simpa [bq, bqf] using h'

theorem fz_free {P Q : Nat} (h : fzK P = true) :
    fixFreeA 256 (unpack 256 9 P) (unpack 256 9 Q) = true := by
  unfold fixFreeA
  rw [allLt_iff]
  intro m hm
  have h' := allN_spec h m hm
  rw [get_unpack hm, get_unpack hm]
  by_cases e : m = 0
  · simp [e]
  · have e' : ap9 P m ≠ m := by simpa [bq, bqf, e] using h'
    simp [e, e']

theorem cover_all {i : Nat} (hi : i < GB.N) : coverK i = true := by
  rw [gbN'] at hi
  have e : ∀ lo l, Nat.add lo l = lo + l := fun _ _ => rfl
  rcases (by omega : i < 4800 ∨ (4800 ≤ i ∧ i < 9600) ∨ (9600 ≤ i ∧ i < 14400)) with
    h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simpa [e] using allBlk_spec cov0 i h
  · simpa [e, Nat.add_sub_cancel' h1] using allBlk_spec cov1 (i - 4800) (by omega)
  · simpa [e, Nat.add_sub_cancel' h1] using allBlk_spec cov2 (i - 9600) (by omega)

theorem pairB_all {k : Nat} (hk : k < 624) : pairB k = true := by
  have e : ∀ lo l, Nat.add lo l = lo + l := fun _ _ => rfl
  have key : ∀ c < 13, allBlk (48 * c) pairB 48 = true := by
    intro c hc
    interval_cases c
    exacts [pb0, pb1, pb2, pb3, pb4, pb5, pb6, pb7, pb8, pb9, pb10, pb11, pb12]
  have h := allBlk_spec (key (k / 48) (by omega)) (k % 48) (Nat.mod_lt _ (by norm_num))
  rwa [e, Nat.div_add_mod] at h

theorem pairA_all {j : Nat} (hj : j < 475) : pairA j = true := by
  have e : ∀ lo l, Nat.add lo l = lo + l := fun _ _ => rfl
  have key : ∀ c < 19, allBlk (25 * c) pairA 25 = true := by
    intro c hc
    interval_cases c
    exacts [ua0, ua1, ua2, ua3, ua4, ua5, ua6, ua7, ua8, ua9, ua10, ua11, ua12, ua13, ua14, ua15,
      ua16, ua17, ua18]
  have h := allBlk_spec (key (j / 25) (by omega)) (j % 25) (Nat.mod_lt _ (by norm_num))
  rwa [e, Nat.div_add_mod] at h

theorem inU_spec {j k : Nat} (h : inU j k = true) :
    ∃ l < GB.UO (j + 1) - GB.UO j, GB.UV (GB.UO j + l) = k := by
  unfold inU at h
  by_contra hc
  push Not at hc
  have : allBlk (GB.UO j) (fun t => !Nat.beq (GB.UV t) k) (GB.UO (j + 1) - GB.UO j) = true :=
    allBlk_intro fun l hl => by
      have := hc l hl
      simpa [bq, bqf] using this
  rw [this] at h
  simp at h

theorem filter_mem {p : Array Nat → Bool} {pts : Array (Array Nat)} {x : Array Nat}
    (h : x ∈ pts.filter p) : x ∈ pts ∧ p x = true := Array.mem_filter.1 h

theorem all_of {p : Array Nat → Bool} {a : Array (Array Nat)} (h : ∀ x ∈ a, p x = true) :
    a.all p = true := by
  rw [Array.all_eq_true]
  intro i hi
  exact h _ (Array.getElem_mem hi)

theorem halfB {a b : Array Nat} (ha : a ∈ gbarCert.pts) (ha5 : isFiveA 256 a = true)
    (hb : b ∈ gbarCert.pts) (hb5 : isFiveA 256 b = true) :
    (fixFreeA 256 a b || !commA 256 a b || memLineA 256 a b) = true := by
  obtain ⟨i, hi, rfl⟩ := mem_pts ha
  obtain ⟨i', hi', rfl⟩ := mem_pts hb
  obtain ⟨hk, ek⟩ := five_listed hi (cover_all hi) ha5
  obtain ⟨hk', ek'⟩ := five_listed hi' (cover_all hi') hb5
  have hA : X i = A (GB.P5 i) := by unfold A; rw [ek]
  have hB : X i' = A (GB.P5 i') := by unfold A; rw [ek']
  have ppA : P9 (A (GB.P5 i)) := hA ▸ pp_X hi
  have ppB : P9 (A (GB.P5 i')) := hB ▸ pp_X hi'
  rw [hA, hB]
  have h := pairB_all hk
  unfold pairB at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [fz_free h]
    rfl
  · have h' := allN_spec h _ hk'
    simp only [Bool.or_eq_true] at h'
    rcases h' with (h' | h') | h'
    · rw [nc_comm ppA ppB h']
      simp
    · rw [line_mem hk ppA ppB h']
      simp
    · rw [ff_free h']
      rfl

theorem halfA {u a b : Array Nat} (hu : u ∈ gbarCert.pts) (hu2 : isTwoA 256 u = true)
    (ha : a ∈ gbarCert.pts) (ha5 : isFiveA 256 a = true) (hua : commA 256 u a = true)
    (hb : b ∈ gbarCert.pts) (hb5 : isFiveA 256 b = true) (hub : commA 256 u b = true) :
    (!commA 256 a b || memLineA 256 a b) = true := by
  obtain ⟨i0, hi0, rfl⟩ := mem_pts hu
  obtain ⟨i, hi, rfl⟩ := mem_pts ha
  obtain ⟨i', hi', rfl⟩ := mem_pts hb
  obtain ⟨hj, ej⟩ := two_listed hi0 (cover_all hi0) hu2
  obtain ⟨hk, ek⟩ := five_listed hi (cover_all hi) ha5
  obtain ⟨hk', ek'⟩ := five_listed hi' (cover_all hi') hb5
  have ppU := pp_X hi0
  have ppA := pp_X hi
  have ppB := pp_X hi'
  have hU : X i0 = U (GB.P2 i0) := by unfold U; rw [ej]
  have hA : X i = A (GB.P5 i) := by unfold A; rw [ek]
  have hB : X i' = A (GB.P5 i') := by unfold A; rw [ek']
  rw [hU] at ppU hua hub
  rw [hA] at ppA hua ⊢
  rw [hB] at ppB hub ⊢
  have h := pairA_all hj
  unfold pairA at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨-, hcov⟩, hpairs⟩ := h
  have mem : ∀ k < 624, commA 256 (unpack 256 9 (U (GB.P2 i0))) (unpack 256 9 (A k)) = true →
      P9 (A k) → ∃ l < GB.UO (GB.P2 i0 + 1) - GB.UO (GB.P2 i0),
        GB.UV (GB.UO (GB.P2 i0) + l) = k := by
    intro k hk hc pk
    have h1 := allN_spec hcov k hk
    simp only [Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · rw [nc_comm ppU pk h1] at hc
      simp at hc
    · exact inU_spec h1
  obtain ⟨l, hl, el⟩ := mem _ hk hua ppA
  obtain ⟨l', hl', el'⟩ := mem _ hk' hub ppB
  have hrow := allBlk_spec hpairs l hl
  simp only [Bool.and_eq_true] at hrow
  have hcell := allBlk_spec hrow.2 l' hl'
  change ncK (A (GB.UV (GB.UO (GB.P2 i0) + l))) (A (GB.UV (GB.UO (GB.P2 i0) + l'))) ||
    lineK (GB.UV (GB.UO (GB.P2 i0) + l)) (A (GB.UV (GB.UO (GB.P2 i0) + l'))) = true at hcell
  rw [el, el'] at hcell
  simp only [Bool.or_eq_true] at hcell
  rcases hcell with h' | h'
  · rw [nc_comm ppA ppB h']
    simp
  · rw [line_mem hk ppA ppB h']
    simp

theorem gbarCheck_eq : gbarCheck 256 gbarCert.pts = true := by
  unfold gbarCheck
  simp only [Bool.and_eq_true]
  refine ⟨all_of fun u hu => ?_, all_of fun a ha => all_of fun b hb => ?_⟩
  · obtain ⟨hu', hu2⟩ := filter_mem hu
    refine all_of fun a ha => all_of fun b hb => ?_
    obtain ⟨ha', hua⟩ := filter_mem ha
    obtain ⟨hb', hub⟩ := filter_mem hb
    obtain ⟨ha'', ha5⟩ := filter_mem ha'
    obtain ⟨hb'', hb5⟩ := filter_mem hb'
    exact halfA hu' hu2 ha'' ha5 hua hb'' hb5 hub
  · obtain ⟨ha', ha5⟩ := filter_mem ha
    obtain ⟨hb', hb5⟩ := filter_mem hb
    exact halfB ha' ha5 hb' hb5

theorem gbarOK : GBarOK := by
  unfold GBarOK
  rw [enum_ok, gbarCheck_eq]
  rfl

end CertificateChecks.KernelK133

end
