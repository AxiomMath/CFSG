module

public import Certificates.Kernel.HMathieu.C7243Orb
public import Certificates.Kernel.HMathieu.T24Glue
public import CFSG.Certificates.Kernel.HMathieu.RepSound
public import CFSG.Certificates.Kernel.HMathieu.MatSearch
import CFSG.Certificates.Kernel.HMathieu.FixTabSound

public section

namespace CertificateChecks.KernelHMathieu.C7243Orb

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1

theorem strictL_eq_app (y : Nat) (k : Nat → List Nat) : strictL y k = k y := by
  cases y <;> rfl

theorem mems_succ (k i : Nat) : mems (k + 1) i = repX i :: mems k (repPar i) := by
  rw [mems, strictL_eq_app, strictL_eq_app]

theorem length_mems : ∀ k i, (mems k i).length = k
  | 0, _ => rfl
  | k + 1, i => by rw [mems_succ, List.length_cons, length_mems k]

theorem fixL_succ (k i : Nat) : fixL (k + 1) i =
    (fixL k (repPar i)).filter fun m => Nat.beq (actK (T24.Md.getD (repX i) []) m) m := by
  rw [fixL, strictL_eq_app, strictL_eq_app]

theorem repOK_of_lt : ∀ i < 752, repOK i = true := by
  intro i hi
  have h : ∀ a n, blkOK a n = true → a ≤ i → i < a + n → repOK i = true := fun a n h h1 h2 =>
    List.all_eq_true.1 h i (List.mem_range'_1.2 ⟨h1, h2⟩)
  by_cases h1 : i < 100
  · exact h 0 100 b0 (by omega) (by omega)
  by_cases h2 : i < 200
  · exact h 100 100 b1 (by omega) (by omega)
  by_cases h3 : i < 300
  · exact h 200 100 b2 (by omega) (by omega)
  by_cases h4 : i < 400
  · exact h 300 100 b3 (by omega) (by omega)
  by_cases h5 : i < 500
  · exact h 400 100 b4 (by omega) (by omega)
  by_cases h6 : i < 600
  · exact h 500 100 b5 (by omega) (by omega)
  by_cases h7 : i < 700
  · exact h 600 100 b6 (by omega) (by omega)
  · exact h 700 52 b7 (by omega) (by omega)

theorem structOK_all {i : Nat} (hi : i < 752) : structOK i = true := by
  have h := repOK_of_lt i hi
  simp only [repOK, Bool.and_eq_true] at h
  exact h.1

theorem testBit_foldl_span (S : Nat) (f : Nat → Nat) (s : Nat) : ∀ (L : List Nat) (A : Nat),
    (L.foldl (fun acc t => bif Nat.testBit S t then Nat.lor acc (2 ^ f t) else acc)
      A).testBit s = true ↔ A.testBit s = true ∨ ∃ t ∈ L, S.testBit t = true ∧ f t = s
  | [], A => by simp
  | t :: L, A => by
    rw [List.foldl_cons, testBit_foldl_span S f s L]
    cases h : S.testBit t
    · simp only [Bool.cond_false, List.mem_cons, exists_eq_or_imp, h]
      simp
    · have e : (A.lor (2 ^ f t)).testBit s = (A.testBit s || decide (f t = s)) := by
        change (A ||| 2 ^ f t).testBit s = _
        rw [Nat.testBit_or, Nat.testBit_two_pow]
      simp only [Bool.cond_true, List.mem_cons, exists_eq_or_imp, h, e, Bool.or_eq_true,
        decide_eq_true_eq, true_and]
      tauto

theorem testBit_spanAdd (x S s : Nat) : (spanAdd x S).testBit s = true ↔
    S.testBit s = true ∨ ∃ t < 192, S.testBit t = true ∧ mkT x t = s := by
  unfold spanAdd
  rw [testBit_foldl_span]
  simp only [List.mem_range]

theorem mkF_eq_mkT {x : Nat} (hx : x < 191) (t : Nat) : mkF (mkD T24.rows) 191 x t = mkT x t := by
  unfold mkF mkT
  rw [ite_eq_right (Nat.ne_of_lt hx)]
  by_cases ht : t = 191
  · subst ht
    rfl
  · rw [ite_eq_right ht, CFSG.KC.HMathieu.beq_false_of_ne ht]
    rfl

@[expose] noncomputable def memsE (i : Nat) : List T24s2.Elem :=
  (mems (repRank i) i).map (el inv24s2)

theorem el_mem_inv24 {x : Nat} (hx : x < 191) : el inv24s2 x ∈ inv24s2 := by
  rw [el_of_lt (by rw [T24.len]; exact hx)]
  exact List.getElem_mem _

theorem idxOf_el' {x : Nat} (hx : x ≤ 191) : inv24s2.idxOf (el inv24s2 x) = x :=
  idxOf_el T24.gtabs (by rw [T24.len]; exact hx)

theorem struct_sound : ∀ i < 752, (∀ y ∈ mems (repRank i) i, y < 191) ∧ IndepList (memsE i) ∧
    CMask inv24s2 (memsE i) (cmOf (repRank i) i) ∧
    ∀ s, (mask i).testBit s = true ↔ ∃ z ∈ subprods (memsE i), inv24s2.idxOf z = s := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  have hs := structOK_all hi
  by_cases hi0 : i = 0
  · subst hi0
    simp only [structOK, Nat.beq_refl, Bool.cond_true, Bool.and_eq_true] at hs
    have hr : repRank 0 = 0 := Nat.eq_of_beq_eq_true hs.1
    have hm : mask 0 = 2 ^ 191 := Nat.eq_of_beq_eq_true hs.2
    unfold memsE
    rw [hr, hm]
    refine ⟨by simp [mems], IndepList.nil, ?_, fun s => ?_⟩
    · have := cmask_nil inv24s2
      rw [T24.len] at this
      exact this
    · simp only [mems, List.map_nil, subprods, List.mem_singleton, exists_eq_left,
        List.idxOf_eq_length (one_notMem T24.gtabs), T24.len, Nat.testBit_two_pow,
        decide_eq_true_eq]
  · simp only [structOK, CFSG.KC.HMathieu.beq_false_of_ne hi0, Bool.cond_false,
      Bool.and_eq_true, Nat.blt_eq, strictBo_eq_app,
      Bool.not_eq_true'] at hs
    obtain ⟨⟨⟨⟨hp, hr⟩, hx⟩, hc⟩, hn, hm⟩ := hs
    have hr : repRank i = repRank (repPar i) + 1 := Nat.eq_of_beq_eq_true hr
    have hm : mask i = spanAdd (repX i) (mask (repPar i)) := Nat.eq_of_beq_eq_true hm
    obtain ⟨hpos, hind, hcm, hsp⟩ := ih _ hp (by omega)
    set p := repPar i
    set x := repX i
    have hxR := el_mem_inv24 hx
    have hxi : inv24s2.idxOf (el inv24s2 x) = x := idxOf_el' hx.le
    have he : memsE i = el inv24s2 x :: memsE p := by
      unfold memsE
      rw [hr, mems_succ, List.map_cons]
    have hci := isCommInvol_of_indepList hind
    have hcomm : ∀ y ∈ memsE p, el inv24s2 x * y = y * el inv24s2 x := by
      have := hcm x (by rw [T24.len]; exact hx)
      rw [hc, eq_comm, List.all_eq_true] at this
      intro y hy
      simpa using this y hy
    have hnot : el inv24s2 x ∉ subprods (memsE p) := by
      intro h
      have := (hsp x).2 ⟨_, h, hxi⟩
      rw [hn] at this
      exact Bool.false_ne_true this
    have hinv := T24.gtabs.invol _ hxR
    refine ⟨?_, ?_, ?_, fun s => ?_⟩
    · rw [hr, mems_succ]
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hx
      · exact hpos y hy
    · rw [he]
      exact IndepList.cons _ _ hinv.2 hinv.1 hcomm hnot hind
    · rw [he, hr]
      have := cmask_cons T24.gtabs hcm hxR
      rw [hxi] at this
      change CMask _ _ (cmT x &&& cmOf (repRank p) p)
      rw [Nat.land_comm]
      exact this
    · rw [hm, testBit_spanAdd, he]
      constructor
      · rintro (h | ⟨t, ht, hb, rfl⟩)
        · obtain ⟨z, hz, e⟩ := (hsp s).1 h
          exact ⟨z, mem_subprods_cons.2 (Or.inl hz), e⟩
        · obtain ⟨z, hz, rfl⟩ := (hsp t).1 hb
          refine ⟨_, mem_subprods_cons.2 (Or.inr ⟨z, hz, rfl⟩), ?_⟩
          rw [idxOf_mul T24.gtabs hxR (mem_or_one_of_subprods T24.gtabs hci hz)
            (commute_subprods hcomm z hz), hxi, T24.len, mkF_eq_mkT hx]
      · rintro ⟨z, hz, rfl⟩
        rcases mem_subprods_cons.1 hz with hz | ⟨w, hw, rfl⟩
        · exact Or.inl ((hsp _).2 ⟨z, hz, rfl⟩)
        · refine Or.inr ⟨inv24s2.idxOf w, ?_, (hsp _).2 ⟨w, hw, rfl⟩, ?_⟩
          · have := idxOf_le (R := inv24s2) w
            rw [T24.len] at this
            omega
          · rw [idxOf_mul T24.gtabs hxR (mem_or_one_of_subprods T24.gtabs hci hw)
              (commute_subprods hcomm w hw), hxi, T24.len, mkF_eq_mkT hx]

theorem scan_rec {j : Nat} {l : List Nat} {c S : Nat} : ∀ (xs : List Nat) (k : Nat),
    scan j l c S xs k = true → ∀ x ∈ xs, c.testBit x = true → S.testBit x = false →
      ∃ e, recOK j l x e = true
  | [], _, _, x, hx, _, _ => by simp at hx
  | y :: xs, k, h, x, hx, hc, hS => by
    rw [scan] at h
    cases hy : (Nat.testBit c y && !Nat.testBit S y)
    · rw [hy, Bool.cond_false] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [hc, hS] at hy
        simp at hy
      · exact scan_rec xs k h x hx hc hS
    · rw [hy, Bool.cond_true, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨_, h.1⟩
      · exact scan_rec xs _ h.2 x hx hc hS

theorem rowOK_all : ∀ r < 64, rowOK r = true := by
  intro r hr
  have h : ∀ a, (List.range' a 16).all rowOK = true → a ≤ r → r < a + 16 → rowOK r = true :=
    fun a h h1 h2 => List.all_eq_true.1 h r (List.mem_range'_1.2 ⟨h1, h2⟩)
  by_cases h1 : r < 16
  · exact h 0 r0 (by omega) (by omega)
  by_cases h2 : r < 32
  · exact h 16 r1 (by omega) (by omega)
  by_cases h3 : r < 48
  · exact h 32 r2 (by omega) (by omega)
  · exact h 48 r3 (by omega) (by omega)

theorem rowAt_conj {r : Nat} (hr : r < 64) : ∃ g : T24s2.Elem, ∀ y < 191,
    MulAut.conj g (el inv24s2 y) = el inv24s2 (rowAt r y) := by
  have h := rowOK_all r hr
  simp only [rowOK, Bool.and_eq_true, Nat.blt_eq, List.all_eq_true, List.mem_range,
    strictBo_eq_app] at h
  have hl : T24s2.invols.length = 191 := T24.len
  obtain ⟨g, hg⟩ := exists_conj_of_row T24.packed T24.invData T24.idOK h.1 (fun y => rowAt r y)
    (fun y hy => by
      have : rowAt r y < 192 := (h.2 y (by omega)).1
      omega)
    (fun y hy => Nat.eq_of_beq_eq_true (h.2 y (by omega)).2)
  exact ⟨g, fun y hy => hg y (by omega)⟩

theorem cons_memsE {i : Nat} {x : T24s2.Elem} (hx : x ∈ inv24s2) :
    x :: memsE i = (inv24s2.idxOf x :: mems (repRank i) i).map (el inv24s2) := by
  rw [List.map_cons, el_idxOf (Or.inl hx)]
  rfl

theorem mem_subprods_of_bit {t s : Nat} (ht : t < 752) (h : (mask t).testBit s = true) :
    el inv24s2 s ∈ subprods (memsE t) := by
  obtain ⟨_, hind, _, hsp⟩ := struct_sound t ht
  obtain ⟨z, hz, rfl⟩ := (hsp s).1 h
  rw [el_idxOf (mem_or_one_of_subprods T24.gtabs (isCommInvol_of_indepList hind) hz)]
  exact hz

theorem ext_of_rep {i : Nat} (hi : i < 752) (h6 : repRank i < 6) {x : T24s2.Elem}
    (hx : x ∈ inv24s2) (hxi : IndepList (x :: memsE i)) : ∃ g : T24s2.Elem, ∃ t < 752,
      repRank t = repRank i + 1 ∧ ∀ y ∈ x :: memsE i, MulAut.conj g y ∈ subprods (memsE t) := by
  obtain ⟨hpos, hind, hcm, hsp⟩ := struct_sound i hi
  have hrep := repOK_of_lt i hi
  simp only [repOK, Bool.and_eq_true, Bool.or_eq_true, strictBo_eq_app,
    CFSG.KC.HMathieu.beq_false_of_ne (Nat.ne_of_lt h6),
    Bool.false_eq_true, false_or] at hrep
  have hxl : inv24s2.idxOf x < 191 := by
    rw [← T24.len]
    exact List.idxOf_lt_length_iff.2 hx
  cases hxi with
  | cons _ _ _ _ hc hn _ =>
  have hcx : (cmOf (repRank i) i).testBit (inv24s2.idxOf x) = true := by
    rw [hcm _ (by rw [T24.len]; exact hxl), el_idxOf (Or.inl hx), List.all_eq_true]
    intro y hy
    simpa using hc y hy
  have hmx : (mask i).testBit (inv24s2.idxOf x) = false := by
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨z, hz, e⟩ := (hsp _).1 h
    have hz1 := mem_or_one_of_subprods T24.gtabs (isCommInvol_of_indepList hind) hz
    exact hn (idxOf_inj T24.gtabs hz1 (Or.inl hx) e ▸ hz)
  obtain ⟨e, he⟩ := scan_rec _ _ hrep.2 _ (List.mem_range.2 hxl) hcx hmx
  simp only [recOK, Bool.and_eq_true, Nat.blt_eq, List.all_eq_true, strictBo_eq_app] at he
  obtain ⟨⟨ht, hrt⟩, hbits⟩ := he
  obtain ⟨g, hg⟩ := rowAt_conj (r := Nat.land e 63) (Nat.lt_of_le_of_lt Nat.and_le_right (by omega))
  refine ⟨g, _, ht, Nat.eq_of_beq_eq_true hrt, ?_⟩
  rw [cons_memsE hx]
  intro y hy
  obtain ⟨yp, hyp, rfl⟩ := List.mem_map.1 hy
  have hyl : yp < 191 := by
    rcases List.mem_cons.1 hyp with rfl | hyp
    · exact hxl
    · exact hpos yp hyp
  rw [hg yp hyl]
  exact mem_subprods_of_bit ht (hbits yp hyp)

theorem predOK_all : ∀ i < 752, predOK i = true := by
  intro i hi
  have h : ∀ a n, predBlk a n = true → a ≤ i → i < a + n → predOK i = true := fun a n h h1 h2 =>
    List.all_eq_true.1 h i (List.mem_range'_1.2 ⟨h1, h2⟩)
  by_cases h1 : i < 100
  · exact h 0 100 p0 (by omega) (by omega)
  by_cases h2 : i < 200
  · exact h 100 100 p1 (by omega) (by omega)
  by_cases h3 : i < 300
  · exact h 200 100 p2 (by omega) (by omega)
  by_cases h4 : i < 400
  · exact h 300 100 p3 (by omega) (by omega)
  by_cases h5 : i < 500
  · exact h 400 100 p4 (by omega) (by omega)
  by_cases h6 : i < 600
  · exact h 500 100 p5 (by omega) (by omega)
  by_cases h7 : i < 700
  · exact h 600 100 p6 (by omega) (by omega)
  by_cases h8 : i < 750
  · exact h 700 50 p7 (by omega) (by omega)
  by_cases h9 : i < 751
  · exact h 750 1 p8 (by omega) (by omega)
  · exact h 751 1 p9 (by omega) (by omega)

theorem map_subprods_eq_spanL : ∀ ps : List Nat, (∀ y ∈ ps, y < 191) →
    IndepList (ps.map (el inv24s2)) → (subprods (ps.map (el inv24s2))).map inv24s2.idxOf = spanL ps
  | [], _, _ => by
    simp [subprods, spanL, List.idxOf_eq_length (one_notMem T24.gtabs), T24.len]
  | y :: ps, hp, hi => by
    have hy := hp y List.mem_cons_self
    rw [List.map_cons] at hi ⊢
    have hi' := hi
    cases hi' with
    | cons _ _ _ _ hc _ ht =>
    rw [map_subprods_cons T24.gtabs (el_mem_inv24 hy) (isCommInvol_of_indepList ht) hc,
      map_subprods_eq_spanL ps (fun z hz => hp z (List.mem_cons_of_mem y hz)) ht, spanL,
      idxOf_el' hy.le, T24.len]
    congr 1
    exact List.map_congr_left fun t _ => mkF_eq_mkT hy t

theorem fixL_eq_fixMasks : ∀ k i, fixL k i = fixMasks 11 actM ((mems k i).map (T24.Md.getD · []))
  | 0, _ => by rw [fixL, mems, List.map_nil, fixMasks_nil]
  | k + 1, i => by
    rw [fixL_succ, mems_succ, List.map_cons, fixMasks_cons', ← fixL_eq_fixMasks k]
    refine List.filter_congr fun m _ => ?_
    rw [Bool.eq_iff_iff, beq_iff_eq, actK_eq]
    exact ⟨Nat.eq_of_beq_eq_true, fun e => by rw [e]; exact Nat.beq_refl _⟩

end CertificateChecks.KernelHMathieu.C7243Orb

end
