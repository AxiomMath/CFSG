
module

public import Certificates.Kernel.L34Cov.CoverTabChecks
public import Certificates.Kernel.L34Cov.CoverIdChecks
public import Certificates.Kernel.L34Cov.Lift22212

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.Certificates.CosetEnumeration CFSG.Certificates.L34Cov CFSG.CosetTable
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.L34W CFSG.KC.L34KSnd
open CertificateChecks.KernelLC.L34Para CertificateChecks.KernelL34W

theorem gT0 : g₁T = unpack 42 6 (GT 0) ∧ Cn (GT 0) := by
  obtain ⟨e, c⟩ := gensG 0 (by norm_num)
  exact ⟨e, c⟩

theorem gT1 : g₂T = unpack 42 6 (GT 1) ∧ Cn (GT 1) := by
  obtain ⟨e, c⟩ := gensG 1 (by norm_num)
  exact ⟨e, c⟩

theorem gT2 : g₃T = unpack 42 6 (GT 2) ∧ Cn (GT 2) := by
  obtain ⟨e, c⟩ := gensG 2 (by norm_num)
  exact ⟨e, c⟩

theorem cn_r4 : Cn r4K := CFSG.KC.BfsPin.canonK_pcomp gT4.2 gT5.2

theorem r4T_eq : r₄T = unpack 42 6 r4K := by
  change comp 42 r₂T r₃T = _
  rw [gT4.1, gT5.1, comp_unpack' gT4.2 gT5.2]
  rfl

theorem wordK_eq (w : List ℕ) :
    Cn (pword (gS GT) w (pidn 42 6)) ∧ wordTab w = unpack 42 6 (pword (gS GT) w (pidn 42 6)) := by
  unfold wordTab
  rw [idTab42]
  exact pword_spec (gS GT) genT w _ cn_pidn fun j _ => genT_gS gensG j

theorem abParts : AB 0 = pword (gS GT) wa (pidn 42 6) ∧ AB 2 = pword (gS GT) wb (pidn 42 6) ∧
    Cn (AB 1) ∧ Cn (AB 3) ∧ pc (AB 0) (AB 1) = pidn 42 6 ∧ pc (AB 2) (AB 3) = pidn 42 6 := by
  have h := ch22201t_ab
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨(Nat.eq_of_beq_eq_true h1).symm, (Nat.eq_of_beq_eq_true h2).symm, h3, h4,
    Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6⟩

theorem aK_eq : Cn (AB 0) ∧ aST = unpack 42 6 (AB 0) := by
  rw [abParts.1]
  exact wordK_eq wa

theorem bK_eq : Cn (AB 2) ∧ bST = unpack 42 6 (AB 2) := by
  rw [abParts.2.1]
  exact wordK_eq wb

theorem aiK_eq : Cn (AB 1) ∧ invTab 42 aST = unpack 42 6 (AB 1) := by
  rw [aK_eq.2]
  exact ⟨abParts.2.2.1, invTab_eq_of_pcomp aK_eq.1 abParts.2.2.1 abParts.2.2.2.2.1⟩

theorem biK_eq : Cn (AB 3) ∧ invTab 42 bST = unpack 42 6 (AB 3) := by
  rw [bK_eq.2]
  exact ⟨abParts.2.2.2.1, invTab_eq_of_pcomp bK_eq.1 abParts.2.2.2.1 abParts.2.2.2.2.2⟩

theorem letK (l : Fin 2 × Bool) :
    Cn (AB (letterCode l)) ∧ letTab l = unpack 42 6 (AB (letterCode l)) := by
  obtain ⟨i, b⟩ := l
  fin_cases i <;> cases b
  · exact aiK_eq
  · exact aK_eq
  · exact biK_eq
  · exact bK_eq

theorem abK_eq (w : List (Fin 2 × Bool)) : Cn (abK w) ∧ abTab w = unpack 42 6 (abK w) := by
  have h := pword_spec AB (fun j => unpack 42 6 (AB j)) (w.map letterCode) (pidn 42 6) cn_pidn
    fun j hj => by
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 hj
      exact ⟨(letK l).1, rfl⟩
  rw [List.foldl_map, ← idTab42] at h
  have hf : (fun t l => comp 42 t (letTab l)) =
      fun x y => comp 42 x (unpack 42 6 (AB (letterCode y))) := by
    funext t l
    rw [(letK l).2]
  refine ⟨h.1, ?_⟩
  unfold abTab abK
  rw [hf]
  exact h.2

theorem cn_cj {g x : ℕ} (hg : Cn g) (hx : Cn x) : Cn (cjK g x) :=
  CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp hg hx) hg

theorem beqU {x y : ℕ} (hx : Cn x) (hy : Cn y) : (unpack 42 6 x == unpack 42 6 y) = Nat.beq x y :=
  beq_unpack hx hy

theorem abOne {w : List (Fin 2 × Bool)} (h : oneK (abK w) = true) :
    (abTab w == idTab 42) = true := by
  rw [(abK_eq w).2, idTab42, beqU (abK_eq w).1 cn_pidn]
  exact h

theorem witOK_of {w : List (Fin 2 × Bool)} {ρ : ℕ} (hρ : Cn ρ) (h : invCK (abK w) ρ = true) :
    witnessOK w (unpack 42 6 ρ) = true := by
  obtain ⟨hc, e⟩ := abK_eq w
  unfold witnessOK
  unfold invCK oneK pc at h
  rw [e, comp_unpack' hc hc, comp_unpack' hc hρ, comp_unpack' hρ hc, idTab42,
    beqU (CFSG.KC.BfsPin.canonK_pcomp hc hc) cn_pidn, beqU hc cn_pidn,
    beqU (CFSG.KC.BfsPin.canonK_pcomp hc hρ) (CFSG.KC.BfsPin.canonK_pcomp hρ hc)]
  exact h

theorem and_s {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem and_t {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]
  rfl

theorem allB {f : ℕ → Bool} (h : ∀ k < 64, f k = true) : allBelow 64 f = true := by
  rw [CFSG.PSL3Four.Native.allBelow, List.all_eq_true]
  intro k hk
  exact h k (List.mem_range.1 hk)

theorem invs22201 : invsOK 42 #[aST, bST] #[invTab 42 aST, invTab 42 bST] = true := by
  have h := (invsOK_of_pcomp (n := 42) (w := 6) (gs := #[aST, bST]) (ng := 2)
    (G := fun k => AB (2 * k)) (GI := fun k => AB (2 * k + 1)) rfl ?_ ?_).2
  · simpa only [List.map_toArray, List.map_cons, List.map_nil] using h
  · intro k hk
    interval_cases k
    · exact aK_eq.2
    · exact bK_eq.2
  · intro k hk
    interval_cases k
    · exact ⟨aK_eq.1, abParts.2.2.1, abParts.2.2.2.2.1⟩
    · exact ⟨bK_eq.1, abParts.2.2.2.1, abParts.2.2.2.2.2⟩

theorem relParts : (∀ r ∈ rels, oneK (abK r) = true) ∧ (∀ r ∈ coverWs, oneK (abK r) = true) ∧
    oneK (abK zOne) = true ∧ oneK (abK zTwo) = true ∧ oneK (abK zThree) = true ∧
    oneK (AB 2) = false := by
  have h := ch22201t_rel
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem relsR : rels.all (fun r => abTab r == idTab 42) = true :=
  List.all_eq_true.2 fun r hr => abOne (relParts.1 r hr)

theorem relsC : coverWs.all (fun r => abTab r == idTab 42) = true :=
  List.all_eq_true.2 fun r hr => abOne (relParts.2.1 r hr)

theorem relsZ :
    (abTab zOne == idTab 42 && abTab zTwo == idTab 42 && abTab zThree == idTab 42) = true := by
  rw [abOne relParts.2.2.1, abOne relParts.2.2.2.1, abOne relParts.2.2.2.2.1]
  rfl

theorem bne22201 : (!(bST == idTab 42)) = true := by
  rw [bK_eq.2, idTab42, beqU bK_eq.1 cn_pidn]
  have h := relParts.2.2.2.2.2
  unfold oneK at h
  rw [h]
  rfl

theorem gens22201 : (abTab (genABWords.getD 0 []) == g₁T && abTab (genABWords.getD 1 []) == g₂T &&
    abTab (genABWords.getD 2 []) == g₃T) = true := by
  have h := ch22201t_gen
  rw [(abK_eq _).2, (abK_eq _).2, (abK_eq _).2, gT0.1, gT1.1, gT2.1, beqU (abK_eq _).1 gT0.2,
    beqU (abK_eq _).1 gT1.2, beqU (abK_eq _).1 gT2.2]
  exact h

theorem aut22201 :
    ((abTab uAU == conjTab 42 r₄T r₄T aST && abTab uBU == conjTab 42 r₄T r₄T bST) &&
      (abTab uAF == conjTab 42 r₂T r₂T aST && abTab uBF == conjTab 42 r₂T r₂T bST) &&
      (abTab uAG == conjTab 42 r₃T r₃T aST && abTab uBG == conjTab 42 r₃T r₃T bST)) = true := by
  have h := ch22201t_aut
  rw [r4T_eq, gT4.1, gT5.1, aK_eq.2, bK_eq.2, conj_unpack cn_r4 aK_eq.1, conj_unpack cn_r4 bK_eq.1,
    conj_unpack gT4.2 aK_eq.1, conj_unpack gT4.2 bK_eq.1, conj_unpack gT5.2 aK_eq.1,
    conj_unpack gT5.2 bK_eq.1, (abK_eq uAU).2, (abK_eq uBU).2, (abK_eq uAF).2, (abK_eq uBF).2,
    (abK_eq uAG).2, (abK_eq uBG).2,
    beqU (abK_eq uAU).1 (cn_cj cn_r4 aK_eq.1), beqU (abK_eq uBU).1 (cn_cj cn_r4 bK_eq.1),
    beqU (abK_eq uAF).1 (cn_cj gT4.2 aK_eq.1), beqU (abK_eq uBF).1 (cn_cj gT4.2 bK_eq.1),
    beqU (abK_eq uAG).1 (cn_cj gT5.2 aK_eq.1), beqU (abK_eq uBG).1 (cn_cj gT5.2 bK_eq.1)]
  obtain ⟨h, h6⟩ := and_s h
  obtain ⟨h, h5⟩ := and_s h
  obtain ⟨h, h4⟩ := and_s h
  obtain ⟨h, h3⟩ := and_s h
  obtain ⟨h1, h2⟩ := and_s h
  exact and_t (and_t (and_t h1 h2) (and_t h3 h4)) (and_t h5 h6)

theorem tw22201 : (allBelow 64 fun k => abTab (tw k) == wordTab (tg k) &&
    found (indexOf (enumBFS 42 (wordTabs wT₀) 64).tabs) (enumBFS 42 (wordTabs wT₀) 64).tabs
      (wordTab (tg k))) = true := by
  rw [rT.1]
  refine allB fun k hk => ?_
  obtain ⟨hc, e⟩ := tgK_eq gensG k
  obtain ⟨h1, h2⟩ := and_s (allN' ch22201t_tw k hk)
  rw [Bool.and_eq_true, e, (abK_eq (tw k)).2, beqU (abK_eq (tw k)).1 hc]
  exact ⟨h1, found_of h2⟩

theorem dist22201 :
    (allBelow 64 fun k => allBelow k fun l => !(wordTab (tg k) == wordTab (tg l))) = true := by
  refine allB fun k hk => ?_
  rw [CFSG.PSL3Four.Native.allBelow, List.all_eq_true]
  intro l hl
  have hl' := List.mem_range.1 hl
  rw [(tgK_eq gensG k).2, (tgK_eq gensG l).2, beqU (tgK_eq gensG k).1 (tgK_eq gensG l).1]
  exact allN' (allN' ch22201t_dist k hk) l hl'

theorem invols22201 : (allBelow 64 fun k => (comp 42 (wordTab (tg k)) (wordTab (tg k)) ==
    idTab 42) == (k == 0 || (sqData.map (·.1)).contains k)) = true := by
  refine allB fun k hk => ?_
  obtain ⟨hc, e⟩ := tgK_eq gensG k
  rw [e, comp_unpack' hc hc, idTab42, beqU (CFSG.KC.BfsPin.canonK_pcomp hc hc) cn_pidn]
  exact allN' ch22201t_inv k hk

theorem r4norm22201 : (allBelow 64 fun k => found (indexOf (enumBFS 42 (wordTabs wT₀) 64).tabs)
    (enumBFS 42 (wordTabs wT₀) 64).tabs (conjTab 42 r₄T r₄T (wordTab (tg k)))) = true := by
  rw [rT.1, r4T_eq]
  refine allB fun k hk => ?_
  obtain ⟨hc, e⟩ := tgK_eq gensG k
  rw [e, conj_unpack cn_r4 hc]
  exact found_of (allN' ch22201t_r4 k hk)

theorem q8_22201 : (allBelow 64 fun k => (comp 42 (wordTab (tg k)) r₄T ==
    comp 42 r₄T (wordTab (tg k))) == q8Idx.contains k) = true := by
  rw [r4T_eq]
  refine allB fun k hk => ?_
  obtain ⟨hc, e⟩ := tgK_eq gensG k
  rw [e, comp_unpack' hc cn_r4, comp_unpack' cn_r4 hc,
    beqU (CFSG.KC.BfsPin.canonK_pcomp hc cn_r4) (CFSG.KC.BfsPin.canonK_pcomp cn_r4 hc)]
  exact allN' ch22201t_q8 k hk

theorem count22201 : (countBelow 64 (fun k => comp 42 (wordTab (tg k))
    (conjTab 42 r₄T r₄T (wordTab (tg k))) == idTab 42) == 8) = true := by
  rw [beq_iff_eq]
  refine Eq.trans ?_ (Nat.eq_of_beq_eq_true ch22201t_c8)
  unfold CFSG.PSL3Four.Native.countBelow
  refine congrArg List.length (List.filter_congr fun k _ => ?_)
  beta_reduce
  obtain ⟨hc, e⟩ := tgK_eq gensG k
  rw [r4T_eq, e, conj_unpack cn_r4 hc, comp_unpack' hc (cn_cj cn_r4 hc), idTab42,
    beqU (CFSG.KC.BfsPin.canonK_pcomp hc (cn_cj cn_r4 hc)) cn_pidn]
  rfl

theorem wit22201 :
    (witnessOK witnessF r₂T && witnessOK witnessG r₃T && witnessOK witnessU r₄T) = true := by
  have h := ch22201t_wit
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [gT4.1, gT5.1, r4T_eq]
  exact ⟨⟨witOK_of gT4.2 h1, witOK_of gT5.2 h2⟩, witOK_of cn_r4 h3⟩

theorem tabs22201 :
    (invsOK 42 #[aST, bST] #[invTab 42 aST, invTab 42 bST] &&
      rels.all (fun r => abTab r == idTab 42) &&
      coverWs.all (fun r => abTab r == idTab 42) &&
      (abTab zOne == idTab 42 && abTab zTwo == idTab 42 && abTab zThree == idTab 42) &&
      !(bST == idTab 42) &&
      (abTab (genABWords.getD 0 []) == g₁T && abTab (genABWords.getD 1 []) == g₂T &&
        abTab (genABWords.getD 2 []) == g₃T) &&
      (abTab uAU == conjTab 42 r₄T r₄T aST && abTab uBU == conjTab 42 r₄T r₄T bST) &&
      (abTab uAF == conjTab 42 r₂T r₂T aST && abTab uBF == conjTab 42 r₂T r₂T bST) &&
      (abTab uAG == conjTab 42 r₃T r₃T aST && abTab uBG == conjTab 42 r₃T r₃T bST) &&
      (allBelow 64 fun k => abTab (tw k) == wordTab (tg k) &&
        found (indexOf (enumBFS 42 (wordTabs wT₀) 64).tabs) (enumBFS 42 (wordTabs wT₀) 64).tabs
          (wordTab (tg k))) &&
      (allBelow 64 fun k => allBelow k fun l => !(wordTab (tg k) == wordTab (tg l))) &&
      (allBelow 64 fun k => (comp 42 (wordTab (tg k)) (wordTab (tg k)) == idTab 42) ==
        (k == 0 || (sqData.map (·.1)).contains k)) &&
      (allBelow 64 fun k => found (indexOf (enumBFS 42 (wordTabs wT₀) 64).tabs)
        (enumBFS 42 (wordTabs wT₀) 64).tabs (conjTab 42 r₄T r₄T (wordTab (tg k)))) &&
      (allBelow 64 fun k => (comp 42 (wordTab (tg k)) r₄T == comp 42 r₄T (wordTab (tg k))) ==
        q8Idx.contains k) &&
      countBelow 64 (fun k => comp 42 (wordTab (tg k)) (conjTab 42 r₄T r₄T (wordTab (tg k))) ==
        idTab 42) == 8 &&
      (witnessOK witnessF r₂T && witnessOK witnessG r₃T && witnessOK witnessU r₄T)) = true := by
  obtain ⟨ha, h9⟩ := and_s aut22201
  obtain ⟨h7, h8⟩ := and_s ha
  exact and_t (and_t (and_t (and_t (and_t (and_t (and_t (and_t (and_t (and_t (and_t (and_t
    (and_t (and_t (and_t invs22201 relsR) relsC) relsZ) bne22201) gens22201) h7) h8) h9)
    tw22201) dist22201) invols22201) r4norm22201) q8_22201) count22201) wit22201

open Certificates in
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four in
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable in
open CFSG.ComponentClassification.GrSLit.L34Facts in
theorem facts22201 :
    (invsOK 42 #[aST, bST] #[invTab 42 aST, invTab 42 bST] &&
      rels.all (fun r => abTab r == idTab 42) &&
      coverWs.all (fun r => abTab r == idTab 42) &&
      (abTab zOne == idTab 42 && abTab zTwo == idTab 42 && abTab zThree == idTab 42) &&
      !(bST == idTab 42) &&
      (abTab (genABWords.getD 0 []) == g₁T && abTab (genABWords.getD 1 []) == g₂T &&
        abTab (genABWords.getD 2 []) == g₃T) &&
      (abTab uAU == conjTab 42 r₄T r₄T aST && abTab uBU == conjTab 42 r₄T r₄T bST) &&
      (abTab uAF == conjTab 42 r₂T r₂T aST && abTab uBF == conjTab 42 r₂T r₂T bST) &&
      (abTab uAG == conjTab 42 r₃T r₃T aST && abTab uBG == conjTab 42 r₃T r₃T bST) &&
      (allBelow 64 fun k => abTab (tw k) == wordTab (tg k) &&
        found (indexOf (enumBFS 42 (wordTabs wT₀) 64).tabs) (enumBFS 42 (wordTabs wT₀) 64).tabs
          (wordTab (tg k))) &&
      (allBelow 64 fun k => allBelow k fun l => !(wordTab (tg k) == wordTab (tg l))) &&
      (allBelow 64 fun k => (comp 42 (wordTab (tg k)) (wordTab (tg k)) == idTab 42) ==
        (k == 0 || (sqData.map (·.1)).contains k)) &&
      (allBelow 64 fun k => found (indexOf (enumBFS 42 (wordTabs wT₀) 64).tabs)
        (enumBFS 42 (wordTabs wT₀) 64).tabs (conjTab 42 r₄T r₄T (wordTab (tg k)))) &&
      (allBelow 64 fun k => (comp 42 (wordTab (tg k)) r₄T == comp 42 r₄T (wordTab (tg k))) ==
        q8Idx.contains k) &&
      countBelow 64 (fun k => comp 42 (wordTab (tg k)) (conjTab 42 r₄T r₄T (wordTab (tg k))) ==
        idTab 42) == 8 &&
      (witnessOK witnessF r₂T && witnessOK witnessG r₃T && witnessOK witnessU r₄T)) = true ∧
    ∀ s ∈ coverSpecs, (PresentedGroup.mk _ (FreeGroup.mk s.1) : PG 2 coverWs) =
      PresentedGroup.mk _ (FreeGroup.mk (zword s.2.1 s.2.2.1 s.2.2.2)) := by
  refine ⟨tabs22201, fun s hs => ?_⟩
  change cv s.1 = cv (zword s.2.1 s.2.2.1 s.2.2.2)
  rw [cv_zword]
  rcases List.mem_append.1 hs with hs | hs
  · rcases List.mem_append.1 hs with hs | hs
    · rcases List.mem_append.1 hs with hs | hs
      · rcases List.mem_append.1 hs with hs | hs
        · rcases List.mem_append.1 hs with hs | hs
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
            rcases hs with rfl | rfl
            · have h : cv (zOne ++ substWord (autWs uAU uBU) zOne) = 1 :=
                (lift_eq ch22201l_U List.mem_cons_self).trans (by norm_num)
              rw [cv_append] at h
              dsimp only
              rw [cv_append, alphaU_eq, pow_zero, pow_zero, pow_zero, mul_one, mul_one]
              exact mul_eq_one_comm.1 h
            · have h : cv (zTwo ++ substWord (autWs uAU uBU) zTwo) = 1 :=
                (lift_eq ch22201l_U (List.mem_cons_of_mem _ List.mem_cons_self)).trans
                  (by norm_num)
              rw [cv_append] at h
              dsimp only
              rw [cv_append, alphaU_eq, pow_zero, pow_zero, pow_zero, mul_one, mul_one]
              exact mul_eq_one_comm.1 h
          · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hs
            exact cv_eq_of_cvId (List.all_eq_true.1 ch22201w_sq d hd)
        · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hs
          exact cv_eq_of_cvId (List.all_eq_true.1 ch22201w_comm d hd)
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hs
        simp only [unitData, List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · dsimp only
          rw [alphaU_eq]
          exact (lift_eq ch22201l_U (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            List.mem_cons_self))).trans (by norm_num)
        · dsimp only
          rw [alphaU_eq]
          exact (lift_eq ch22201l_U (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ List.mem_cons_self)))).trans (by norm_num)
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hs
      exact cv_eq_of_cvId (List.all_eq_true.1 ch22201w_four d hd)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · change cv (FreeGroup.invRev witnessF ++ substWord (autWs uAF uBF) witnessF) = _
      exact (lift_eq ch22201l_F List.mem_cons_self).trans (by norm_num)
    · exact cv_eq_of_cvId ch22201w_wit.1
    · dsimp only
      rw [alphaG_eq]
      exact (lift_eq ch22201l_G List.mem_cons_self).trans (by norm_num)
    · exact cv_eq_of_cvId ch22201w_wit.2.1
    · dsimp only
      rw [alphaU_eq]
      exact (lift_eq ch22201l_U (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))).trans
        (by norm_num)
    · exact cv_eq_of_cvId ch22201w_wit.2.2

end CertificateChecks.KernelL34Cov

end
