module

public import Certificates.Kernel.LocalComp.L34Para.Chk
public import Certificates.Kernel.LocalComp.L34Cert
public import CFSG.Certificates.Kernel.L34DWordSound
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicFacts
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Para

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KC.L34KSnd CFSG.KC.L34Scan CFSG.KC.L34Two CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four CFSG.ComponentClassification.GrSLit.L34Facts
open CertificateChecks.KernelLC.L34Cert
open CFSG.KLie.CT (andB orB notB)

theorem allN' {n : Nat} {f : Nat → Bool} (h : allN n f = true) : ∀ i < n, f i = true :=
  CFSG.KS.Raw.Orb.allN_iff.1 h

theorem lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := Nat.le_of_ble_eq_true h

theorem exists_of_notB_allN {n : Nat} {f : Nat → Bool} (h : notB (allN n f) = true) :
    ∃ k < n, f k = false := by
  rw [notB_iff] at h
  by_contra hc
  push Not at hc
  have : allN n f = true := CFSG.KS.Raw.Orb.allN_iff.2 fun k hk => by
    have := hc k hk
    cases e : f k
    · exact absurd e this
    · rfl
  rw [this] at h
  exact absurd h (by decide)

theorem memK_spec {N x : Nat} {T : Nat → Nat} (h : memK N T x = true) : ∃ q < N, T q = x := by
  obtain ⟨q, hq, h'⟩ := exists_of_notB_allN h
  refine ⟨q, hq, Nat.eq_of_beq_eq_true ?_⟩
  cases e : Nat.beq (T q) x
  · rw [e] at h'
    exact absurd h' (by decide)
  · rfl

theorem rec_of {k cnt : Nat} {gens : Array Tab} {G GI T PL POS SRT SRI : Nat → Nat}
    (hg : gensK gens 42 6 k G = true) (hd : penumHdK (pidn 42 6) cnt cnt T PL = true)
    (hs : penumSlK 42 6 (mask 6) (42 * 6) false G GI k cnt T PL POS SRT SRI 0 cnt = true) :
    (enumBFS 42 gens cnt).tabs = pts 42 6 cnt T ∧ enumOK 42 gens (enumBFS 42 gens cnt) = true ∧
      (∀ i < cnt, canonK 42 6 (mask 6) (42 * 6) (T i) = true) ∧ GensOK 42 6 k G gens := by
  have hp : ∀ i < cnt, penumPtK 42 6 (mask 6) (42 * 6) false G GI k cnt T PL POS SRT SRI i =
      true := fun i hi => penumSl_spec hs i (Nat.zero_le _) (by omega) hi
  have h := penumK_left_sound hsz42 (gensOK_of hg) hd hp
  rw [h.1]
  exact ⟨rfl, h.2, fun i hi => penumPt_canon (hp i hi), gensOK_of hg⟩

theorem rT : (enumBFS 42 (wordTabs wT₀) 64).tabs = pts 42 6 64 L34PT.T ∧
    enumOK 42 (wordTabs wT₀) (enumBFS 42 (wordTabs wT₀) 64) = true ∧
    (∀ i < 64, canonK 42 6 (mask 6) (42 * 6) (L34PT.T i) = true) ∧
    GensOK 42 6 4 L34PT.G (wordTabs wT₀) :=
  rec_of kT_gens kT_hd kT_sl

theorem rB : (enumBFS 42 (wordTabs wB₀) 192).tabs = pts 42 6 192 L34PB.T ∧
    enumOK 42 (wordTabs wB₀) (enumBFS 42 (wordTabs wB₀) 192) = true ∧
    (∀ i < 192, canonK 42 6 (mask 6) (42 * 6) (L34PB.T i) = true) ∧
    GensOK 42 6 3 L34PB.G (wordTabs wB₀) :=
  rec_of kB_gens kB_hd kB_sl

theorem r1 : (enumBFS 42 (wordTabs wP₁) 960).tabs = pts 42 6 960 L34P1.T ∧
    enumOK 42 (wordTabs wP₁) (enumBFS 42 (wordTabs wP₁) 960) = true ∧
    (∀ i < 960, canonK 42 6 (mask 6) (42 * 6) (L34P1.T i) = true) ∧
    GensOK 42 6 3 L34P1.G (wordTabs wP₁) :=
  rec_of kP1_gens kP1_hd kP1_sl

theorem r2 : (enumBFS 42 (wordTabs wP₂) 960).tabs = pts 42 6 960 L34P2.T ∧
    enumOK 42 (wordTabs wP₂) (enumBFS 42 (wordTabs wP₂) 960) = true ∧
    (∀ i < 960, canonK 42 6 (mask 6) (42 * 6) (L34P2.T i) = true) ∧
    GensOK 42 6 3 L34P2.G (wordTabs wP₂) :=
  rec_of kP2_gens kP2_hd kP2_sl

theorem gY : GensOK 42 6 105 L34PR.Y (wordTabs wReps) := gensOK_of kY

theorem canonY {k : Nat} (hk : k < 105) : canonK 42 6 (mask 6) (42 * 6) (L34PR.Y k) = true :=
  (gY.2 k hk).2

theorem invY : (∀ k < 105, ((wordTabs wReps).map (invTab 42))[k]! = unpack 42 6 (L34PR.YI k)) ∧
    invsOK 42 (wordTabs wReps) ((wordTabs wReps).map (invTab 42)) = true :=
  invsOK_of_pcomp gY.1 (fun k hk => (gY.2 k hk).1) fun k hk => by
    obtain ⟨c, e⟩ := andB_iff.1 (allN' kYI k hk)
    exact ⟨canonY hk, c, Nat.eq_of_beq_eq_true e⟩

theorem invB : (∀ j < 3, ((wordTabs wB₀).map (invTab 42))[j]! = unpack 42 6 (bInv j)) ∧
    invsOK 42 (wordTabs wB₀) ((wordTabs wB₀).map (invTab 42)) = true :=
  invsOK_of_pcomp rB.2.2.2.1 (fun j hj => (rB.2.2.2.2 j hj).1) fun j hj => by
    obtain ⟨c, e⟩ := andB_iff.1 (allN' kBI j hj)
    exact ⟨(rB.2.2.2.2 j hj).2, c, Nat.eq_of_beq_eq_true e⟩

theorem found_of {N x : Nat} {T : Nat → Nat} (h : memK N T x = true) :
    found (indexOf (pts 42 6 N T)) (pts 42 6 N T) (unpack 42 6 x) = true := by
  obtain ⟨q, hq, e⟩ := memK_spec h
  exact found_pts hq e

theorem normal_ok : normalOK 42 (enumBFS 42 (wordTabs wT₀) 64).tabs (wordTabs wB₀)
    ((wordTabs wB₀).map (invTab 42)) (wordTabs wT₀) = true := by
  unfold normalOK
  dsimp only
  rw [rT.1, Bool.and_eq_true, allBelow_eq_true]
  refine ⟨invB.2, fun j hj => ?_⟩
  rw [allBelow_eq_true]
  intro i hi
  rw [rB.2.2.2.1] at hj
  rw [rT.2.2.2.1] at hi
  obtain ⟨m1, m2⟩ := andB_iff.1 (allN' (allN' kNorm j hj) i hi)
  obtain ⟨bj, cbj⟩ := rB.2.2.2.2 j hj
  obtain ⟨ti, cti⟩ := rT.2.2.2.2 i hi
  have cbi := (andB_iff.1 (allN' kBI j hj)).1
  rw [Bool.and_eq_true]
  unfold conjTab
  rw [bj, ti, invB.1 j hj, comp_unpack' cbj cti, comp_unpack' (canonK_pcomp cbj cti) cbi,
    comp_unpack' cbi cti, comp_unpack' (canonK_pcomp cbi cti) cbj]
  exact ⟨found_of m1, found_of m2⟩

theorem inP_ok : ∀ j < (wordTabs wB₀).size,
    found (indexOf (enumBFS 42 (wordTabs wP₁) 960).tabs) (enumBFS 42 (wordTabs wP₁) 960).tabs
      (wordTabs wB₀)[j]! = true ∧
    found (indexOf (enumBFS 42 (wordTabs wP₂) 960).tabs) (enumBFS 42 (wordTabs wP₂) 960).tabs
      (wordTabs wB₀)[j]! = true := by
  intro j hj
  rw [rB.2.2.2.1] at hj
  obtain ⟨m1, m2⟩ := andB_iff.1 (allN' kInP j hj)
  rw [r1.1, r2.1, (rB.2.2.2.2 j hj).1]
  exact ⟨found_of m1, found_of m2⟩

theorem cosets_ok : ∀ i < (enumBFS 42 gensS 20160).tabs.size, ∃ k < (wordTabs wReps).size,
    found (indexOf (enumBFS 42 (wordTabs wB₀) 192).tabs) (enumBFS 42 (wordTabs wB₀) 192).tabs
      (comp 42 ((wordTabs wReps).map (invTab 42))[k]! (enumBFS 42 gensS 20160).tabs[i]!) =
        true := by
  intro i hi
  rw [hS.1, size_pts] at hi
  have h := allN' kCos i hi
  simp only [strictB_eq] at h
  obtain ⟨hk, h⟩ := andB_iff.1 h
  obtain ⟨hq, he⟩ := andB_iff.1 h
  have hk' := lt_of_blt hk
  refine ⟨Nat.land (L34PC.C i) 255, by rw [gY.1]; exact hk', ?_⟩
  have cyi := (andB_iff.1 (allN' kYI _ hk')).1
  rw [rB.1, hS.1, invY.1 _ hk', pts_get' hi, comp_unpack' cyi (pinS.canon i hi)]
  exact found_pts (lt_of_blt hq) (Nat.eq_of_beq_eq_true he)

theorem letters {k : Nat} (hk : k < 105) : ∀ a < 4,
    canonK 42 6 (mask 6) (42 * 6) (L34PW.A k a) = true ∧
      ∃ x ∈ Subgroup.closure (wordSet (wB₀ ++ [wReps.getD k []])),
        TabRep (unpack 42 6 (L34PW.A k a)) x := by
  intro a ha
  have hlen : wB₀.length = 3 := rfl
  rcases Nat.lt_or_ge a 3 with h3 | h3
  · have e : L34PW.A k a = L34PB.G a := by
      unfold L34PW.A
      have hb : Nat.blt a 3 = true := Nat.ble_eq_true_of_le h3
      rw [hb]
    rw [e]
    obtain ⟨bj, cbj⟩ := rB.2.2.2.2 a h3
    refine ⟨cbj, wordPerm wB₀[a], Subgroup.subset_closure
      ⟨wB₀[a], List.mem_append_left _ (List.getElem_mem _), rfl⟩, ?_⟩
    rw [← bj]
    exact tabRep_wordTabs wB₀ (by rw [hlen]; exact h3)
  · have e : L34PW.A k a = L34PR.Y k := by
      unfold L34PW.A
      have : Nat.blt a 3 = false := by
        cases hb : Nat.blt a 3
        · rfl
        · exact absurd (lt_of_blt hb) (by omega)
      rw [this]
    rw [e]
    have hkl : k < wReps.length := hk
    refine ⟨canonY hk, wordPerm (wReps.getD k []), Subgroup.subset_closure
      ⟨wReps.getD k [], List.mem_append_right _ (List.mem_singleton_self _), rfl⟩, ?_⟩
    rw [← (gY.2 k hk).1, List.getD_eq_getElem _ _ hkl]
    exact tabRep_wordTabs wReps hkl

theorem gen_S {k e : Nat} (hk : k < 105) (he : e < 96) (hwk : L34PW.WL.getD (4 * e) 0 = k) :
    Subgroup.closure (wordSet (wB₀ ++ [wReps.getD k []])) = S := by
  have h := allN' kWords e he
  simp only [strictB_eq] at h
  have e4 : Nat.mul 4 e = 4 * e := rfl
  rw [e4, hwk] at h
  obtain ⟨-, hw⟩ := andB_iff.1 h
  refine le_antisymm (closure_wordSet_le _) ?_
  have hSdef : S = Subgroup.closure {g₁, g₂, g₃} := rfl
  rw [hSdef, Subgroup.closure_le]
  intro a ha
  obtain ⟨i, hi, hia⟩ := gensS_cover a ha
  have hi3 : i < 3 := hi
  rw [bindS.2 i hi3] at hia
  exact mem_of_dwordK (m := 4) (by decide) (letters hk) hia (allN' hw i hi3)

theorem reps_ok : ∀ k < wReps.length,
    wordPerm (wReps.getD k []) ∈ Subgroup.closure (wordSet wP₁) ∨
      wordPerm (wReps.getD k []) ∈ Subgroup.closure (wordSet wP₂) ∨
      Subgroup.closure (wordSet (wB₀ ++ [wReps.getD k []])) = S := by
  intro k hkl
  have hk : k < 105 := hkl
  have hy : TabRep (unpack 42 6 (L34PR.Y k)) (wordPerm (wReps.getD k [])) := by
    rw [← (gY.2 k hk).1, List.getD_eq_getElem _ _ hkl]
    exact tabRep_wordTabs wReps hkl
  have h := allN' kReps k hk
  rw [orB_iff, orB_iff] at h
  rcases h with h | h | h
  · left
    have hE := enumerates_wordClosure r1.2.1
    rw [r1.1] at hE
    exact mem_of_found_enum hE hy (found_of h)
  · right
    left
    have hE := enumerates_wordClosure r2.2.1
    rw [r2.1] at hE
    exact mem_of_found_enum hE hy (found_of h)
  · right
    right
    obtain ⟨e, he, he'⟩ := exists_of_notB_allN h
    have hb : Nat.beq (L34PW.WL.getD (Nat.mul 4 e) 0) k = true := by
      cases hb : Nat.beq (L34PW.WL.getD (Nat.mul 4 e) 0) k
      · rw [hb] at he'
        exact absurd he' (by decide)
      · rfl
    exact gen_S hk he (Nat.eq_of_beq_eq_true hb)

theorem facts22200 : ParabolicParts where
  okT := rT.2.1
  sizeT := by rw [rT.1, size_pts]
  okB := rB.2.1
  ok₁ := r1.2.1
  size₁ := by rw [r1.1, size_pts]
  ok₂ := r2.2.1
  size₂ := by rw [r2.1, size_pts]
  normal := normal_ok
  inP := inP_ok
  invs := invY.2
  cosets := cosets_ok
  reps := reps_ok

end CertificateChecks.KernelLC.L34Para

end
