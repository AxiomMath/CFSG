
module

public import Certificates.Kernel.LocalComp.L34Syl3.Chk
public import Certificates.Kernel.LocalComp.L34T1.Glue
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Syl3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KC.L34KSnd CFSG.KC.L34Scan2 CFSG.KC.L34W CertificateChecks.KernelLC.L34X
open CertificateChecks.KernelLC.L34Cert CertificateChecks.KernelLC.L34Para
open CertificateChecks.KernelLC.L34T1
open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.PSL3Four (TabRep allBelow_eq_true)
open CFSG.KLie.CT (andB orB notB)

theorem rU1 : (enumBFS 42 (wordTabs wU₁) 16).tabs = pts 42 6 16 L34SyU1.T ∧
    enumOK 42 (wordTabs wU₁) (enumBFS 42 (wordTabs wU₁) 16) = true ∧
    (∀ i < 16, canonK 42 6 (mask 6) (42 * 6) (L34SyU1.T i) = true) ∧
    GensOK 42 6 4 L34SyU1.G (wordTabs wU₁) :=
  rec_of kU1_gens kU1_hd kU1_sl

theorem rU2 : (enumBFS 42 (wordTabs wU₂) 16).tabs = pts 42 6 16 L34SyU2.T ∧
    enumOK 42 (wordTabs wU₂) (enumBFS 42 (wordTabs wU₂) 16) = true ∧
    (∀ i < 16, canonK 42 6 (mask 6) (42 * 6) (L34SyU2.T i) = true) ∧
    GensOK 42 6 4 L34SyU2.G (wordTabs wU₂) :=
  rec_of kU2_gens kU2_hd kU2_sl

theorem norm_sl {o : Nat} (h : normSl 192 2520 o = true) {r : Nat} (hr : r < 2520) :
    normPt 192 (L34S.T (o + r)) = true := by
  unfold normSl at h
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h r hr
  rw [sapp] at h'
  exact h'

theorem norm_all {i : Nat} (hi : i < 20160) : normPt 192 (L34S.T i) = true := by
  obtain ⟨s, r, hr, rfl⟩ : ∃ s r, r < 2520 ∧ i = 2520 * s + r :=
    ⟨i / 2520, i % 2520, Nat.mod_lt _ (by decide), (Nat.div_add_mod i 2520).symm⟩
  have hs : s < 8 := by omega
  interval_cases s
  · exact norm_sl k22203n0 hr
  · exact norm_sl k22203n1 hr
  · exact norm_sl k22203n2 hr
  · exact norm_sl k22203n3 hr
  · exact norm_sl k22203n4 hr
  · exact norm_sl k22203n5 hr
  · exact norm_sl k22203n6 hr
  · exact norm_sl k22203n7 hr

theorem tab_of_S {i : Nat} (hi : i < 20160) :
    ∃ g : Equiv.Perm (Fin 42), TabRep (unpack 42 6 (L34S.T i)) g := by
  have hE := CFSG.ComponentClassification.PSL3Four.enumerates_closure
    CFSG.ComponentClassification.PSL3Four.gensS_cover
    CFSG.ComponentClassification.PSL3Four.gensS_tabs hS.2
  have e : (enumBFS 42 gensS 20160).tabs[i]! = unpack 42 6 (L34S.T i) := by
    rw [hS.1]
    exact pts_get hi
  obtain ⟨g, -, h⟩ := hE.sound (unpack 42 6 (L34S.T i)) (by
    rw [← e]
    exact CFSG.ComponentClassification.PSL3Four.getElem!_mem (by rw [hS.1, size_pts]; exact hi))
  exact ⟨g, h⟩

theorem inj_of_tab {x : Nat} {g : Equiv.Perm (Fin 42)} (h : TabRep (unpack 42 6 x) g) :
    CFSG.KS.PinvS.InjK 42 6 x := by
  have hx : ∀ a (ha : a < 42), pg 6 (mask 6) x a = (g ⟨a, ha⟩ : ℕ) := fun a ha => by
    rw [← CFSG.KC.BfsPin.unpack_get' ha]
    exact h.apply ⟨a, ha⟩
  refine ⟨fun a ha => ?_, fun a ha b hb e => ?_⟩
  · rw [hx a ha]
    exact (g _).isLt
  · rw [hx a ha, hx b hb] at e
    exact congrArg Fin.val (g.injective (Fin.ext e))

theorem invOK_inj {x : Nat} (cx : Cn x) (hI : CFSG.KS.PinvS.InjK 42 6 x) :
    invOK (unpack 42 6 x) = true := by
  have ci := CFSG.KS.PinvS.canonK_pinvS cx hI
  have hw : (42 : Nat) < 2 ^ 6 := by decide
  refine invOK_of cx ci (eq_of_pg (canonK_pcomp cx ci) (canon_pidn (canon_sz cx)) fun i hi => ?_)
  obtain ⟨a, ha, rfl⟩ := CFSG.KS.PinvS.surj_of_injK hI i hi
  rw [pg_pcomp' cx (canon_lt cx ha), CFSG.KS.PinvS.pg_pinvS hw hI ha,
    pg_pidn' (canon_sz cx) (canon_lt cx ha)]

theorem notIn_of_move {c p : Nat} (hp : p = 2 ∨ p = 23) (hc : pg 6 (mask 6) c p ≠ p) :
    notInK 64 L34PT.T c = true := by
  have hf := k22203f
  unfold fixT at hf
  unfold notInK
  rw [CFSG.KC.BfsPin.strictB_app, CFSG.KS.Raw.Orb.allN_iff]
  intro i hi
  have h := CFSG.KS.Raw.Orb.allN_iff.1 hf i hi
  rw [sapp] at h
  obtain ⟨h2, h23⟩ := andB_iff.1 h
  rw [notB_iff]
  cases e : Nat.beq (L34PT.T i) c
  · rfl
  · exfalso
    rw [Nat.eq_of_beq_eq_true e] at h2 h23
    rcases hp with rfl | rfl
    · exact hc (Nat.eq_of_beq_eq_true h2)
    · exact hc (Nat.eq_of_beq_eq_true h23)

theorem orB_false {a b : Bool} (h : orB a b = false) : a = false ∧ b = false := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

theorem andB_false {a b : Bool} (h : andB a b = false) : a = false ∨ b = false := by
  cases a <;> cases b <;> first | exact Or.inl rfl | exact Or.inr rfl | exact absurd h (by decide)

theorem normT0_true : normT0OK (enumBFS 42 gensS 20160).tabs = true := by
  unfold normT0OK
  dsimp only
  rw [rT.1, rB.1, hS.1, size_pts, size_pts, Bool.and_eq_true]
  refine ⟨beq_self_eq_true _, ?_⟩
  rw [CFSG.KS.BfsReplay.allBelow_iff]
  intro i hi
  have cx := pinS.canon i hi
  obtain ⟨g, hg⟩ := tab_of_S hi
  have hI := inj_of_tab hg
  have h := norm_all hi
  unfold normPt at h
  rw [CFSG.KC.L34Scan.pts_get' hi, invOK_inj cx hI, Bool.true_and, Bool.or_eq_true]
  rcases orB_iff.1 h with h | h
  · right
    obtain ⟨q, hq, hf⟩ := ex_of_notB_allN h
    rw [sapp] at hf
    obtain ⟨hv, hm⟩ := orB_false hf
    have hp : pg 6 (mask 6) (L34S.T i) q = 2 ∨ pg 6 (mask 6) (L34S.T i) q = 23 := by
      rcases andB_false hv with hv | hv
      · exact Or.inl (Nat.eq_of_beq_eq_true (nf_of hv))
      · exact Or.inr (Nat.eq_of_beq_eq_true (nf_of hv))
    have hmove := Nat.ne_of_beq_eq_false hm
    rw [anyBelow_iff, rT.2.2.2.1]
    refine ⟨0, by decide, ?_⟩
    obtain ⟨t0, ct0⟩ := rT.2.2.2.2 0 (by decide)
    have ci := CFSG.KS.PinvS.canonK_pinvS cx hI
    have hw : (42 : Nat) < 2 ^ 6 := by decide
    have ei : invTab 42 (unpack 42 6 (L34S.T i)) =
        unpack 42 6 (pinvS 42 6 (mask 6) (L34S.T i)) :=
      CFSG.KC.BfsPin.invCand_PP ⟨cx, hI⟩
    unfold conjTab
    rw [ei, t0, comp_unpack' cx ct0, comp_unpack' (canonK_pcomp cx ct0) ci]
    refine notIn_sound rfl (canonK_pcomp (canonK_pcomp cx ct0) ci) rT.2.2.1 (notIn_of_move hp ?_)
    rw [pg_pcomp' (canonK_pcomp cx ct0) (canon_lt cx hq), CFSG.KS.PinvS.pg_pinvS hw hI hq,
      pg_pcomp' cx hq]
    intro e
    exact hmove (hI.2 _ (canon_lt ct0 hq) _ hq e)
  · left
    exact found_of_memL h

theorem comm_eq {x g : Nat} (cx : Cn x) (cg : Cn g) :
    (comp 42 (unpack 42 6 x) (unpack 42 6 g) == comp 42 (unpack 42 6 g) (unpack 42 6 x)) =
      commPt 42 6 x g := by
  rw [Bool.eq_iff_iff, beq_iff_eq]
  exact (commPt_iff cx cg).symm

theorem center_true : centerT0OK = true := by
  have hk := k22203c
  unfold centK at hk
  unfold centerT0OK
  rw [CFSG.KS.BfsReplay.allBelow_iff]
  intro k hk64
  have h := CFSG.KS.Raw.Orb.allN_iff.1 hk k hk64
  rw [sapp] at h
  obtain ⟨ct, et⟩ := tgK_eq hG k
  have e : allBelow (wordTabs wT₀).size (fun j => comp 42 (tgT k) (wordTabs wT₀)[j]! ==
      comp 42 (wordTabs wT₀)[j]! (tgT k)) = allN 4 (fun j => commPt 42 6 (tgK L34R.G k)
        (L34PT.G j)) := by
    rw [Bool.eq_iff_iff, rT.2.2.2.1, CFSG.KS.BfsReplay.allBelow_iff, CFSG.KS.Raw.Orb.allN_iff]
    refine forall₂_congr fun j hj => ?_
    obtain ⟨tj, ctj⟩ := rT.2.2.2.2 j hj
    unfold tgT
    rw [et, tj, comm_eq ct ctj]
  rw [e]
  exact h

theorem prod_true : prodOK = true := by
  have hk := k22203p
  unfold prodK at hk
  unfold prodOK
  rw [List.all_eq_true] at hk ⊢
  intro d hd
  have h := hk d hd
  obtain ⟨c1, e1⟩ := tgK_eq hG d.1
  obtain ⟨c2, e2⟩ := tgK_eq hG d.2.1
  obtain ⟨c3, e3⟩ := tgK_eq hG d.2.2
  unfold tgT
  rw [e1, e2, e3, comp_unpack' c1 c2, CFSG.KC.L34KSnd.beq_unpack (canonK_pcomp c1 c2) c3]
  exact h

theorem mem_U {U : Nat → Nat} {a : Nat} (h : memU U a = true) {k : Nat} (hk : k < 16) :
    found (indexOf (pts 42 6 16 U)) (pts 42 6 16 U) (tgT (a * k)) = true := by
  unfold memU at h
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h k hk
  unfold tgT
  rw [(tgK_eq hG (a * k)).2]
  exact found_of_memL h'

theorem invP1 : (∀ j < 3, ((wordTabs wP₁).map (invTab 42))[j]! = unpack 42 6 (pInv1 j)) ∧
    invsOK 42 (wordTabs wP₁) ((wordTabs wP₁).map (invTab 42)) = true :=
  invsOK_of_pcomp r1.2.2.2.1 (fun j hj => (r1.2.2.2.2 j hj).1) fun j hj => by
    obtain ⟨h1, -⟩ := andB_iff.1 (allN' k22203i j hj)
    obtain ⟨c, e⟩ := andB_iff.1 h1
    exact ⟨(r1.2.2.2.2 j hj).2, c, Nat.eq_of_beq_eq_true e⟩

theorem invP2 : (∀ j < 3, ((wordTabs wP₂).map (invTab 42))[j]! = unpack 42 6 (pInv2 j)) ∧
    invsOK 42 (wordTabs wP₂) ((wordTabs wP₂).map (invTab 42)) = true :=
  invsOK_of_pcomp r2.2.2.2.1 (fun j hj => (r2.2.2.2.2 j hj).1) fun j hj => by
    obtain ⟨-, h2⟩ := andB_iff.1 (allN' k22203i j hj)
    obtain ⟨c, e⟩ := andB_iff.1 h2
    exact ⟨(r2.2.2.2.2 j hj).2, c, Nat.eq_of_beq_eq_true e⟩

theorem normal_of {ws us : List (List Nat)} {P PI UG UT : Nat → Nat}
    (hE : (enumBFS 42 (wordTabs us) 16).tabs = pts 42 6 16 UT)
    (hP : GensOK 42 6 3 P (wordTabs ws)) (hU : GensOK 42 6 4 UG (wordTabs us))
    (hI : (∀ j < 3, ((wordTabs ws).map (invTab 42))[j]! = unpack 42 6 (PI j)) ∧
      invsOK 42 (wordTabs ws) ((wordTabs ws).map (invTab 42)) = true)
    (cI : ∀ j < 3, Cn (PI j)) (h : normU P PI UG UT = true) :
    normalOK 42 (enumBFS 42 (wordTabs us) 16).tabs (wordTabs ws)
      ((wordTabs ws).map (invTab 42)) (wordTabs us) = true := by
  unfold normalOK
  dsimp only
  rw [hE, Bool.and_eq_true, allBelow_eq_true]
  refine ⟨hI.2, fun j hj => ?_⟩
  rw [allBelow_eq_true]
  intro i hi
  rw [hP.1] at hj
  rw [hU.1] at hi
  unfold normU at h
  obtain ⟨m1, m2⟩ := andB_iff.1 (allN' (allN' h j hj) i hi)
  obtain ⟨pj, cpj⟩ := hP.2 j hj
  obtain ⟨ui, cui⟩ := hU.2 i hi
  have cpi := cI j hj
  rw [Bool.and_eq_true]
  unfold conjTab
  rw [pj, ui, hI.1 j hj, comp_unpack' cpj cui, comp_unpack' (canonK_pcomp cpj cui) cpi,
    comp_unpack' cpi cui, comp_unpack' (canonK_pcomp cpi cui) cpj]
  exact ⟨found_of_memL m1, found_of_memL m2⟩

open Certificates in
open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts in
theorem facts22203 :
    (normT0OK (enumBFS 42 gensS 20160).tabs && centerT0OK &&
      enumOK 42 (wordTabs wU₁) (enumBFS 42 (wordTabs wU₁) 16) &&
      (enumBFS 42 (wordTabs wU₁) 16).tabs.size == 16 &&
      enumOK 42 (wordTabs wU₂) (enumBFS 42 (wordTabs wU₂) 16) &&
      (enumBFS 42 (wordTabs wU₂) 16).tabs.size == 16 &&
      (allBelow 16 fun k => found (indexOf (enumBFS 42 (wordTabs wU₁) 16).tabs)
        (enumBFS 42 (wordTabs wU₁) 16).tabs (tgT k)) &&
      (allBelow 16 fun k => found (indexOf (enumBFS 42 (wordTabs wU₂) 16).tabs)
        (enumBFS 42 (wordTabs wU₂) 16).tabs (tgT (4 * k))) &&
      normalOK 42 (enumBFS 42 (wordTabs wU₁) 16).tabs (wordTabs wP₁)
        ((wordTabs wP₁).map (invTab 42)) (wordTabs wU₁) &&
      normalOK 42 (enumBFS 42 (wordTabs wU₂) 16).tabs (wordTabs wP₂)
        ((wordTabs wP₂).map (invTab 42)) (wordTabs wU₂) &&
      prodOK) = true := by
  obtain ⟨hm1, hm2⟩ := andB_iff.1 k22203m
  obtain ⟨hn1, hn2⟩ := andB_iff.1 k22203u
  have c1 : ∀ j < 3, Cn (pInv1 j) := fun j hj =>
    (andB_iff.1 (andB_iff.1 (allN' k22203i j hj)).1).1
  have c2 : ∀ j < 3, Cn (pInv2 j) := fun j hj =>
    (andB_iff.1 (andB_iff.1 (allN' k22203i j hj)).2).1
  simp only [Bool.and_eq_true, beq_iff_eq, allBelow_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨normT0_true, center_true⟩, rU1.2.1⟩, by rw [rU1.1, size_pts]⟩, rU2.2.1⟩,
    by rw [rU2.1, size_pts]⟩, ?_⟩, ?_⟩, normal_of rU1.1 r1.2.2.2 rU1.2.2.2 invP1 c1 hn1⟩,
    normal_of rU2.1 r2.2.2.2 rU2.2.2.2 invP2 c2 hn2⟩, prod_true⟩
  · intro k hk
    rw [rU1.1]
    have := mem_U hm1 hk
    rwa [Nat.one_mul] at this
  · intro k hk
    rw [rU2.1]
    exact mem_U hm2 hk

end CertificateChecks.KernelLC.L34Syl3

end
