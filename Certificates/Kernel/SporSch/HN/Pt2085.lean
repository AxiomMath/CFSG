module

public import Certificates.Kernel.SporSch.HN.Pt2085K
public import Certificates.Kernel.SporSch.HN.Pt2085E
public import Certificates.Kernel.SporSch.HN.Pt2085B
public import Certificates.Kernel.SporSch.HN.FixK.P2085Q0
public import Certificates.Kernel.SporSch.HN.FixK.P2085Q1
public import Certificates.Kernel.SporSch.HN.FixK.P2085Q2
public import Certificates.Kernel.SporSch.HN.FixK.P2085Q3
public import Certificates.Kernel.SporSch.HN.FixK.Spec
public import Certificates.Kernel.SporSch.HN.Pt2109
public import Certificates.Kernel.SporSch.HN.Pt2094
public import CFSG.Sporadic.HNSchreier.Separating
public import CFSG.Sporadic.HNSchreier.FALocal
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSporSch.HNPt2085

open CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS.SporSch CFSG.KS.HNArr CFSG.KS.Ord CFSG.KD.HNPt2085
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier.Native
open CFSG.ONSchreier (ptoLetters)
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.HNArrS
open CertificateChecks.KernelSporSch.HNPt2103 Matrix

local notation "OMat" => ordMat 5 133 13 1729

theorem hWordJ_eq_wJ (w : List ℤ) : hWordJ w = wJ hJ w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [hWordJ_cons, ih, CFSG.KS.HNArr.wJ]
    congr 1
    unfold lJ
    by_cases h : 0 < l
    · rw [if_pos h, if_pos h, show l.toNat = l.natAbs by omega]
    · rw [if_neg h, if_neg h, show (-l).toNat = l.natAbs by omega]

theorem evalWord_eq_wJ (gs : ℕ → JH) {j : ℕ} : ∀ w : List ℤ, plettersOK j w = true →
    Quiver.SchreierGraph.evalWord (fun h : Fin j => gs h) (ptoLetters j w) = wJ gs w
  | [], _ => rfl
  | l :: w, hw => by
    simp only [plettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : plettersOK j w = true := by
      simpa [plettersOK, List.all_eq_true] using hw
    have hcons : ptoLetters j (l :: w) = (⟨l.natAbs - 1, by omega⟩, decide (0 < l)) ::
        ptoLetters j w := by
      simp [ptoLetters, hl0, hlj]
    rw [hcons, CFSG.KS.HNArr.wJ, ← evalWord_eq_wJ gs w hw']
    unfold lJ
    by_cases hpos : 0 < l
    · rw [decide_eq_true hpos, Quiver.SchreierGraph.evalWord_cons_true, if_pos hpos,
        show l.toNat = l.natAbs by omega]
    · rw [show decide (0 < l) = false by simpa using hpos,
        Quiver.SchreierGraph.evalWord_cons_false, if_neg hpos, show (-l).toNat = l.natAbs by omega]

theorem sL_eq_hJ : ∀ j < 17, sL j = hJ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.lt_or_ge j 2 with h | h
    · interval_cases j
      · rw [sL0, hJ_zero]
        rfl
      · rw [sL1, hJ_one]
        rfl
    · have hw := words_lt j h hj
      rw [sL, sJ_two h hw, hJ, gStrong_of_ge _ _ (by simp; omega)]
      change _ = Quiver.SchreierGraph.evalWord (fun i : Fin j => hJ i) _
      rw [evalWord_eq_wJ hJ _ (plettersOK_iff.2 hw)]
      exact wJ_congr (m := j) (fun i hi => ih i hi (by omega)) _ hw

theorem wJ_sL (w : List ℤ) (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 17) : wJ sL w = hWordJ w := by
  rw [hWordJ_eq_wJ]
  exact wJ_congr (m := 17) sL_eq_hJ w hw

theorem seedWordJ_eq : ∀ w : List ℕ, seedWordJ w = seedJ w
  | [] => rfl
  | l :: w => by
    rw [seedWordJ, List.map_cons, List.prod_cons, ← seedWordJ, seedWordJ_eq w, seedJ]

@[expose] noncomputable def iG (k : ℕ) : JH := if k < 5 then aGenJ k else commJ

@[expose] noncomputable def IW (k : ℕ) : ℕ :=
  [CFSG.KD.HNPt2085.I0, CFSG.KD.HNPt2085.I1, CFSG.KD.HNPt2085.I2, CFSG.KD.HNPt2085.I3,
    CFSG.KD.HNPt2085.I4, CFSG.KD.HNPt2085.I5].getD k 0

@[expose] noncomputable def EW (k : ℕ) : ℕ :=
  [CFSG.KD.HNPt2085.E0, CFSG.KD.HNPt2085.E1, CFSG.KD.HNPt2085.E2, CFSG.KD.HNPt2085.E3].getD k 0

theorem codesF : fc = FAData.fWord.map scode ∧ g5c = FAData.g5Root.map (33 + ·) ∧
    ic0 = FAData.aWords[0]!.map scode ∧ ic1 = FAData.aWords[1]!.map scode ∧
    ic2 = FAData.aWords[2]!.map scode ∧ ic3 = FAData.aWords[3]!.map scode ∧
    ic4 = FAData.aWords[4]!.map scode ∧
    ic5 = (HNPt2094.invZ FAData.aWords[0]!).map scode ++ ((HNPt2094.seedInv FAData.g5Root).map (33 + ·) ++
      (FAData.aWords[0]!.map scode ++ FAData.g5Root.map (33 + ·))) ∧
    ec0 = FAData.a6Words[0]!.map scode ∧ ec1 = FAData.a6Words[1]!.map scode ∧
    ec2 = FAData.a6Words[2]!.map scode ∧ ec3 = FAData.a6Words[3]!.map scode ∧
    (∀ c ∈ ic5, c < 36) ∧ (∀ c ∈ g5c, c < 36) ∧ FAData.iCommIdx = 0 := by
  decide +kernel

theorem lettersF : (∀ l ∈ FAData.fWord, l ≠ 0 ∧ l.natAbs ≤ 17) ∧
    (∀ j < 5, ∀ l ∈ FAData.aWords[j]!, l ≠ 0 ∧ l.natAbs ≤ 17) ∧
    (∀ j < 4, ∀ l ∈ FAData.a6Words[j]!, l ≠ 0 ∧ l.natAbs ≤ 17) ∧
    (∀ l ∈ FAData.g5Root, l = 1 ∨ l = 2) ∧
    (∀ l ∈ HNPt2094.invZ FAData.aWords[0]!, l ≠ 0 ∧ l.natAbs ≤ 17) := by
  decide +kernel

theorem word_mat {w : List ℤ} {cs : List ℕ} {W : ℕ}
    (hw : wordC CFSG.KD.HNPt.R cs = W) (hc : cs = w.map scode)
    (hl : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 17) : Canon 5 133 13 W ∧ OMat W = matJ (hWordJ w) := by
  rw [← wJ_sL w hl]
  exact HNPt2109.strong_elem hw hc hl

theorem F_mat :
    Canon 5 133 13 CFSG.KD.HNPt2085.F ∧ OMat CFSG.KD.HNPt2085.F = matJ fJ :=
  word_mat w_F.1 codesF.1 lettersF.1

theorem seed_mat {w : List ℕ} {W : ℕ}
    (hw : wordC CFSG.KD.HNPt.R (w.map (33 + ·)) = W) (hl : ∀ l ∈ w, l = 1 ∨ l = 2)
    (hc : ∀ c ∈ w.map (33 + ·), c < 36) : Canon 5 133 13 W ∧ OMat W = matJ (seedJ w) := by
  rw [← hw, ← prod_seed w hl]
  exact mat_word hc

theorem G5_mat :
    Canon 5 133 13 CFSG.KD.HNPt2085.G5 ∧ OMat CFSG.KD.HNPt2085.G5 = matJ g5J := by
  obtain ⟨-, e, -⟩ := codesF
  obtain ⟨-, -, -, hl, -⟩ := lettersF
  have hc := codesF.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [e] at hc
  have hw := w_F.2
  rw [e] at hw
  rw [g5J, seedWordJ_eq]
  exact seed_mat hw hl hc

theorem comm_eq :
    (((HNPt2094.invZ FAData.aWords[0]!).map scode ++ ((HNPt2094.seedInv FAData.g5Root).map (33 + ·) ++
      (FAData.aWords[0]!.map scode ++ FAData.g5Root.map (33 + ·)))).map genJ).prod = commJ := by
  obtain ⟨-, hla, -, hlg, hli⟩ := lettersF
  obtain ⟨hA, hB⟩ := HNPt2094.seeds_J
  have ha := hla 0 (by norm_num)
  rw [List.map_append, List.map_append, List.map_append, List.prod_append, List.prod_append,
    List.prod_append, prod_scode _ hli, prod_seed _ (HNPt2094.seedInv_letters _), prod_scode _ ha,
    prod_seed _ hlg, HNPt2094.wJ_invZ _ _ fun l hl => (ha l hl).1, ← HNPt2094.seedJ_inv hA hB _ hlg,
    wJ_sL _ ha, commJ, codesF.2.2.2.2.2.2.2.2.2.2.2.2.2.2, g5J, seedWordJ_eq]
  simp only [aGenJ, mul_assoc]

theorem I_mat {k : ℕ} (hk : k < 6) :
    Canon 5 133 13 (IW k) ∧ OMat (IW k) = matJ (iG k) := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := w_I
  obtain ⟨-, -, e0, e1, e2, e3, e4, e5, -, -, -, -, hc5, -⟩ := codesF
  have hl := lettersF.2.1
  interval_cases k
  · exact word_mat a0 e0 (hl 0 (by norm_num))
  · exact word_mat a1 e1 (hl 1 (by norm_num))
  · exact word_mat a2 e2 (hl 2 (by norm_num))
  · exact word_mat a3 e3 (hl 3 (by norm_num))
  · exact word_mat a4 e4 (hl 4 (by norm_num))
  · change Canon 5 133 13 CFSG.KD.HNPt2085.I5 ∧ OMat CFSG.KD.HNPt2085.I5 = matJ commJ
    rw [← a5, ← comm_eq, ← e5]
    exact mat_word hc5

theorem E_mat {k : ℕ} (hk : k < 4) :
    Canon 5 133 13 (EW k) ∧ OMat (EW k) = matJ (hWordJ FAData.a6Words[k]!) := by
  obtain ⟨a0, a1, a2, a3⟩ := w_E
  obtain ⟨-, -, -, -, -, -, -, -, e0, e1, e2, e3, -⟩ := codesF
  have hl := lettersF.2.2.1
  interval_cases k
  · exact word_mat a0 e0 (hl 0 (by norm_num))
  · exact word_mat a1 e1 (hl 1 (by norm_num))
  · exact word_mat a2 e2 (hl 2 (by norm_num))
  · exact word_mat a3 e3 (hl 3 (by norm_num))

theorem iG_lt {k : ℕ} (hk : k < 5) : iG k = aGenJ k := if_pos hk

theorem fJ_comm_aGen {j : ℕ} (hj : j < 5) :
    fJ * aGenJ j = aGenJ j * fJ := by
  rw [← iG_lt hj]
  refine HNPt2109.comm_of F_mat (I_mat (by omega)) ?_
  obtain ⟨c0, c1, c2, c3, c4, -⟩ := cm_F
  interval_cases j
  · exact c0
  · exact c1
  · exact c2
  · exact c3
  · exact c4

theorem fJ_comm_g5 : fJ * g5J = g5J * fJ :=
  HNPt2109.comm_of F_mat G5_mat cm_F.2.2.2.2.2

theorem pts_data : FAData.fFixed.length = 50 ∧ (∀ t < 50, om t = FAData.fFixed.getD t 0) ∧
    (∀ s < 50, ∀ t < 50, om s = om t → s = t) ∧
    (∀ k < 6, lgetL IS k = FAData.iSmall[k]!) ∧ (∀ k < 4, lgetL ES6 k = FAData.a6Small[k]!) ∧
    (∀ c < 4, lget CH c = (chainPt c).val) := by
  decide +kernel

theorem om_lt {t : ℕ} (ht : t < 50) : om t < nPts := pb.2.2.2.1 t ht

theorem img_om {g : JH} {W : ℕ} {J : List ℕ}
    (hW : Canon 5 133 13 W ∧ OMat W = matJ g) (hp : omImg (trM W) J = true)
    (hJ : ∀ t < 50, lget J t < 50) {t : ℕ} (ht : t < 50) : gi g (om t) = om (lget J t) :=
  HNPt2109.gi_fn hW.1 hW.2 hp (fun k hk => ⟨om_lt hk, om_lt (hJ k hk)⟩) ht

theorem iG_om {k t : ℕ} (hk : k < 6) (ht : t < 50) :
    gi (iG k) (om t) = om (lget (lgetL IS k) t) := by
  have hJ := pb.2.2.2.2.1 k hk
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := t_I
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := rs_I
  interval_cases k
  · rw [← b0] at r0
    exact img_om (I_mat (k := 0) (by norm_num)) r0 hJ ht
  · rw [← b1] at r1
    exact img_om (I_mat (k := 1) (by norm_num)) r1 hJ ht
  · rw [← b2] at r2
    exact img_om (I_mat (k := 2) (by norm_num)) r2 hJ ht
  · rw [← b3] at r3
    exact img_om (I_mat (k := 3) (by norm_num)) r3 hJ ht
  · rw [← b4] at r4
    exact img_om (I_mat (k := 4) (by norm_num)) r4 hJ ht
  · rw [← b5] at r5
    exact img_om (I_mat (k := 5) (by norm_num)) r5 hJ ht

theorem E_om {k t : ℕ} (hk : k < 4) (ht : t < 50) :
    gi (hWordJ FAData.a6Words[k]!) (om t) = om (lget (lgetL ES6 k) t) := by
  have hJ := pb.2.2.2.2.2 k hk
  obtain ⟨b0, b1, b2, b3⟩ := t_E
  obtain ⟨r0, r1, r2, r3⟩ := rs_E
  interval_cases k
  · rw [← b0] at r0
    exact img_om (E_mat (k := 0) (by norm_num)) r0 hJ ht
  · rw [← b1] at r1
    exact img_om (E_mat (k := 1) (by norm_num)) r1 hJ ht
  · rw [← b2] at r2
    exact img_om (E_mat (k := 2) (by norm_num)) r2 hJ ht
  · rw [← b3] at r3
    exact img_om (E_mat (k := 3) (by norm_num)) r3 hJ ht

theorem iG_omega {k t : ℕ} (hk : k < 6) (ht : t < 50) :
    gi (iG k) (FAData.fFixed.getD t 0) =
      FAData.fFixed.getD ((FAData.iSmall[k]!).getD t 0) 0 := by
  obtain ⟨-, ho, -, hI, -⟩ := pts_data
  rw [← ho t ht, iG_om hk ht, ← hI k hk]
  exact ho _ (pb.2.2.2.2.1 k hk t ht)

theorem a6_omega {k t : ℕ} (hk : k < 4) (ht : t < 50) :
    gi (hWordJ FAData.a6Words[k]!) (FAData.fFixed.getD t 0) =
      FAData.fFixed.getD ((FAData.a6Small[k]!).getD t 0) 0 := by
  obtain ⟨-, ho, -, -, hE, -⟩ := pts_data
  rw [← ho t ht, E_om hk ht, ← hE k hk]
  exact ho _ (pb.2.2.2.2.2 k hk t ht)

theorem fq (k : ℕ) (hk : k < 8) : CFSG.KD.HNXK.fixOk CFSG.KD.HNPt2085.GF CFSG.KD.HNXK.FIX2085 0 k =
    true := by
  interval_cases k
  · exact CFSG.KD.HNXK.F2085_0.c0
  · exact CFSG.KD.HNXK.F2085_0.c1
  · exact CFSG.KD.HNXK.F2085_1.c0
  · exact CFSG.KD.HNXK.F2085_1.c1
  · exact CFSG.KD.HNXK.F2085_2.c0
  · exact CFSG.KD.HNXK.F2085_2.c1
  · exact CFSG.KD.HNXK.F2085_3.c0
  · exact CFSG.KD.HNXK.F2085_3.c1

theorem tot_F : ∑ b ∈ Finset.range 17813, fixLeaf CFSG.KD.LgHNX.TX 464 CFSG.KD.LgHNX.CM3
    CFSG.KD.LgHNX.M [CFSG.KD.HNPt2085.GF] b (hnxC b) = 50 :=
  (HNPt2109.sum8 (HNPt2109.fixSum_of (fq 0 (by norm_num)) (lo' := 0) (n' := 2227) (by decide)
    (by decide))
    (HNPt2109.fixSum_of (fq 1 (by norm_num)) (lo' := 2227) (n' := 2227) (by decide) (by decide))
    (HNPt2109.fixSum_of (fq 2 (by norm_num)) (lo' := 4454) (n' := 2227) (by decide) (by decide))
    (HNPt2109.fixSum_of (fq 3 (by norm_num)) (lo' := 6681) (n' := 2227) (by decide) (by decide))
    (HNPt2109.fixSum_of (fq 4 (by norm_num)) (lo' := 8908) (n' := 2227) (by decide) (by decide))
    (HNPt2109.fixSum_of (fq 5 (by norm_num)) (lo' := 11135) (n' := 2227) (by decide) (by decide))
    (HNPt2109.fixSum_of (fq 6 (by norm_num)) (lo' := 13362) (n' := 2227) (by decide) (by decide))
    (HNPt2109.fixSum_of (fq 7 (by norm_num)) (lo' := 15589) (n' := 2224) (by decide)
      (by decide))).trans (by decide +kernel)

theorem fix_f {x : ℕ} (hx : x < nPts) :
    gi fJ x = x ↔ x ∈ FAData.fFixed := by
  obtain ⟨hlen, ho, hinj, -⟩ := pts_data
  have hfx : ∀ t < 50, gi fJ (om t) = om t := by
    have h := fx
    rw [← t_F.1] at h
    exact fun t ht => HNPt2109.gi_fn F_mat.1 F_mat.2 h (fun k hk => ⟨om_lt hk, om_lt hk⟩) ht
  have hcard := HNPt2109.card_fix_of F_mat.1 F_mat.2 g_F tot_F
  set Fx := (Finset.range nPts).filter fun i => gi fJ i = i
  have hsub : (Finset.range 50).image om ⊆ Fx := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    have ht' := Finset.mem_range.1 ht
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (om_lt ht'), hfx t ht'⟩
  have himg : ((Finset.range 50).image om).card = 50 := by
    rw [Finset.card_image_of_injOn fun s hs t ht h => hinj s (Finset.mem_range.1 hs) t
      (Finset.mem_range.1 ht) h, Finset.card_range]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, himg])
  have hmem : x ∈ Fx ↔ gi fJ x = x := by
    simp [Fx, Finset.mem_filter, Finset.mem_range, hx]
  rw [← hmem, ← heq, Finset.mem_image, List.mem_iff_getElem]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have ht' := Finset.mem_range.1 ht
    exact ⟨t, by omega, by rw [ho t ht', List.getD_eq_getElem _ _ (by omega)]⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, Finset.mem_range.2 (by omega), by rw [ho t (by omega), List.getD_eq_getElem _ _ ht]⟩

@[expose] noncomputable def evI : List ℕ → JH
  | [] => 1
  | l :: ls => evI ls * iG l

theorem evI_append : ∀ u v : List ℕ, evI (u ++ v) = evI v * evI u
  | [], v => by rw [List.nil_append, evI, mul_one]
  | l :: u, v => by rw [List.cons_append, evI, evI, evI_append u v, mul_assoc]

theorem lget_TIL {l : ℕ} (hl : l < 6) : lget TIL l = trM (IW l) := by
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := t_I
  interval_cases l
  · exact b0.symm
  · exact b1.symm
  · exact b2.symm
  · exact b3.symm
  · exact b4.symm
  · exact b5.symm

theorem edge {l e : ℕ} (he : e < lget EN l) :
    gi (iG l) (src l e) = dst l e := by
  have hl : l < 6 := by
    by_contra h
    have e0 : lget EN l = 0 := List.getD_eq_default _ _ (by rw [pb.1]; omega)
    omega
  have hok : edgeOk l = true := by
    obtain ⟨⟨c0, c1, c2⟩, c3, c4, c5⟩ := And.intro ed_0 ed_3
    interval_cases l
    · exact c0
    · exact c1
    · exact c2
    · exact c3
    · exact c4
    · exact c5
  unfold edgeOk at hok
  rw [lget_TIL hl] at hok
  exact HNPt2109.gi_fn (I_mat hl).1 (I_mat hl).2 hok (fun k hk => eb l hl k hk) he

theorem walk_sound : ∀ (ls es : List ℕ) (p : ℕ) (es' : List ℕ)
    (q : ℕ) (es'' : List ℕ), walk src dst ls es p = some (es', q) → bndW EN ls es = some es'' →
    p < nPts → es'' = es' ∧ gi (evI ls) p = q
  | [], es, p, es', q, es'', h1, h2, hp => by
    rw [walk] at h1
    rw [bndW] at h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h1)
    exact ⟨Option.some.inj h2.symm, by rw [evI, gi_one hp]⟩
  | _ :: _, [], _, _, _, _, h1, _, _ => by
    rw [walk] at h1
    exact absurd h1 (by simp)
  | l :: ls, e :: es, p, es', q, es'', h1, h2, hp => by
    rw [walk] at h1
    rw [bndW] at h2
    cases hs : Nat.beq (src l e) p
    · rw [hs] at h1
      exact absurd h1 (by simp)
    cases hb : Nat.blt e (lget EN l)
    · rw [hb] at h2
      exact absurd h2 (by simp)
    rw [hs, cond_true] at h1
    rw [hb, cond_true] at h2
    have hsp : src l e = p := Nat.eq_of_beq_eq_true hs
    have hd : gi (iG l) p = dst l e := by rw [← hsp]; exact edge (Nat.blt_eq.mp hb)
    have hdl : dst l e < nPts := by rw [← hd]; exact gi_lt _ hp
    obtain ⟨h3, h4⟩ := walk_sound ls es (dst l e) es' q es'' h1 h2 hdl
    exact ⟨h3, by rw [evI, gi_mul _ _ hp, hd, h4]⟩

noncomputable abbrev tJ (x : ℕ) : JH := evI (lgetL TW x)

theorem ids_sound {c : ℕ} (hc : c < nPts) :
    ∀ (ids : List (List ℕ)) (es : List ℕ), idsOk src dst TW IS c ids es = true →
      bndOk EN TW IS ids es = true → ∀ i ∈ ids, ∃ x k w, i = x :: k :: w ∧
        gi (iG k * tJ x) c = gi (tJ (lget (lgetL IS k) x) * evI w) c
  | [], _, _, _, i, hi => absurd hi List.not_mem_nil
  | [] :: _, es, h1, _, _, _ => by
    rw [idsOk] at h1
    · exact absurd h1 (by simp)
    · intro x k w h
      simp at h
  | [_] :: _, es, h1, _, _, _ => by
    rw [idsOk] at h1
    · exact absurd h1 (by simp)
    · intro x k w h
      simp at h
  | (x :: k :: w) :: ids, es, h1, h2, i, hi => by
    rw [idsOk] at h1
    rw [bndOk] at h2
    rcases hw1 : walk src dst (lgetL TW x ++ [k]) es c with _ | ⟨es₁, p⟩
    · rw [hw1] at h1
      exact absurd h1 (by simp)
    rcases hb1 : bndW EN (lgetL TW x ++ [k]) es with _ | fs₁
    · rw [hb1] at h2
      exact absurd h2 (by simp)
    obtain ⟨rfl, hp⟩ := walk_sound _ _ _ _ _ _ hw1 hb1 hc
    rw [hw1] at h1
    rw [hb1] at h2
    dsimp only at h1 h2
    rcases hw2 : walk src dst (w ++ lgetL TW (lget (lgetL IS k) x)) fs₁ c with _ | ⟨es₂, q⟩
    · rw [hw2] at h1
      exact absurd h1 (by simp)
    rcases hb2 : bndW EN (w ++ lgetL TW (lget (lgetL IS k) x)) fs₁ with _ | fs₂
    · rw [hb2] at h2
      exact absurd h2 (by simp)
    obtain ⟨rfl, hq⟩ := walk_sound _ _ _ _ _ _ hw2 hb2 hc
    rw [hw2] at h1
    rw [hb2] at h2
    dsimp only at h1 h2
    simp only [Bool.and_eq_true] at h1
    rcases List.mem_cons.1 hi with rfl | hi
    · refine ⟨x, k, w, rfl, ?_⟩
      rw [evI_append, evI, evI, one_mul] at hp
      rw [evI_append] at hq
      rw [hp, hq]
      exact Nat.eq_of_beq_eq_true h1.1
    · exact ids_sound hc ids fs₂ h1.2 h2 i hi

theorem ids_J {i : List ℕ}
    (hi : i ∈ IDS) : ∃ x k w, i = x :: k :: w ∧
      iG k * tJ x = tJ (lget (lgetL IS k) x) * evI w := by
  obtain ⟨i0, i1, i2, i3⟩ := ids
  obtain ⟨b0, b1, b2, b3⟩ := bnd
  have hch := pts_data.2.2.2.2.2
  have hlt : ∀ c < 4, lget CH c < nPts := fun c hc => by rw [hch c hc]; exact (chainPt c).isLt
  obtain ⟨x, k, w, rfl, h0⟩ := ids_sound (hlt 0 (by norm_num)) _ _ i0 b0 _ hi
  have hall : ∀ c < 4, gi (iG k * tJ x) (lget CH c) =
      gi (tJ (lget (lgetL IS k) x) * evI w) (lget CH c) := by
    intro c hc
    have key : ∀ {es : List ℕ}, idsOk src dst TW IS (lget CH c) IDS es = true →
        bndOk EN TW IS IDS es = true → gi (iG k * tJ x) (lget CH c) =
          gi (tJ (lget (lgetL IS k) x) * evI w) (lget CH c) := fun h1 h2 => by
      obtain ⟨x', k', w', e, h⟩ := ids_sound (hlt c hc) _ _ h1 h2 _ hi
      obtain ⟨rfl, rfl, rfl⟩ : x = x' ∧ k = k' ∧ w = w' := by simpa using e
      exact h
    interval_cases c
    · exact key i0 b0
    · exact key i1 b1
    · exact key i2 b2
    · exact key i3 b3
  refine ⟨x, k, w, rfl, ?_⟩
  have h1 := eq_one_of_fix_chain (h := (tJ (lget (lgetL IS k) x) * evI w)⁻¹ * (iG k * tJ x))
    fun c hc => by
      have hc' := hlt c hc
      apply Fin.ext
      rw [← gi_of_lt _ (chainPt c).isLt, ← hch c hc, gi_mul _ _ hc', hall c hc, ← gi_mul _ _ hc',
        inv_mul_cancel, gi_one hc']
  rw [inv_mul_eq_one] at h1
  exact h1.symm

theorem evI_om : ∀ (ls : List ℕ), (∀ l ∈ ls, l < 6) →
    ∀ p < 50, gi (evI ls) (om p) = om (wordPos IS ls p) ∧ wordPos IS ls p < 50
  | [], _, p, hp => ⟨by rw [evI, gi_one (om_lt hp)]; rfl, hp⟩
  | l :: ls, hl, p, hp => by
    have hl0 := hl l List.mem_cons_self
    have hq := pb.2.2.2.2.1 l hl0 p hp
    obtain ⟨h1, h2⟩ := evI_om ls (fun z hz => hl z (List.mem_cons_of_mem l hz)) _ hq
    exact ⟨by rw [evI, gi_mul _ _ (om_lt hp), iG_om hl0 hp, h1]; rfl, h2⟩

theorem evI_mem : ∀ (w : List ℕ), (∀ l ∈ w, l < 5) →
    evI w ∈ Subgroup.closure (Set.range fun j : Fin 5 => aGenJ j)
  | [], _ => Subgroup.one_mem _
  | l :: w, hw => by
    have hl := hw l List.mem_cons_self
    rw [evI, iG_lt hl]
    exact Subgroup.mul_mem _ (evI_mem w fun z hz => hw z (List.mem_cons_of_mem l hz))
      (Subgroup.subset_closure ⟨⟨l, hl⟩, rfl⟩)

theorem stab_le {g : JH}
    (hg : g ∈ Subgroup.closure (Set.range fun k : Fin 6 => iG k))
    (hfix : gi g (FAData.fFixed.getD 0 0) = FAData.fFixed.getD 0 0) :
    g ∈ Subgroup.closure (Set.range fun j : Fin 5 => aGenJ j) := by
  set K := Subgroup.closure (Set.range fun j : Fin 5 => aGenJ j)
  obtain ⟨-, ho, hinj, -⟩ := pts_data
  have hs := sch
  simp only [schOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, List.any_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨hlen, h0⟩, htw⟩, hcov⟩ := hs
  have ht0 : lgetL TW 0 = [] := List.isEmpty_iff.1 h0
  have htx : ∀ x < 50, gi (tJ x) (om 0) = om x := fun x hx => by
    obtain ⟨hl, hp⟩ := htw x hx
    rw [(evI_om _ (fun l h => hl l h) 0 (by norm_num)).1, hp]
  let P : JH → Prop := fun g => ∀ x < 50, ∃ y < 50, gi g (om x) = om y ∧ (tJ y)⁻¹ * g * tJ x ∈ K
  have hgen : ∀ k < 6, P (iG k) := by
    intro k hk x hx
    have hy := pb.2.2.2.2.1 k hk x hx
    refine ⟨_, hy, iG_om hk hx, ?_⟩
    rcases hcov x hx k hk with he | ⟨i, hi, hhd, hw⟩
    · rw [tJ, he, evI_append, evI, evI, one_mul, _root_.mul_inv_rev, mul_assoc, mul_assoc,
        inv_mul_cancel_left, inv_mul_cancel]
      exact K.one_mem
    · obtain ⟨x', k', w, rfl, hid⟩ := ids_J hi
      obtain ⟨rfl, rfl⟩ : x' = x ∧ k' = k := by simpa using hhd
      rw [mul_assoc, hid, inv_mul_cancel_left]
      exact evI_mem w fun l hl => by simpa using hw l (by simpa using hl)
  have hP : P g := by
    clear hfix
    induction hg using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨k, rfl⟩ := hz
      exact hgen k k.isLt
    | one =>
      intro x hx
      refine ⟨x, hx, gi_one (om_lt hx), ?_⟩
      rw [mul_one, inv_mul_cancel]
      exact K.one_mem
    | mul a b _ _ ha hb =>
      intro x hx
      obtain ⟨y, hy, e1, m1⟩ := hb x hx
      obtain ⟨z, hz, e2, m2⟩ := ha y hy
      refine ⟨z, hz, by rw [gi_mul _ _ (om_lt hx), e1, e2], ?_⟩
      have e : (tJ z)⁻¹ * (a * b) * tJ x = ((tJ z)⁻¹ * a * tJ y) * ((tJ y)⁻¹ * b * tJ x) := by
        group
      rw [e]
      exact K.mul_mem m2 m1
    | inv a _ ha =>
      choose φ hφ e1 _ using fun x : Fin 50 => ha x x.isLt
      have hφi : Function.Injective fun x : Fin 50 => (⟨φ x, hφ x⟩ : Fin 50) := by
        intro s t hst
        have e := congrArg Fin.val hst
        simp only at e
        have e' : gi a (om s) = gi a (om t) := by rw [e1, e1, e]
        have e'' := congrArg (gi a⁻¹) e'
        rw [gi_inv _ (om_lt s.isLt), gi_inv _ (om_lt t.isLt)] at e''
        exact Fin.ext (hinj s s.isLt t t.isLt e'')
      intro x hx
      obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hφi) ⟨x, hx⟩
      have hyx : φ y = x := congrArg Fin.val hy
      obtain ⟨-, -, -, m⟩ := ha y y.isLt
      refine ⟨y, y.isLt, ?_, ?_⟩
      · rw [← hyx, ← e1, gi_inv _ (om_lt y.isLt)]
      · obtain ⟨z, hz, ez, mz⟩ := ha y y.isLt
        have hzx : z = x := by
          rw [← hyx]
          exact hinj z hz (φ y) (hφ y) (by rw [← ez, e1])
        subst hzx
        have e : (tJ y)⁻¹ * a⁻¹ * tJ z = ((tJ z)⁻¹ * a * tJ y)⁻¹ := by group
        rw [e]
        exact K.inv_mem mz
  obtain ⟨y, hy, e, m⟩ := hP 0 (by norm_num)
  rw [← ho 0 (by norm_num)] at hfix
  have hy0 : y = 0 := hinj y hy 0 (by norm_num) (by rw [← e, hfix])
  subst hy0
  rw [tJ, ht0, evI, inv_one, one_mul, mul_one] at m
  exact m

end CertificateChecks.KernelSporSch.HNPt2085

end
