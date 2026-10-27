module

public import Certificates.Kernel.Misc.Perm.HS100.G5Checks
public import Certificates.Kernel.Misc.Perm.HS100.FiveGlue

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.G5

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
  CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.KC.Misc.ArrEnum (permB pp_of_permB permB_of_pp pp_of_permOK)
open CertificateChecks.KernelMisc.HS100
open CertificateChecks.KernelMisc.HS100.Five (eqA_F hidA pidPP and_of)
open CertificateChecks.KernelMisc.HS100.S0 (cK)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256c CFSG.RankThree.PartTwo.Sec4.Item434SporGen

theorem ppHX {j : ℕ} (hj : j < 15) : PP 100 7 (HX.F j) := by
  rw [Nat.eq_of_beq_eq_true (allN_spec cFS j hj)]
  exact pp_of_permOK sz (allN_spec cperm j hj)

theorem ppG (j : ℕ) : PP 100 7 (GG j) := by
  unfold GG
  split_ifs
  · exact ppHX (by norm_num)
  · exact ppHX (by norm_num)

theorem gs_get : ∀ j < 2, (#[hs100Arr 0, hs100Arr 1] : Array (Array ℕ))[j]! = unpack 100 7 (GG j) := by
  intro j hj
  interval_cases j
  · rw [GG, if_pos rfl, ← hs100Arr_eq 0 (by norm_num)]
    rfl
  · rw [GG, if_neg (by norm_num), ← hs100Arr_eq 1 (by norm_num)]
    rfl

theorem prod_eq {G : ℕ → ℕ} {gs : Array (Array ℕ)} {m : ℕ}
    (hg : ∀ j < m, gs[j]! = unpack 100 7 (G j)) (hp : ∀ j < m, PP 100 7 (G j)) :
    ∀ w : List ℕ, (∀ j ∈ w, j < m) →
      prodN 100 gs w = unpack 100 7 (prodK G w) ∧ PP 100 7 (prodK G w)
  | [], _ => ⟨hidA, pidPP⟩
  | j :: w, h => by
    obtain ⟨e, pw⟩ := prod_eq hg hp w fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hj := h j List.mem_cons_self
    have hpj := hp j hj
    refine ⟨?_, hpj.mul pw⟩
    rw [prodN, e, hg j hj, compA_unpack hpj.1 pw.1]
    rfl

theorem pow_eq {p : ℕ} (hp : PP 100 7 p) : ∀ k,
    powN 100 (unpack 100 7 p) k = unpack 100 7 (powK p k) ∧ PP 100 7 (powK p k)
  | 0 => ⟨hidA, pidPP⟩
  | k + 1 => by
    obtain ⟨e, pk⟩ := pow_eq hp k
    refine ⟨?_, hp.mul pk⟩
    rw [powN, e, compA_unpack hp.1 pk.1]
    rfl

theorem pN_eq {p q : ℕ} (hp : PP 100 7 p) (hq : PP 100 7 q) (ab : ℕ × ℕ) :
    pN 100 (unpack 100 7 p) (unpack 100 7 q) ab = unpack 100 7 (pNK p q ab) ∧
      PP 100 7 (pNK p q ab) := by
  obtain ⟨e1, p1⟩ := pow_eq hp ab.1
  obtain ⟨e2, p2⟩ := pow_eq hq ab.2
  refine ⟨?_, p1.mul p2⟩
  rw [pN, e1, e2, compA_unpack p1.1 p2.1]
  rfl

theorem valid_pp {p : ℕ} (hp : PP 100 7 p) :
    isInvA 100 (unpack 100 7 p) (invCand 100 (unpack 100 7 p)) = true :=
  validA_unpack (permB_of_pp hp)

theorem commN_eq {p q : ℕ} (hp : PP 100 7 p) (hq : PP 100 7 q) :
    commN 100 (unpack 100 7 p) (unpack 100 7 q) = cK p q := by
  rw [commN, compA_unpack hp.1 hq.1, compA_unpack hq.1 hp.1,
    eqA_F (canonK_pcomp hp.1 hq.1) (canonK_pcomp hq.1 hp.1)]
  rfl

theorem letters' : (∀ j ∈ hsG5E1W, j < 2) ∧ (∀ j ∈ hsG5E2W, j < 2) ∧
    (∀ t ∈ hsG5Cls, (∀ j ∈ t.2.2.2, j < 2)) ∧ (∀ w ∈ hsG5WW, ∀ j ∈ w, j < 2) ∧
    (∀ j ∈ hsG5AW, j < 2) ∧ (∀ j ∈ hsG5BW, j < 2) := by
  have h := letters
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_append] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, h4⟩, -⟩, h6⟩, h7⟩ := h
  rw [beq_iff_eq] at h7
  rw [h7] at h6
  exact ⟨fun j hj => h1 j (Or.inl hj), fun j hj => h1 j (Or.inr hj), fun t ht => (h2 t ht).1,
    h4, fun j hj => h6 j (Or.inl hj), fun j hj => h6 j (Or.inr hj)⟩

abbrev gs : Array (Array ℕ) := #[hs100Arr 0, hs100Arr 1]

theorem e1_eq : prodN 100 gs hsG5E1W = unpack 100 7 E1 ∧ PP 100 7 E1 :=
  prod_eq gs_get (fun j _ => ppG j) hsG5E1W letters'.1

theorem e2_eq : prodN 100 gs hsG5E2W = unpack 100 7 E2 ∧ PP 100 7 E2 :=
  prod_eq gs_get (fun j _ => ppG j) hsG5E2W letters'.2.1

theorem ws_get : ∀ j < 2, ((hsG5WW.map (prodN 100 gs)).toArray)[j]! = unpack 100 7 (WK j) := by
  intro j hj
  have hl : j < hsG5WW.length := by rw [show hsG5WW.length = 2 from rfl]; exact hj
  rw [getElem!_pos _ j (by simpa using hl), List.getElem_toArray, List.getElem_map, WK,
    List.getD_eq_getElem _ _ hl]
  exact (prod_eq gs_get (fun j _ => ppG j) _ (letters'.2.2.2.1 _ (List.getElem_mem hl))).1

theorem ppW (j : ℕ) (hj : j < 2) : PP 100 7 (WK j) := by
  have hl : j < hsG5WW.length := by rw [show hsG5WW.length = 2 from rfl]; exact hj
  rw [WK, List.getD_eq_getElem _ _ hl]
  exact (prod_eq gs_get (fun j _ => ppG j) _ (letters'.2.2.2.1 _ (List.getElem_mem hl))).2

theorem e9_true : e9Check 100 (prodN 100 gs hsG5E1W) (prodN 100 gs hsG5E2W) = true := by
  obtain ⟨e1, p1⟩ := e1_eq
  obtain ⟨e2, p2⟩ := e2_eq
  obtain ⟨q13, r13⟩ := pow_eq p1 3
  obtain ⟨q23, r23⟩ := pow_eq p2 3
  obtain ⟨q12, r12⟩ := pow_eq p1 2
  rw [e1, e2]
  unfold e9Check
  rw [valid_pp p1, valid_pp p2, q13, q23, q12, hidA, eqA_F r13.1 pidPP.1, eqA_F r23.1 pidPP.1,
    commN_eq p1 p2, eqA_F p1.1 pidPP.1, eqA_F p2.1 pidPP.1, eqA_F p2.1 p1.1, eqA_F p2.1 r12.1,
    Bool.true_and, Bool.true_and]
  exact e9

theorem cls_true : (hsG5Cls.all fun t => t.2.2.2.all (fun j => decide (j < 2)) &&
    (t.2.2.1 == 1 || t.2.2.1 == 2) &&
    eqA 100 (compA 100 (prodN 100 gs t.2.2.2) (powN 100 (prodN 100 gs hsG5E1W) t.2.2.1))
      (compA 100 (pN 100 (prodN 100 gs hsG5E1W) (prodN 100 gs hsG5E2W) (t.1, t.2.1))
        (prodN 100 gs t.2.2.2))) = true := by
  have hl := letters
  simp only [Bool.and_eq_true, List.all_eq_true] at hl
  obtain ⟨⟨⟨⟨⟨⟨-, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hl
  obtain ⟨e1, p1⟩ := e1_eq
  obtain ⟨e2, p2⟩ := e2_eq
  rw [List.all_eq_true]
  intro t ht
  obtain ⟨ec, pc⟩ := prod_eq gs_get (fun j _ => ppG j) t.2.2.2 (letters'.2.2.1 t ht)
  obtain ⟨es, ps⟩ := pow_eq p1 t.2.2.1
  obtain ⟨en, pn⟩ := pN_eq p1 p2 (t.1, t.2.1)
  have hc := List.all_eq_true.1 cls t ht
  rw [e1, e2, ec, es, en, compA_unpack pc.1 ps.1, compA_unpack pn.1 pc.1,
    eqA_F (canonK_pcomp pc.1 ps.1) (canonK_pcomp pn.1 pc.1), hc,
    List.all_eq_true.2 (h2 t ht).1, (h2 t ht).2]
  rfl

theorem sig_true : sigCheck 100 (hsG5WW.map (prodN 100 gs)).toArray (hsG5WW.map fun _ => 5) hsG5WP
    (prodN 100 gs hsG5E1W) (prodN 100 gs hsG5E2W) = true := by
  obtain ⟨e1, p1⟩ := e1_eq
  obtain ⟨e2, p2⟩ := e2_eq
  unfold sigCheck
  rw [allLt_iff]
  intro i hi
  have hi2 : i < 2 := by
    have : i < hsG5WW.length := by simpa using hi
    exact this
  have h := allN_spec sig i hi2
  have h5 : (hsG5WW.map fun _ => 5).getD i 0 = 5 := by interval_cases i <;> rfl
  obtain ⟨ep, pp⟩ := pow_eq (ppW i hi2) 5
  obtain ⟨en, pn⟩ := pN_eq p1 p2 (hsG5WP.getD i (0, 0))
  rw [ws_get i hi2, h5, e1, e2, ep, en, hidA, eqA_F pp.1 pidPP.1, commN_eq (ppW i hi2) pn,
    eqA_F pn.1 pidPP.1]
  simpa using h

theorem words_true : (eqA 100 (prodN 100 (hsG5WW.map (prodN 100 gs)).toArray hsG5AW) (hs100Arr 0) &&
    eqA 100 (prodN 100 (hsG5WW.map (prodN 100 gs)).toArray hsG5BW) (hs100Arr 1)) = true := by
  obtain ⟨ea, pa⟩ := prod_eq ws_get ppW hsG5AW letters'.2.2.2.2.1
  obtain ⟨eb, pb⟩ := prod_eq ws_get ppW hsG5BW letters'.2.2.2.2.2
  rw [ea, eb, hs100Arr_eq 0 (by norm_num), hs100Arr_eq 1 (by norm_num),
    eqA_F pa.1 (ppHX (j := 0) (by norm_num)).1, eqA_F pb.1 (ppHX (j := 1) (by norm_num)).1]
  exact words

theorem hsGen5Check_true : hsGen5Check = true := by
  have hl := letters
  simp only [Bool.and_eq_true] at hl
  obtain ⟨⟨⟨⟨⟨⟨h1, -⟩, h3⟩, h4⟩, h5⟩, h6⟩, -⟩ := hl
  have v0 := valid_pp (ppG 0)
  have v1 := valid_pp (ppG 1)
  rw [← (gs_get 0 (by norm_num))] at v0
  rw [← (gs_get 1 (by norm_num))] at v1
  have w := words_true
  rw [Bool.and_eq_true] at w
  unfold hsGen5Check gen5Check
  dsimp only
  rw [show (#[hs100Arr 0, hs100Arr 1] : Array (Array ℕ))[0]! = hs100Arr 0 from rfl] at v0
  rw [show (#[hs100Arr 0, hs100Arr 1] : Array (Array ℕ))[1]! = hs100Arr 1 from rfl] at v1
  rw [v0, v1, h1, e9_true, h3, cls_true, h4, h5, sig_true, h6, w.1, w.2]
  rfl

end CertificateChecks.KernelMisc.HS100.G5

end
