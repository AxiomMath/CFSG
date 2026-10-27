module

public import Certificates.Kernel.Sporadic.OddCore.McLTG
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLTK

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin CertificateChecks.KernelCensus
open CertificateChecks.KernelSpor

local notation "⟪" p "⟫" => tabT (unpack 275 9 p)

theorem small : Nat.beq (pc (pc (McLTl.F 0) X) (McLTlI 0)) XI = true ∧ cm (McLTl.F 1) X = true ∧
    (∀ j < 5, cm X (McLTl.F (j + 2)) = true) ∧ (∀ j < 5, cm X (McLTh.F (j + 6)) = true) ∧
    (∀ k < 20, atK McLTR.cnt McLTR.T (r32 McLTQNR k)
      (pc (pc (gxG (Nat.div k 5)) (McLTl.F (Nat.add (Nat.mod k 5) 2))) (gxGI (Nat.div k 5))) =
        true) ∧
    (Nat.beq (pc (pc (McLTl.F 11) X) (McLTlI 11)) X = true ∨
      Nat.beq (pc (pc (McLTl.F 11) X) (McLTlI 11)) XI = true) ∧
    atK McLTR.cnt McLTR.T (r32 McLTQX 0) X = true ∧
    atK McLTR.cnt McLTR.T (r32 McLTQX 1) (McLTl.F 12) = true ∧
    atK McLTR.cnt McLTR.T (r32 McLTQX 2) (McLTl.F 13) = true ∧
    Nat.beq (pc (pc (McLTl.F 12) (McLTl.F 13)) (pc (McLTlI 12) (McLTlI 13))) X = true ∧
    Nat.beq (pc (McLTl.F 14) (McLTl.F 14)) idP = true ∧
    (∀ j < 4, Nat.beq (pc (pc (McLTl.F 14) (McLTl.F (j + 7))) (McLTlI 14)) (McLTlI (j + 7)) =
      true) ∧
    (∀ j < 4, atK McLTC.cnt McLTC.T (r32 McLTQAC j) (McLTl.F (j + 7)) = true) := by
  have h := small_ok
  simp only [Bool.and_eq_true, Bool.or_eq_true, and_assoc] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h
  exact ⟨a1, a2, allN_spec a3, allN_spec a4, allN_spec a5, a6, a7, a8, a9, a10, a11,
    allN_spec a12, allN_spec a13⟩

theorem rKs {i : Nat} (hi : i < 243) :
    canonK 275 9 (mask 9) (275 * 9) (McLTRI i) = true ∧
    invEqK 275 9 (mask 9) (275 * 9) (McLTR.T i) (McLTRI i) = true ∧ cube1 (McLTR.T i) = true ∧
    atK McLTT.cnt McLTT.T (r32 McLTQRT i) (McLTR.T i) = true ∧
    memK 275 9 (mask 9) McLTC.cnt McLTC.T McLTC.HS (McLTR.T i) (lo32 (McLTQRC i))
      (hi32 (McLTQRC i)) = true ∧
    (Nat.blt (lo32 (McLTQRC i)) McLTC.cnt = false ∨ Nat.beq (McLTR.T i) X = true ∨
      Nat.beq (McLTR.T i) XI = true) := by
  have h0 := rA_ok
  simp only [Bool.and_eq_true] at h0
  have h := allN_spec h0.1 i hi
  unfold rK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', and_assoc, or_assoc] at h
  exact h

theorem aKs {i : Nat} (hi : i < 81) : cube1 (McLTA.T i) = true ∧
    atK McLTT.cnt McLTT.T (r32 McLTQAT i) (McLTA.T i) = true ∧
    memK 275 9 (mask 9) McLTR.cnt McLTR.T McLTR.HS (McLTA.T i) (lo32 (McLTQAR i))
      (hi32 (McLTQAR i)) = true := by
  have h0 := aA_ok
  simp only [Bool.and_eq_true] at h0
  have h := allN_spec h0.1 i hi
  unfold aK at h
  simp only [Bool.and_eq_true, and_assoc] at h
  exact h

theorem tKs {i : Nat} (hi : i < 729) :
    atOr McLTR.cnt McLTR.T (lo32 (McLTQS i)) (McLTT.T i)
      (absK 275 9 (mask 9) McLTT.cnt McLTT.T McLTT.HS
        (pc (pc (McLTlI 11) (McLTT.T i)) (McLTl.F 11)) (hi32 (McLTQS i))) = true ∧
    Nat.blt (lo32 (McLTQRA i)) McLTR.cnt = true ∧
    atK McLTA.cnt McLTA.T (hi32 (McLTQRA i)) (pc (McLTRI (lo32 (McLTQRA i))) (McLTT.T i)) = true ∧
    atOr McLTR.cnt McLTR.T (lo32 (McLTQO i)) (McLTT.T i)
      (atOr McLTA.cnt McLTA.T (hi32 (McLTQO i)) (McLTT.T i) (!cube1 (McLTT.T i))) = true ∧
    memK 275 9 (mask 9) McLTC.cnt McLTC.T McLTC.HS (McLTT.T i) (lo32 (McLTQTC i))
      (hi32 (McLTQTC i)) = true ∧
    (!Nat.blt (lo32 (McLTQTC i)) McLTC.cnt ||
      atK McLTA.cnt McLTA.T (hi32 (McLTQO i)) (McLTT.T i)) = true ∧
    atOr McLTA.cnt McLTA.T (hi32 (McLTQO i)) (McLTT.T i)
      (Nat.ble (cntBelowK McLTA.cnt (fun k => cm (McLTT.T i) (McLTA.T k)) 2) 9) = true := by
  have h := tKe_of hi
  unfold tKe at h
  simp only [Bool.and_eq_true, and_assoc] at h
  exact h

theorem rgen {j : Nat} (hj : j < 5) (h : j < rGens3.size) :
    rGens3[j] = ⟪McLTl.F (j + 2)⟫ := by
  have hx := (rG_tabs.2 j hj).1
  rw [getElem!_pos rGens3 j h, (rG hj).2] at hx
  exact hx

theorem agen {j : Nat} (hj : j < 4) (h : j < aGens3.size) :
    aGens3[j] = ⟪McLTl.F (j + 7)⟫ := by
  have hx := (aG_tabs.2 j hj).1
  rw [getElem!_pos aGens3 j h, (aG hj).2] at hx
  exact hx

theorem tgen {g : Table} (hg : g ∈ sylowThreeGens) :
    ∃ j < 5, g = ⟪McLTh.F (j + 6)⟫ ∧ canonK 275 9 (mask 9) (275 * 9) (McLTh.F (j + 6)) = true := by
  obtain ⟨j, hj, e, hc⟩ := TabsOK_list sylT_tabs hg
  rw [(tG hj).2] at e hc
  exact ⟨j, hj, e, hc⟩

theorem rgen_all {f : Table → Bool} (h : ∀ j < 5, f ⟪McLTl.F (j + 2)⟫ = true) :
    rGens3.all f = true := by
  rw [Array.all_eq_true]
  intro j hj
  have hj' : j < 5 := by rw [← rG_tabs.1]; exact hj
  rw [rgen hj' hj]
  exact h j hj'

theorem agen_all {f : Table → Bool} (h : ∀ j < 4, f ⟪McLTl.F (j + 7)⟫ = true) :
    aGens3.all f = true := by
  rw [Array.all_eq_true]
  intro j hj
  have hj' : j < 4 := by rw [← aG_tabs.1]; exact hj
  rw [agen hj' hj]
  exact h j hj'

theorem tgen_all {f : Table → Bool} (h : ∀ j < 5, f ⟪McLTh.F (j + 6)⟫ = true) :
    sylowThreeGens.all f = true := by
  rw [List.all_eq_true]
  intro g hg
  obtain ⟨j, hj, rfl, -⟩ := tgen hg
  exact h j hj

theorem rgen_all_eq {f : Table → Bool} {q : Bool} (h : q = true ↔ ∀ j < 5, f ⟪McLTl.F (j + 2)⟫ = true) :
    rGens3.all f = q := by
  rw [Bool.eq_iff_iff, h, Array.all_eq_true]
  constructor
  · intro ha j hj
    have hs : j < rGens3.size := by rw [rG_tabs.1]; exact hj
    rw [← rgen hj hs]
    exact ha j hs
  · intro ha j hj
    have hj' : j < 5 := by rw [← rG_tabs.1]; exact hj
    rw [rgen hj' hj]
    exact ha j hj'

theorem tgen_all_eq {f : Table → Bool} {q : Bool} (h : q = true ↔ ∀ j < 5, f ⟪McLTh.F (j + 6)⟫ = true) :
    sylowThreeGens.all f = q := by
  rw [Bool.eq_iff_iff, h, List.all_eq_true]
  constructor
  · intro ha j hj
    refine ha _ ?_
    rw [← th_tab (by omega)]
    simp only [sylowThreeGens, List.mem_map, List.mem_range]
    exact ⟨j, hj, rfl⟩
  · intro ha g hg
    obtain ⟨j, hj, rfl, -⟩ := tgen hg
    exact ha j hj

theorem threeEnum_ok : threeEnumCheck = true := by
  obtain ⟨e, ht, hd⟩ := eC
  unfold threeEnumCheck
  simp only [Bool.and_eq_true]
  rw [e]
  have hx := th_tab (k := 0) (by norm_num)
  obtain ⟨x1, x2, x3⟩ := thF (k := 0) (by norm_num)
  refine ⟨⟨⟨⟨⟨⟨⟨⟨subT, subR⟩, subA⟩, ?_⟩, ?_⟩, ?_⟩, ht⟩, hd⟩, ?_⟩
  · refine allInH_of fun l _ hl => ?_
    have hl' : l < 2 := hl
    rw [(pg_tabs.2 l hl').1, (pgi_tabs.2 l hl').1]
    exact invOK_unpack (pgF hl').2.1 (pgF hl').2.2.1 (pgF hl').2.2.2
  · rw [hx]
    exact permOK_unpack x1 x3
  · rw [hx, inv_tab x3]
    exact invOK_unpack x1 x2 x3
  · rw [hRec_size, cC]
    exact beq_self_eq_true _

theorem gx_ok : gxCheck = true := by
  obtain ⟨x1, x2, x3⟩ := thF (k := 0) (by norm_num)
  obtain ⟨h1, h2, h3⟩ := tlF (k := 0) (by norm_num)
  obtain ⟨o1, o2, o3⟩ := tlF (k := 1) (by norm_num)
  obtain ⟨u1, -, u3⟩ := outF
  unfold gxCheck invHTab outerOTab
  rw [th_tab (k := 0) (by norm_num), tl_tab (k := 0) (by norm_num), tl_tab (k := 1) (by norm_num),
    out_tab, inv_tab x3, inv_tab h3, inv_tab o3, conjT_unpack h1 h2 x1, tblEq_unpack
      (canonK_pcomp (canonK_pcomp h1 x1) h2) x2, commTT_unpack o1 x1, sift_eq' h1, sift_eq' o1,
    compT_unpack o1 u1, sift_eq' (canonK_pcomp o1 u1)]
  simp only [Bool.and_eq_true, Bool.not_eq_true', and_assoc]
  exact ⟨permOK_unpack x1 x3, invOK_unpack x1 x2 x3, permOK_unpack u1 u3, permOK_unpack h1 h3,
    invOK_unpack h1 h2 h3, sifts.2.2.2.1, small.1, permOK_unpack o1 o3, invOK_unpack o1 o2 o3,
    small.2.1, sifts.2.2.2.2.1, sifts.2.2.2.2.2.1⟩

theorem rInT_ok : rInTCheck = true := by
  obtain ⟨x1, -, -⟩ := thF (k := 0) (by norm_num)
  unfold rInTCheck
  rw [eR.1, eT.1, eA.1]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨all_rec fun i hi => mem_at (rKs (by rw [← cR]; exact hi)).2.2.2.1,
    all_rec fun i hi => mem_at (aKs (by rw [← cA]; exact hi)).2.1⟩, ?_⟩, ?_⟩
  · rw [th_tab (k := 0) (by norm_num)]
    refine rgen_all fun j hj => ?_
    rw [commTT_unpack x1 (tlF (by omega)).1]
    exact small.2.2.1 j hj
  · rw [th_tab (k := 0) (by norm_num)]
    refine tgen_all fun j hj => ?_
    rw [commTT_unpack x1 (thF (by omega)).1]
    exact small.2.2.2.1 j hj

theorem gxGens_eq : gxGens = #[⟪gxG 0⟫, ⟪gxG 1⟫, ⟪gxG 2⟫, ⟪gxG 3⟫] := by
  unfold gxGens cpGens3 invHTab
  rw [th_tab (k := 0) (by norm_num), th_tab (k := 1) (by norm_num), th_tab (k := 2) (by norm_num),
    tl_tab (k := 0) (by norm_num)]
  rfl

theorem gxF {c : Nat} (hc : c < 4) : canonK 275 9 (mask 9) (275 * 9) (gxG c) = true ∧
    canonK 275 9 (mask 9) (275 * 9) (gxGI c) = true ∧
    invEqK 275 9 (mask 9) (275 * 9) (gxG c) (gxGI c) = true := by
  interval_cases c
  · exact thF (k := 0) (by norm_num)
  · exact thF (k := 1) (by norm_num)
  · exact thF (k := 2) (by norm_num)
  · exact tlF (k := 0) (by norm_num)

theorem gx_all {f : Table → Bool} (h : ∀ c < 4, f ⟪gxG c⟫ = true) : gxGens.all f = true := by
  rw [gxGens_eq, Array.all_eq_true]
  intro c hc
  have hc' : c < 4 := by simpa using hc
  interval_cases c
  · exact h 0 (by norm_num)
  · exact h 1 (by norm_num)
  · exact h 2 (by norm_num)
  · exact h 3 (by norm_num)

theorem rNormal_ok : rNormalCheck = true := by
  unfold rNormalCheck
  rw [eR.1]
  simp only [Bool.and_eq_true]
  refine ⟨gx_all fun c hc => ?_, gx_all fun c hc => rgen_all fun r hr => ?_⟩
  · obtain ⟨c1, c2, c3⟩ := gxF hc
    rw [inv_tab c3]
    simp only [Bool.and_eq_true]
    exact ⟨permOK_unpack c1 c3, invOK_unpack c1 c2 c3⟩
  · obtain ⟨c1, c2, c3⟩ := gxF hc
    rw [inv_tab c3, conjT_unpack c1 c2 (tlF (by omega)).1]
    have h := small.2.2.2.2.1 (c * 5 + r) (by omega)
    have e1 : Nat.div (c * 5 + r) 5 = c := (div_mod_pair hr).1
    have e2 : Nat.mod (c * 5 + r) 5 = r := (div_mod_pair hr).2
    rw [e1, e2] at h
    exact mem_at h

theorem sylowInt_ok : sylowIntCheck = true := by
  obtain ⟨x1, x2, x3⟩ := thF (k := 0) (by norm_num)
  obtain ⟨g1, g2, g3⟩ := tlF (k := 11) (by norm_num)
  unfold sylowIntCheck conjGTab
  rw [eT.1, eR.1, th_tab (k := 0) (by norm_num), tl_tab (k := 11) (by norm_num), inv_tab g3,
    inv_tab x3, conjT_unpack g1 g2 x1, tblEq_unpack (canonK_pcomp (canonK_pcomp g1 x1) g2) x1,
    tblEq_unpack (canonK_pcomp (canonK_pcomp g1 x1) g2) x2, sift_eq' g1]
  simp only [Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨⟨⟨⟨permOK_unpack g1 g3, invOK_unpack g1 g2 g3⟩, sifts.2.2.2.2.2.2.1⟩, small.2.2.2.2.2.1⟩,
    all_rec fun i hi => ?_⟩
  have hi' : i < 729 := by rw [← cT]; exact hi
  have hc := tT i hi
  rw [conjT_unpack g2 g1 hc]
  rcases mem_atOr (PL := McLTR.PL) (tKs hi').1 with h | h
  · rw [h, Bool.or_true]
  · rw [memT_absK tT (canonK_pcomp (canonK_pcomp g2 hc) g1) (slice_hs recT.2.1) h]
    rfl

theorem beq_of {a b : Nat} (h : Nat.beq a b = true) : (a == b) = true := by
  rw [beq_iff_eq]
  exact Nat.eq_of_beq_eq_true h

theorem rZ_eq {i : Nat} (hi : i < McLTR.cnt) : rGens3.all (commTT 275 ⟪McLTR.T i⟫) = rZ i :=
  rgen_all_eq (by
    unfold rZ
    rw [allN_iff]
    refine forall_congr' fun j => imp_congr_right fun hj => ?_
    rw [commTT_unpack (tR i hi) (tlF (by omega)).1]
    rfl)

theorem tZ_eq {i : Nat} (hi : i < McLTT.cnt) :
    sylowThreeGens.all (commTT 275 ⟪McLTT.T i⟫) = tZ i :=
  tgen_all_eq (by
    unfold tZ
    rw [allN_iff]
    refine forall_congr' fun j => imp_congr_right fun hj => ?_
    rw [commTT_unpack (tT i hi) (thF (by omega)).1]
    rfl)

theorem rStruct_ok : rStructCheck = true := by
  obtain ⟨x1, x2, x3⟩ := thF (k := 0) (by norm_num)
  obtain ⟨a1, a2, a3⟩ := tlF (k := 12) (by norm_num)
  obtain ⟨b1, b2, b3⟩ := tlF (k := 13) (by norm_num)
  have h0 := rA_ok
  simp only [Bool.and_eq_true] at h0
  unfold rStructCheck commATab commBTab
  rw [eR.1, th_tab (k := 0) (by norm_num), tl_tab (k := 12) (by norm_num),
    tl_tab (k := 13) (by norm_num), inv_tab x3, inv_tab a3, inv_tab b3, compT_unpack a1 b1,
    compT_unpack a2 b2, compT_unpack (canonK_pcomp a1 b1) (canonK_pcomp a2 b2),
    tblEq_unpack (canonK_pcomp (canonK_pcomp a1 b1) (canonK_pcomp a2 b2)) x1]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, mem_at small.2.2.2.2.2.2.1⟩, ?_⟩, permOK_unpack a1 a3⟩,
    permOK_unpack b1 b3⟩, mem_at small.2.2.2.2.2.2.2.1⟩, mem_at small.2.2.2.2.2.2.2.2.1⟩,
    invOK_unpack a1 a2 a3⟩, invOK_unpack b1 b2 b3⟩, small.2.2.2.2.2.2.2.2.2.1⟩
  · refine all_rec fun i hi => ?_
    obtain ⟨r1, r2, -⟩ := rKs (by rw [← cR]; exact hi)
    rw [inv_tab r2]
    exact invOK_unpack (tR i hi) r1 r2
  · refine all_rec fun i hi => ?_
    rw [cube_eq (tR i hi)]
    exact (rKs (by rw [← cR]; exact hi)).2.2.1
  · rw [len_rec (q := rZ) (hi := 4) (by rw [cR]; norm_num) fun i hi => rZ_eq hi]
    exact beq_of h0.2
  · refine all_rec fun i hi => all_rec fun j hj => ?_
    have hi' : i < 243 := by rw [← cR]; exact hi
    have hj' : j < 243 := by rw [← cR]; exact hj
    obtain ⟨p1, p2, -⟩ := rKs hi'
    obtain ⟨q1, q2, -⟩ := rKs hj'
    have hc := canonK_pcomp (canonK_pcomp (tR i hi) (tR j hj)) (canonK_pcomp p1 q1)
    rw [inv_tab p2, inv_tab q2, compT_unpack (tR i hi) (tR j hj), compT_unpack p1 q1,
      compT_unpack (canonK_pcomp (tR i hi) (tR j hj)) (canonK_pcomp p1 q1), hid,
      tblEq_unpack hc hidc, tblEq_unpack hc x1, tblEq_unpack hc x2]
    exact pAll i hi' j hj'

theorem aStruct_ok : aStructCheck = true := by
  have hA := aA_ok
  simp only [Bool.and_eq_true] at hA
  have hTc := tCnt_ok
  simp only [Bool.and_eq_true] at hTc
  unfold aStructCheck
  rw [eR.1, eA.1, eT.1, eC.1]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · refine all_rec fun i hi => ?_
    obtain ⟨r1, r2, -⟩ := rKs (by rw [← cR]; exact hi)
    rw [inv_tab r2]
    exact invOK_unpack (tR i hi) r1 r2
  · refine all_rec fun i hi => all_rec fun j hj => ?_
    rw [commTT_unpack (tA i hi) (tA j hj)]
    exact allN_spec (allN_spec aa_ok i (by rw [← cA]; exact hi)) j (by rw [← cA]; exact hj)
  · refine all_rec fun i hi => ?_
    rw [cube_eq (tA i hi)]
    exact (aKs (by rw [← cA]; exact hi)).1
  · rw [len_rec (q := aR) (hi := 2) (by rw [cA]; norm_num) fun i hi =>
      memT_memK tR (tA i hi) (slice_hs recR.2.1) (aKs (by rw [← cA]; exact hi)).2.2]
    exact beq_of hA.2
  · refine all_rec fun i hi => ?_
    have hi' : i < 729 := by rw [← cT]; exact hi
    obtain ⟨-, k2, k3, -⟩ := tKs hi'
    rw [Array.any_eq_true]
    have hr : lo32 (McLTQRA i) < McLTR.cnt := Nat.blt_eq.mp k2
    refine ⟨lo32 (McLTQRA i), by simpa [hRec] using hr, ?_⟩
    simp only [hRec, Array.getElem_ofFn]
    obtain ⟨r1, r2, -⟩ := rKs (by rw [← cR]; exact hr)
    rw [inv_tab r2, compT_unpack r1 (tT i hi)]
    exact mem_at (PL := McLTA.PL) k3
  · refine all_rec fun i hi => ?_
    have hi' : i < 729 := by rw [← cT]; exact hi
    obtain ⟨-, -, -, k4, -⟩ := tKs hi'
    rcases mem_atOr (PL := McLTR.PL) k4 with h | h
    · rw [h, Bool.or_true, Bool.true_or]
    rcases mem_atOr (PL := McLTA.PL) h with h' | h'
    · rw [h', Bool.or_true]
    · rw [Bool.not_eq_true'] at h'
      rw [ord3_false (tT i hi) h']
      rfl
  · exact agen_all fun j hj => mem_at (small.2.2.2.2.2.2.2.2.2.2.2.2 j hj)
  · refine all_rec fun i hi => ?_
    have hi' : i < 729 := by rw [← cT]; exact hi
    obtain ⟨-, -, -, -, k5, k6, -⟩ := tKs hi'
    rw [memT_memK tC' (tT i hi) c_hs k5]
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at k6 ⊢
    rcases k6 with h | h
    · exact Or.inl h
    · exact Or.inr (mem_at h)
  · rw [len_rec (q := tC) (hi := 12) (by rw [cT]; norm_num) fun i hi =>
      memT_memK tC' (tT i hi) c_hs (tKs (by rw [← cT]; exact hi)).2.2.2.2.1]
    exact beq_of hTc.1

theorem aInv_ok : aInvCheck = true := by
  obtain ⟨s1, s2, s3⟩ := tlF (k := 14) (by norm_num)
  obtain ⟨u1, -, u3⟩ := outF
  unfold aInvCheck sigmaTab
  rw [tl_tab (k := 14) (by norm_num), out_tab, inv_tab s3, sift_eq' s1, compT_unpack s1 u1,
    sift_eq' (canonK_pcomp s1 u1), compT_unpack s1 s1, hid, tblEq_unpack (canonK_pcomp s1 s1) hidc]
  simp only [Bool.and_eq_true, Bool.not_eq_true', and_assoc]
  refine ⟨permOK_unpack s1 s3, invOK_unpack s1 s2 s3, permOK_unpack u1 u3,
    sifts.2.2.2.2.2.2.2.1, sifts.2.2.2.2.2.2.2.2, small.2.2.2.2.2.2.2.2.2.2.1,
    agen_all fun j hj => ?_⟩
  obtain ⟨a1, -, a3⟩ := tlF (k := j + 7) (by omega)
  rw [inv_tab a3, conjT_unpack s1 s2 a1, tblEq_unpack (canonK_pcomp (canonK_pcomp s1 a1) s2)
    (tlF (k := j + 7) (by omega)).2.1]
  exact small.2.2.2.2.2.2.2.2.2.2.2.1 j hj

theorem weak_ok : weakCheck = true := by
  obtain ⟨x1, x2, x3⟩ := thF (k := 0) (by norm_num)
  unfold weakCheck
  rw [eR.1, eC.1, th_tab (k := 0) (by norm_num), inv_tab x3]
  refine all_rec fun i hi => ?_
  have hi' : i < 243 := by rw [← cR]; exact hi
  obtain ⟨-, -, -, -, k5, k6⟩ := rKs hi'
  rw [memT_memK tC' (tR i hi) c_hs k5, tblEq_unpack (tR i hi) x1, tblEq_unpack (tR i hi) x2]
  simp only [Bool.or_eq_true, Bool.not_eq_true']
  rcases k6 with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem thompson_ok : thompsonCheck = true := by
  have hTc := tCnt_ok
  simp only [Bool.and_eq_true] at hTc
  unfold thompsonCheck
  rw [eT.1, eA.1]
  simp only [Bool.and_eq_true]
  refine ⟨all_rec fun i hi => ?_, ?_⟩
  · have hi' : i < 729 := by rw [← cT]; exact hi
    obtain ⟨-, -, -, -, -, -, k7⟩ := tKs hi'
    rcases mem_atOr (PL := McLTA.PL) k7 with h | h
    · rw [h, Bool.true_or]
    · rw [len_rec (q := fun k => cm (McLTT.T i) (McLTA.T k)) (hi := 2) (by rw [cA]; norm_num)
        fun k hk => commTT_unpack (tT i hi) (tA k hk), h, Bool.or_true]
  · have e : (fun e => sylowThreeGens.toArray.all (commTT 275 e)) =
        fun e => sylowThreeGens.all (commTT 275 e) := by
      funext e
      exact List.all_toArray
    rw [e, len_rec (q := tZ) (hi := 12) (by rw [cT]; norm_num) fun i hi => tZ_eq hi]
    exact beq_of hTc.2

theorem threeLocal_ok : threeEnumCheck = true ∧ gxCheck = true ∧ rInTCheck = true ∧
    rNormalCheck = true ∧ sylowIntCheck = true ∧ rStructCheck = true ∧ aStructCheck = true ∧
    aInvCheck = true ∧ weakCheck = true ∧ thompsonCheck = true :=
  ⟨threeEnum_ok, gx_ok, rInT_ok, rNormal_ok, sylowInt_ok, rStruct_ok, aStruct_ok, aInv_ok,
    weak_ok, thompson_ok⟩

end CertificateChecks.KernelSpor.McLTK

end
