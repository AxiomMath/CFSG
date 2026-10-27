module

public import Certificates.Kernel.U38Fix.Checks
public import Certificates.Kernel.U38Q.Glue
public import Certificates.Data.HuppertU38Fix.Check
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU38Fix

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum CFSG.KC.PGrp
  CFSG.KC.B3S3K CFSG.KC.K426K CFSG.KC.U38QK CFSG.KC.U38FixK CFSG.KS.PEnum
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.Certificates.Native CFSG.RankThree.PartTwo.Sec4.Item434U38 U38Sylow U38Fix
open CertificateChecks.KernelSchreierFam CertificateChecks.KernelU38Q
open CFSG.Monster.B.Co2 (allLt_iff)

local notation "SX" G => siftOK 513 10 4 CertificateChecks.KernelU38.UX.LR
  CertificateChecks.KernelU38.UX.TRI CertificateChecks.KernelU38.UX.BP G

theorem pF {j : ℕ} (hj : j < 8) : permB 513 10 (FH.F j) = true := Orb.allN_iff.1 fx419Perm j hj

theorem arr_eq {k : ℕ} (hk : k < 8) : fixArr k = unpack 513 10 (FH.F k) := by
  rw [fixArr, FH.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound FH.all k hk

theorem pX : permB 513 10 (U38A.F 31) = true := U38B.pPF (k := 31) (by norm_num) (by norm_num)

theorem x7_eq : x7 = unpack 513 10 (U38A.F 31) := U38B.permArr_eq (k := 31) (by norm_num)

theorem cube_u {p : ℕ} (hp : permB 513 10 p = true) : cubeOne (unpack 513 10 p) = cubeK 513 10 p := by
  have pp := CFSG.KC.PGrp.permB_pcomp hw hp hp
  rw [cubeOne, comp_unpack' hw hp hp, comp_unpack' hw hp pp,
    eqA_id hw (CFSG.KC.PGrp.permB_pcomp hw hp pp)]
  rfl

theorem comm_u {p q : ℕ} (hp : permB 513 10 p = true) (hq : permB 513 10 q = true) :
    commAt (unpack 513 10 p) (unpack 513 10 q) = CFSG.KC.U38FixK.commK 513 10 p q := by
  rw [commAt, comp_unpack' hw hp hq, comp_unpack' hw hq hp,
    eqA_unpack' hw (CFSG.KC.PGrp.permB_pcomp hw hp hq) (CFSG.KC.PGrp.permB_pcomp hw hq hp)]
  rfl

theorem isId_u {p : ℕ} (hp : permB 513 10 p = true) :
    isIdA (unpack 513 10 p) = Nat.beq p (pidn 513 10) := by
  rw [isIdA, eqA_id hw hp]

theorem inX_u {p : ℕ} (hp : permB 513 10 p = true) :
    inXA (rawLevels 513 strong3 base3) (unpack 513 10 p) = SX p := by
  rw [inXA]
  exact siftX_eq (pp_of_permB hw hp)

theorem cubeComm_u {p : ℕ} (hp : permB 513 10 p = true) :
    cubeComm (unpack 513 10 p) = (cubeK 513 10 p && CFSG.KC.U38FixK.commK 513 10 p (U38A.F 31)) := by
  rw [cubeComm, cube_u hp, x7_eq, comm_u hp pX]

theorem pw3_u {X : ℕ} (hX : permB 513 10 X = true) :
    ∀ a, pw3 (unpack 513 10 X) a = unpack 513 10 (pw3K 513 10 X a) ∧
      permB 513 10 (pw3K 513 10 X a) = true
  | 0 => ⟨idA_eq hw, permB_id hw⟩
  | 1 => ⟨rfl, hX⟩
  | _ + 2 => ⟨comp_unpack' hw hX hX, CFSG.KC.PGrp.permB_pcomp hw hX hX⟩

theorem hg_eq {k : ℕ} (hk : k < 2) : hGens[k]! = unpack 513 10 (FH.F k) := by
  have e : hGens[k]! = fixArr k := by interval_cases k <;> rfl
  rw [e, arr_eq (by omega)]

theorem numsH : HE.N = 378 ∧ HE.ng = 2 :=
  ⟨Nat.eq_of_beq_eq_true fx419Nums.1, Nat.eq_of_beq_eq_true fx419Nums.2⟩

theorem GH_eq {k : ℕ} (hk : k < 2) : HE.G k = FH.F k :=
  Nat.eq_of_beq_eq_true (Orb.allN_iff.1 fx419Gens k hk)

theorem bindH : BindA 513 10 hGens HE.ng HE.G := by
  rw [numsH.2]
  refine ⟨rfl, fun k hk => ?_⟩
  rw [hg_eq hk, GH_eq hk]

theorem permGH : ∀ k < HE.ng, permB 513 10 (HE.G k) = true := fun k hk => by
  rw [numsH.2] at hk
  rw [GH_eq hk]
  exact pF (by omega)

theorem enumH : enumOK 513 hGens keyPts (hCert ()) = true ∧ (hCert ()).pts.size = HE.N ∧
    ∀ i < HE.N, (hCert ()).pts[i]! = unpack 513 10 (HE.T i) :=
  enum_of (ps := keyPts) (fuel := 500) bindH permGH HE.ok hps HE.keys (by rw [numsH.1]; omega)

theorem szH : (hCert ()).pts.size = 378 := by rw [enumH.2.1, numsH.1]

theorem iH {i : ℕ} (hi : i < 378) : i < HE.N := by rw [numsH.1]; exact hi

theorem getH {i : ℕ} (hi : i < 378) : (hCert ()).pts[i]! = unpack 513 10 (HE.T i) :=
  enumH.2.2 i (iH hi)

theorem permH {i : ℕ} (hi : i < 378) : permB 513 10 (HE.T i) = true :=
  permB_of_pp (PP_pts HE.ok permGH i (iH hi))

theorem getH' {i : ℕ} (hi : i < (hCert ()).pts.size) :
    (hCert ()).pts[i] = unpack 513 10 (HE.T i) := by
  rw [← getElem!_pos (hCert ()).pts i hi, getH (by rw [szH] at hi; exact hi)]

theorem genSiftH : allLt hGens.size
    (fun k => siftA 513 (rawLevels 513 strong1 base1) base1 0 hGens[k]!) = true := by
  rw [allLt_iff]
  intro k hk
  have hk2 : k < 2 := by simpa [hGens] using hk
  rw [hg_eq hk2]
  exact siftA_of_siftOK U38B.binds1 U38B.perm1 U38C1.hl (Orb.allN_iff.1 fx419Sift1 k hk2)

theorem genFixH : allLt hGens.size (fun k => (hGens[k]!)[109]! == 109 && (hGens[k]!)[458]! == 458) =
    true := by
  rw [allLt_iff]
  intro k hk
  have hk2 : k < 2 := by simpa [hGens] using hk
  have e := Orb.allN_iff.1 fx419Fix.1 k hk2
  rw [Bool.and_eq_true] at e
  rw [hg_eq hk2, Orb.unpack_get (by norm_num : 109 < 513), Orb.unpack_get (by norm_num : 458 < 513),
    Nat.eq_of_beq_eq_true e.1, Nat.eq_of_beq_eq_true e.2]
  rfl

theorem x7Fix : (x7[109]! == 109) = true ∧ (x7[458]! == 458) = true ∧
    inXA (rawLevels 513 strong3 base3) x7 = true := by
  obtain ⟨-, e1, e2, e3⟩ := fx419Fix
  rw [x7_eq, Orb.unpack_get (by norm_num : 109 < 513), Orb.unpack_get (by norm_num : 458 < 513),
    Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2, inX_u pX]
  exact ⟨rfl, rfl, e3⟩

theorem fixOK_true : fixOK (rawLevels 513 strong3 base3) (hCert ()) = true := by
  unfold fixOK
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < 378 := by rw [szH] at hi; exact hi
  have e := Orb.allN_iff.1 fx419FixOK i hi'
  rw [getH' hi, cubeComm_u (permH hi'), inX_u (permH hi')]
  exact e

theorem fixWit_true : fixWit (rawLevels 513 strong3 base3) (hCert ()) = true := by
  have e := fx419FixWit
  generalize FW.getD 0 0 = i at e
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq] at e
  obtain ⟨⟨⟨⟨hi, h1⟩, h2⟩, h3⟩, h4⟩ := e
  unfold fixWit
  rw [Array.any_eq_true]
  refine ⟨i, by rw [szH]; exact hi, ?_⟩
  rw [getH' (by rw [szH]; exact hi), cubeComm_u (permH hi), isId_u (permH hi), inX_u (permH hi), h1,
    h2, h3, h4]
  rfl

theorem fix_true : fixCheck () = true := by
  unfold fixCheck
  simp only [enumH.1, szH, genSiftH, genFixH, x7Fix.1, x7Fix.2.1, x7Fix.2.2, fixOK_true,
    fixWit_true, beq_self_eq_true, Bool.and_self]

theorem eBar_eq : eBar = unpack 513 10 (FH.F 3) := arr_eq (by norm_num)

theorem fBar_eq : fBar = unpack 513 10 (FH.F 4) := arr_eq (by norm_num)

theorem gRefl_eq : gRefl = unpack 513 10 (FH.F 2) := arr_eq (by norm_num)

theorem tHs_size : tHs.size = 3 := rfl

theorem tHs_get {k : ℕ} (hk : k < 3) : tHs[k]! = unpack 513 10 (FH.F (5 + k)) := by
  have e : tHs[k]! = fixArr (5 + k) := by interval_cases k <;> rfl
  rw [e, arr_eq (by omega)]

theorem inXg {j : ℕ} (h1 : 2 ≤ j) (h2 : j < 8) : inXA (rawLevels 513 strong3 base3)
    (unpack 513 10 (FH.F j)) = true := by
  have e := Orb.allN_iff.1 fx419X (j - 2) (by omega)
  have e2 : Nat.add 2 (j - 2) = j := by
    change 2 + (j - 2) = j
    omega
  rw [e2] at e
  rw [inX_u (pF h2)]
  exact e

theorem tHs_valid : allLt tHs.size (fun k => validA 513 tHs[k]!) = true := by
  rw [allLt_iff]
  intro k hk
  rw [tHs_size] at hk
  rw [tHs_get hk]
  exact validA_of (pF (by omega))

theorem tHs_inX : allLt tHs.size (fun k => inXA (rawLevels 513 strong3 base3) tHs[k]!) = true := by
  rw [allLt_iff]
  intro k hk
  rw [tHs_size] at hk
  rw [tHs_get hk]
  exact inXg (by omega) (by omega)

theorem relsE : cubeOne eBar = true ∧ cubeOne fBar = true ∧ isIdA eBar = false ∧
    isIdA fBar = false ∧ eqA 513 fBar eBar = false ∧ eqA 513 fBar (compA 513 eBar eBar) = false ∧
    commAt eBar fBar = true ∧ commAt gRefl eBar = true ∧
    eqA 513 (compA 513 gRefl fBar) (compA 513 (compA 513 fBar fBar) gRefl) = true := by
  have e := fx419E
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at e
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := e
  have p2 := pF (j := 2) (by norm_num)
  have p3 := pF (j := 3) (by norm_num)
  have p4 := pF (j := 4) (by norm_num)
  have p33 := CFSG.KC.PGrp.permB_pcomp hw p3 p3
  have p44 := CFSG.KC.PGrp.permB_pcomp hw p4 p4
  rw [eBar_eq, fBar_eq, gRefl_eq, cube_u p3, cube_u p4, isId_u p3, isId_u p4, eqA_unpack' hw p4 p3,
    comp_unpack' hw p3 p3, eqA_unpack' hw p4 p33, comm_u p3 p4, comm_u p2 p3, comp_unpack' hw p2 p4,
    comp_unpack' hw p4 p4, comp_unpack' hw p44 p2,
    eqA_unpack' hw (CFSG.KC.PGrp.permB_pcomp hw p2 p4) (CFSG.KC.PGrp.permB_pcomp hw p44 p2)]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem memK_sound {y : ℕ} : ∀ {L : List ℕ}, memK y L = true → y ∈ L
  | [], h => absurd h Bool.false_ne_true
  | x :: L, h => by
    have h' : (Nat.beq x y || memK y L) = true := h
    rw [Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · rw [Nat.eq_of_beq_eq_true h']
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (memK_sound h')

theorem hT_facts {t : ℕ} (ht : t < 4) : ∃ h ∈ idA 513 :: tHs.toList,
    h = unpack 513 10 (hT t) ∧ permB 513 10 (hT t) = true := by
  have eT : tHs.toList = [fixArr 5, fixArr 6, fixArr 7] := rfl
  rw [eT]
  interval_cases t
  · exact ⟨_, List.mem_cons_self, idA_eq hw, permB_id hw⟩
  · have e : hT 1 = FH.F 5 := rfl
    rw [e]
    exact ⟨fixArr 5, List.mem_cons_of_mem _ List.mem_cons_self, arr_eq (by norm_num),
      pF (by norm_num)⟩
  · have e : hT 2 = FH.F 6 := rfl
    rw [e]
    exact ⟨fixArr 6, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      arr_eq (by norm_num), pF (by norm_num)⟩
  · have e : hT 3 = FH.F 7 := rfl
    rw [e]
    exact ⟨fixArr 7, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)), arr_eq (by norm_num), pF (by norm_num)⟩

theorem e0_facts {e : ℕ} (he : e < 9) : ∃ w ∈ e0List (),
    w = unpack 513 10 (eK e) ∧ permB 513 10 (eK e) = true := by
  have ha : e / 3 < 3 := by omega
  have hb : e % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have h := Nat.eq_of_beq_eq_true (Orb.allN_iff.1 (Orb.allN_iff.1 fx419E0 (e / 3) ha) (e % 3) hb)
  have e3 : Nat.add (Nat.mul 3 (e / 3)) (e % 3) = e := by
    change 3 * (e / 3) + e % 3 = e
    omega
  rw [e3] at h
  obtain ⟨a1, a2⟩ := pw3_u (pF (j := 3) (by norm_num)) (e / 3)
  obtain ⟨b1, b2⟩ := pw3_u (pF (j := 4) (by norm_num)) (e % 3)
  refine ⟨compA 513 (pw3 eBar (e / 3)) (pw3 fBar (e % 3)), ?_, ?_, ?_⟩
  · unfold e0List
    exact List.mem_flatMap.2 ⟨e / 3, List.mem_range.2 ha,
      List.mem_map.2 ⟨e % 3, List.mem_range.2 hb, rfl⟩⟩
  · rw [h, eBar_eq, fBar_eq, a1, b1, comp_unpack' hw a2 b2]
  · rw [h]
    exact CFSG.KC.PGrp.permB_pcomp hw a2 b2

theorem cover_true : coverAll (uTab (XI.map fun i => (qCert ()).pts[i]!) (e0List ())
    (idA 513 :: tHs.toList)) (XI.map fun i => (qCert ()).pts[i]!) = true := by
  unfold coverAll
  rw [List.all_map, List.all_eq_true]
  intro z hz
  simp only [Function.comp_apply]
  have lz := ltXI z hz
  obtain ⟨c, -, e⟩ := exists_of_forall₂ (forall₂_of_pairK fx419Cover) z hz
  rw [getT lz, cube_u (permT lz), isId_u (permT lz)]
  unfold coverRowK at e
  rw [Bool.or_eq_true, Bool.or_eq_true] at e ⊢
  rcases e with (e | e) | e
  · exact Or.inl (Or.inl e)
  · exact Or.inl (Or.inr e)
  right
  rw [Bool.and_eq_true] at e
  obtain ⟨hm, hc⟩ := e
  have ht : c % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have he : c / 4 % 9 < 9 := Nat.mod_lt _ (by norm_num)
  have hy := memK_sound hm
  generalize c % 4 = t at ht hc
  generalize c / 4 % 9 = k at he hc
  generalize c / 36 = y at hy hc
  have ly := ltXI y hy
  obtain ⟨h, hmem, hh, ph⟩ := hT_facts ht
  obtain ⟨w, wmem, hw', pw⟩ := e0_facts he
  have pu := CFSG.KC.PGrp.permB_pcomp hw ph (permT ly)
  unfold coverOne
  rw [List.any_eq_true]
  refine ⟨(compA 513 h (unpack 513 10 (QE.T y)),
    (e0List ()).map fun w => compA 513 w (compA 513 h (unpack 513 10 (QE.T y)))), ?_, ?_⟩
  · unfold uTab
    exact List.mem_map.2 ⟨_, List.mem_flatMap.2 ⟨h, hmem,
      List.mem_map.2 ⟨_, List.mem_map.2 ⟨y, hy, getT ly⟩, rfl⟩⟩, rfl⟩
  rw [List.any_eq_true]
  refine ⟨compA 513 w (compA 513 h (unpack 513 10 (QE.T y))), List.mem_map.2 ⟨w, wmem, rfl⟩, ?_⟩
  rw [hh, hw', comp_unpack' hw ph (permT ly), comp_unpack' hw pu (permT lz), comp_unpack' hw pw pu,
    eqA_unpack' hw (CFSG.KC.PGrp.permB_pcomp hw pu (permT lz)) (CFSG.KC.PGrp.permB_pcomp hw pw pu)]
  exact hc

theorem toral_true : toralCheck () = true := by
  have hl : XI.length = 81 := Nat.eq_of_beq_eq_true q211Lens.1
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := relsE
  have vE : validA 513 eBar = true := by rw [eBar_eq]; exact validA_of (pF (by norm_num))
  have vF : validA 513 fBar = true := by rw [fBar_eq]; exact validA_of (pF (by norm_num))
  have vG : validA 513 gRefl = true := by rw [gRefl_eq]; exact validA_of (pF (by norm_num))
  have xE : inXA (rawLevels 513 strong3 base3) eBar = true := by
    rw [eBar_eq]
    exact inXg (by norm_num) (by norm_num)
  have xF : inXA (rawLevels 513 strong3 base3) fBar = true := by
    rw [fBar_eq]
    exact inXg (by norm_num) (by norm_num)
  have xG : inXA (rawLevels 513 strong3 base3) gRefl = true := by
    rw [gRefl_eq]
    exact inXg (by norm_num) (by norm_num)
  unfold toralCheck
  simp only [inX_eq, enumQ.1, sz, hl, vE, vF, vG, tHs_valid, xE, xF, xG, tHs_inX, r1, r2, r3, r4,
    r5, r6, r7, r8, r9, cover_true, beq_self_eq_true, Bool.not_false, Bool.and_self]

theorem all_true : u38FixAllCheck () = true := by
  unfold u38FixAllCheck
  rw [fix_true, toral_true]
  rfl

end CertificateChecks.KernelU38Fix

end
