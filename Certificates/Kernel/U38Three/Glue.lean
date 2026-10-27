module

public import Certificates.Kernel.U38Three.Checks
public import Certificates.Kernel.U38Three.PChecks
public import Certificates.Kernel.U38Fix.Glue
public import CFSG.Certificates.Kernel.U38ThreeSound
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU38Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum
  CFSG.KC.B3S3K CFSG.KC.K426K CFSG.KC.U38QK CFSG.KC.U38ThreeK
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.Certificates.Native CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.RankThree.PartOne U38Sylow
  U38Three
open CertificateChecks.KernelSchreierFam CertificateChecks.KernelU38
open CFSG.Monster.B.Co2 (allLt_iff)

theorem hw : szOK 513 10 = true := KernelU38Q.hw

theorem pF {j : ℕ} (hj : j < 7) : permB 513 10 (FT.F j) = true := Orb.allN_iff.1 ch810201Perm j hj

theorem arr_eq {k : ℕ} (hk : k < 7) : u3Arr k = unpack 513 10 (FT.F k) := by
  rw [u3Arr, FT.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound FT.all k hk

theorem d0_eq : d0 = unpack 513 10 (FT.F 0) := arr_eq (k := 0) (by norm_num)

theorem la_eq : la = unpack 513 10 (FT.F 3) := arr_eq (k := 3) (by norm_num)

theorem lb_eq : lb = unpack 513 10 (FT.F 4) := arr_eq (k := 4) (by norm_num)

theorem nums : HE.N = 378 ∧ HE.ng = 2 ∧ LE.N = 504 ∧ LE.ng = 2 ∧ CE.N = 1512 ∧ CE.ng = 2 := by
  have e := ch810201Nums
  simp only [Bool.and_eq_true] at e
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := e
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6⟩

theorem gens {j : ℕ} (hj : j < 2) :
    HE.G j = FT.F (1 + j) ∧ LE.G j = FT.F (3 + j) ∧ CE.G j = FT.F (5 + j) := by
  have e := Orb.allN_iff.1 ch810201Gens j hj
  simp only [Bool.and_eq_true] at e
  exact ⟨Nat.eq_of_beq_eq_true e.1.1, Nat.eq_of_beq_eq_true e.1.2, Nat.eq_of_beq_eq_true e.2⟩

theorem hGens_get {k : ℕ} (hk : k < 2) : hGens[k]! = unpack 513 10 (FT.F (1 + k)) := by
  have e : hGens[k]! = u3Arr (1 + k) := by interval_cases k <;> rfl
  rw [e, arr_eq (by omega)]

theorem lGens_get {k : ℕ} (hk : k < 2) : lGens[k]! = unpack 513 10 (FT.F (3 + k)) := by
  have e : lGens[k]! = u3Arr (3 + k) := by interval_cases k <;> rfl
  rw [e, arr_eq (by omega)]

theorem cGens_get {k : ℕ} (hk : k < 2) : cGens[k]! = unpack 513 10 (FT.F (5 + k)) := by
  have e : cGens[k]! = u3Arr (5 + k) := by interval_cases k <;> rfl
  rw [e, arr_eq (by omega)]

theorem bind2 {gs : Array (Array ℕ)} {ng o : ℕ} {G : ℕ → ℕ} (hs : gs.size = 2) (hng : ng = 2)
    (hget : ∀ k < 2, gs[k]! = unpack 513 10 (FT.F (o + k))) (hG : ∀ k < 2, G k = FT.F (o + k)) :
    BindA 513 10 gs ng G := by
  subst hng
  exact ⟨hs, fun k hk => by rw [hget k hk, hG k hk]⟩

theorem perm2 {ng o : ℕ} {G : ℕ → ℕ} (ho : o + 2 ≤ 7) (hng : ng = 2)
    (hG : ∀ k < 2, G k = FT.F (o + k)) : ∀ k < ng, permB 513 10 (G k) = true := fun k hk => by
  subst hng
  rw [hG k hk]
  exact pF (by omega)

theorem bindH : BindA 513 10 hGens HE.ng HE.G :=
  bind2 rfl nums.2.1 (fun _ hk => hGens_get hk) (fun _ hk => (gens hk).1)

theorem bindL : BindA 513 10 #[la, lb] LE.ng LE.G :=
  bind2 rfl nums.2.2.2.1 (fun _ hk => lGens_get hk) (fun _ hk => (gens hk).2.1)

theorem bindC2 : BindA 513 10 cGens 2 CE.G :=
  bind2 rfl rfl (fun _ hk => cGens_get hk) (fun _ hk => (gens hk).2.2)

theorem bindC : BindA 513 10 cGens CE.ng CE.G := by
  rw [nums.2.2.2.2.2]
  exact bindC2

theorem permGH : ∀ k < HE.ng, permB 513 10 (HE.G k) = true :=
  perm2 (o := 1) (by norm_num) nums.2.1 (fun _ hk => (gens hk).1)

theorem permGL : ∀ k < LE.ng, permB 513 10 (LE.G k) = true :=
  perm2 (o := 3) (by norm_num) nums.2.2.2.1 (fun _ hk => (gens hk).2.1)

theorem permGC : ∀ k < CE.ng, permB 513 10 (CE.G k) = true :=
  perm2 (o := 5) (by norm_num) nums.2.2.2.2.2 (fun _ hk => (gens hk).2.2)

theorem enumH : enumOK 513 hGens keyPts (hCert ()) = true ∧ (hCert ()).pts.size = HE.N ∧
    ∀ i < HE.N, (hCert ()).pts[i]! = unpack 513 10 (HE.T i) :=
  enum_of (ps := keyPts) (fuel := 400) bindH permGH HE.ok KernelU38Q.hps HE.keys
    (by rw [nums.1]; omega)

theorem enumL : enumOK 513 #[la, lb] keyPts (lCert ()) = true ∧ (lCert ()).pts.size = LE.N ∧
    ∀ i < LE.N, (lCert ()).pts[i]! = unpack 513 10 (LE.T i) :=
  enum_of (ps := keyPts) (fuel := 600) bindL permGL LE.ok KernelU38Q.hps LE.keys
    (by rw [nums.2.2.1]; omega)

theorem enumC : enumOK 513 cGens keyPts (cCert ()) = true ∧ (cCert ()).pts.size = CE.N ∧
    ∀ i < CE.N, (cCert ()).pts[i]! = unpack 513 10 (CE.T i) :=
  enum_of (ps := keyPts) (fuel := 1600) bindC permGC CE.ok KernelU38Q.hps CE.keys
    (by rw [nums.2.2.2.2.1]; omega)

theorem szH : (hCert ()).pts.size = 378 := by rw [enumH.2.1, nums.1]

theorem szL : (lCert ()).pts.size = 504 := by rw [enumL.2.1, nums.2.2.1]

theorem getH {i : ℕ} (hi : i < 378) : (hCert ()).pts[i]! = unpack 513 10 (HE.T i) :=
  enumH.2.2 i (by rw [nums.1]; exact hi)

theorem permH {i : ℕ} (hi : i < 378) : permB 513 10 (HE.T i) = true :=
  permB_of_pp (PP_pts HE.ok permGH i (by rw [nums.1]; exact hi))

theorem permL {i : ℕ} (hi : i < LE.N) : permB 513 10 (LE.T i) = true :=
  permB_of_pp (PP_pts LE.ok permGL i hi)

theorem permC {i : ℕ} (hi : i < CE.N) : permB 513 10 (CE.T i) = true :=
  permB_of_pp (PP_pts CE.ok permGC i hi)

theorem sift1_fix {j : ℕ} (hj : j < 3) :
    siftA 513 (rawLevels 513 strong1 base1) base1 0 (unpack 513 10 (FT.F j)) = true ∧
      fix01 (unpack 513 10 (FT.F j)) = true := by
  have e := Orb.allN_iff.1 ch810201Sift1 j hj
  simp only [Bool.and_eq_true] at e
  obtain ⟨⟨h1, h2⟩, h3⟩ := e
  refine ⟨siftA_of_siftOK U38B.binds1 U38B.perm1 U38C1.hl h1, ?_⟩
  unfold fix01
  rw [Orb.unpack_get (by norm_num : 0 < 513), Orb.unpack_get (by norm_num : 1 < 513),
    Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3]
  rfl

theorem genH_true : allLt hGens.size
    (fun k => siftA 513 (rawLevels 513 strong1 base1) base1 0 hGens[k]! && fix01 hGens[k]!) =
      true := by
  rw [allLt_iff]
  intro k hk
  have hk2 : k < 2 := by simpa [hGens] using hk
  rw [hGens_get hk2, Bool.and_eq_true]
  exact sift1_fix (by omega)

theorem d0_facts : validA 513 d0 = true ∧ cubeOne d0 = true ∧ eqA 513 d0 (idA 513) = false := by
  have e := ch810201D0
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at e
  have p0 := pF (j := 0) (by norm_num)
  rw [d0_eq, KernelU38Fix.cube_u p0, eqA_id hw p0]
  exact ⟨validA_of p0, e.1, e.2⟩

theorem hElem_true : hElemCheck (hCert ()).pts d0 (compA 513 d0 d0) = true := by
  have p0 := pF (j := 0) (by norm_num)
  have p00 := CFSG.KC.PGrp.permB_pcomp hw p0 p0
  have hlt : ∀ i ∈ cubeIdxK 513 10 378 HE.T, i < 378 :=
    fun i hi => List.mem_range.1 (List.mem_filter.1 hi).1
  have hcs : cubeIdx (hCert ()).pts = cubeIdxK 513 10 378 HE.T := by
    unfold cubeIdx cubeIdxK
    rw [szH]
    apply List.filter_congr
    intro i hi
    rw [getH (List.mem_range.1 hi), KernelU38Fix.cube_u (permH (List.mem_range.1 hi))]
  have e := ch810201Elem
  unfold hElemK hElemL at e
  unfold hElemCheck
  rw [hcs, d0_eq, comp_unpack' hw p0 p0]
  rw [List.all_eq_true] at e ⊢
  intro i hi
  have li := hlt i hi
  have hf : (cubeIdxK 513 10 378 HE.T).filter
      (fun j => commAt (unpack 513 10 (HE.T i)) (hCert ()).pts[j]!) =
      (cubeIdxK 513 10 378 HE.T).filter
        (fun j => CFSG.KC.U38FixK.commK 513 10 (HE.T i) (HE.T j)) := by
    apply List.filter_congr
    intro j hj
    rw [getH (hlt j hj), KernelU38Fix.comm_u (permH li) (permH (hlt j hj))]
  rw [getH li, eqA_id hw (permH li), eqA_unpack' hw (permH li) p0, eqA_unpack' hw (permH li) p00,
    KernelU38Fix.comm_u (permH li) p0, hf]
  exact e i hi

theorem siftX_of {j : ℕ} (h1 : 3 ≤ j) (h2 : j < 7) :
    siftA 513 (rawLevels 513 strong3 base3) base3 0 (unpack 513 10 (FT.F j)) = true := by
  have e := Orb.allN_iff.1 ch810201SiftX (j - 3) (by omega)
  have e2 : Nat.add 3 (j - 3) = j := by
    change 3 + (j - 3) = j
    omega
  rw [e2] at e
  rw [KernelU38Q.siftX_eq (pp_of_permB hw (pF (j := j) h2))]
  exact e

theorem comm_l : commAt la d0 = true ∧ commAt lb d0 = true := by
  have e := ch810201Comm
  simp only [Bool.and_eq_true] at e
  rw [la_eq, lb_eq, d0_eq, KernelU38Fix.comm_u (pF (j := 3) (by norm_num)) (pF (j := 0) (by norm_num)),
    KernelU38Fix.comm_u (pF (j := 4) (by norm_num)) (pF (j := 0) (by norm_num))]
  exact e

theorem cent_true : centOKP 3 513 strong3 base3 d0 rels3 cGens keyPts (cCert ()) 1512 = true := by
  have e := ch810201Rels
  simp only [Bool.and_eq_true] at e
  obtain ⟨⟨hr, hc⟩, hl⟩ := e
  have hl' := Nat.eq_of_beq_eq_true hl
  have h := centOKP_of hw KernelU38.binds KernelU38.permX KernelU38.UX.hl (pF (j := 0) (by norm_num))
    hr bindC2 hc
    (fun k hk => by
      rw [(gens hk).2.2]
      exact siftX_of (j := 5 + k) (by omega) (by omega))
    enumC.1 enumC.2.1 enumC.2.2 (fun i hi => permC hi) (by norm_num)
    (by rw [hl']; exact ch810201Tail)
  rw [nums.2.2.2.2.1] at h
  rw [d0_eq]
  exact h

theorem conjInv_unpack {p q : ℕ} (hp : permB 513 10 p = true) (hq : permB 513 10 q = true) :
    conjInvA 513 (unpack 513 10 p) (unpack 513 10 q) = unpack 513 10 (cjInv 513 10 p q) := by
  have hP := pp_of_permB hw hp
  have hQ := pp_of_permB hw hq
  rw [conjInvA, invCand_PP hP, compA_PP hQ hP, compA_PP hP.inv (hQ.mul hP)]
  rfl

theorem memL {p : ℕ} (hp : permB 513 10 p = true) {m : ℕ} (hm : m < 504) (he : LE.T m = p) :
    memPts (lCert ()) (unpack 513 10 p) = true := by
  unfold memPts
  rw [any_eqA_unpack' hw enumL.2.1 enumL.2.2 (fun i hi => permL hi) hp, memK, anyNP_eq,
    List.any_eq_true]
  exact ⟨m, List.mem_range.2 (by rw [nums.2.2.1]; exact hm), by rw [he]; exact Nat.beq_refl p⟩

theorem memXY {k x : ℕ} (hk : k < 2) (hx : x < 2) :
    memPts (lCert ()) (conjA 513 cGens[k]! lGens[x]!) = true ∧
      memPts (lCert ()) (conjInvA 513 cGens[k]! lGens[x]!) = true := by
  have e := Orb.allN_iff.1 (Orb.allN_iff.1 ch810201Mem k hk) x hx
  simp only [Bool.and_eq_true, Nat.blt_eq] at e
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := e
  have pc := pF (j := 5 + k) (by omega)
  have py := pF (j := 3 + x) (by omega)
  rw [cGens_get hk, lGens_get hx, conj_unpack' hw pc py, conjInv_unpack pc py]
  have pci := CFSG.KC.Misc.ArrEnum.permB_pinvS hw pc
  have q1 : permB 513 10 (cj 513 10 (FT.F (5 + k)) (FT.F (3 + x))) = true :=
    CFSG.KC.PGrp.permB_pcomp hw pc (CFSG.KC.PGrp.permB_pcomp hw py pci)
  have q2 : permB 513 10 (cjInv 513 10 (FT.F (5 + k)) (FT.F (3 + x))) = true :=
    CFSG.KC.PGrp.permB_pcomp hw pci (CFSG.KC.PGrp.permB_pcomp hw py pc)
  exact ⟨memL q1 h1 (Nat.eq_of_beq_eq_true h2), memL q2 h3 (Nat.eq_of_beq_eq_true h4)⟩

theorem mem_true : allLt cGens.size (fun k => memPts (lCert ()) (conjA 513 cGens[k]! la) &&
    memPts (lCert ()) (conjA 513 cGens[k]! lb) && memPts (lCert ()) (conjInvA 513 cGens[k]! la) &&
    memPts (lCert ()) (conjInvA 513 cGens[k]! lb)) = true := by
  rw [allLt_iff]
  intro k hk
  have hk2 : k < 2 := by simpa [cGens] using hk
  have h0 := memXY hk2 (x := 0) (by norm_num)
  have h1 := memXY hk2 (x := 1) (by norm_num)
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨h0.1, h1.1⟩, h0.2⟩, h1.2⟩

theorem hw9 : szOK 9 4 = true := by decide +kernel

theorem pnums : PE.N = 504 ∧ PE.ng = 2 ∧ RI.length = 8 := by
  have e := ch810201PNums
  simp only [Bool.and_eq_true] at e
  exact ⟨Nat.eq_of_beq_eq_true e.1.1, Nat.eq_of_beq_eq_true e.1.2, Nat.eq_of_beq_eq_true e.2⟩

theorem pGens_get {k : ℕ} (hk : k < 2) : pGens[k]! = unpack 9 4 (PE.G k) := by
  interval_cases k <;> decide +kernel

theorem permGP : ∀ k < PE.ng, permB 9 4 (PE.G k) = true := fun k hk => by
  rw [pnums.2.1] at hk
  interval_cases k <;> decide +kernel

theorem bindP : BindA 9 4 pGens PE.ng PE.G := by
  rw [pnums.2.1]
  exact ⟨rfl, fun k hk => pGens_get hk⟩

theorem hps9 : ∀ p ∈ keyPts9, p < 9 := by decide

theorem enumP : enumOK 9 pGens keyPts9 (pCert ()) = true ∧ (pCert ()).pts.size = PE.N ∧
    ∀ i < PE.N, (pCert ()).pts[i]! = unpack 9 4 (PE.T i) :=
  enum_of (ps := keyPts9) (fuel := 600) bindP permGP PE.ok hps9 PE.keys (by rw [pnums.1]; omega)

theorem szP : (pCert ()).pts.size = 504 := by rw [enumP.2.1, pnums.1]

theorem getP {i : ℕ} (hi : i < 504) : (pCert ()).pts[i]! = unpack 9 4 (PE.T i) :=
  enumP.2.2 i (by rw [pnums.1]; exact hi)

theorem permP {i : ℕ} (hi : i < 504) : permB 9 4 (PE.T i) = true :=
  Orb.allN_iff.1 PE.perm i (by rw [pnums.1]; exact hi)

theorem rep_of {r N ng : ℕ} {G T E S : ℕ → ℕ} {SK : List ℕ}
    (hr : repOK 9 4 12 504 PE.T r N ng G = true) (hk : bfsK 9 4 ng G N T E S = true)
    (hK : keysSK 9 4 pBase.toList N T SK = true) :
    r < (pCert ()).pts.size ∧ ∃ ck : ArrCert, enumOK 9 (conjGensM 9 12 (pCert ()) r) keyPts9 ck =
      true ∧ ck.pts.size = (pCert ()).pts.size := by
  unfold repOK at hr
  simp only [Bool.and_eq_true, Nat.blt_eq] at hr
  obtain ⟨⟨⟨hr1, hN⟩, hng⟩, hG⟩ := hr
  have hN' := Nat.eq_of_beq_eq_true hN
  have hng' := Nat.eq_of_beq_eq_true hng
  have hGj : ∀ j < ng, G j = cj 9 4 (PE.T j) (PE.T r) := fun j hj =>
    Nat.eq_of_beq_eq_true (Orb.allN_iff.1 hG j (by omega))
  have pG : ∀ j < ng, permB 9 4 (G j) = true := fun j hj => by
    rw [hGj j hj]
    exact CFSG.KC.PGrp.permB_pcomp hw9 (permP (by omega)) (CFSG.KC.PGrp.permB_pcomp hw9
      (permP hr1) (CFSG.KC.Misc.ArrEnum.permB_pinvS hw9 (permP (by omega))))
  have hb : BindA 9 4 (conjGensM 9 12 (pCert ()) r) ng G := by
    refine ⟨by simp [conjGensM, hng'], fun j hj => ?_⟩
    rw [getElem!_pos _ j (by simp [conjGensM]; omega)]
    simp only [conjGensM, Array.getElem_ofFn]
    rw [getP (by omega), getP hr1, conj_unpack' hw9 (permP (by omega)) (permP hr1), hGj j hj]
    rfl
  have := enum_of (ps := keyPts9) (fuel := 600) hb pG hk hps9 hK (by omega)
  exact ⟨by rw [szP]; exact hr1, _, this.1, by rw [this.2.1, szP, hN']⟩

theorem allN_false {m : ℕ} {f : ℕ → Bool} (h : allN m f = false) : ∃ t < m, f t = false := by
  by_contra hc
  push Not at hc
  have : allN m f = true := Orb.allN_iff.2 fun t ht => by
    cases e : f t
    · exact absurd e (hc t ht)
    · rfl
  rw [h] at this
  exact Bool.false_ne_true this

theorem p_simple : IsSimpleGroup (Subgroup.closure (permsA 9 pGens)) := by
  have hRl := pnums.2.2
  have hR : ∀ r ∈ RI, r < (pCert ()).pts.size ∧ ∃ ck : ArrCert,
      enumOK 9 (conjGensM 9 12 (pCert ()) r) keyPts9 ck = true ∧ ck.pts.size = (pCert ()).pts.size := by
    intro r hr
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
    have e : RI[k] = rI k := by
      unfold rI
      rw [List.getD_eq_getElem _ _ hk]
    rw [e]
    have hk8 : k < 8 := by rw [← hRl]; exact hk
    interval_cases k
    · exact rep_of ch810201Q0 Q0.ok Q0.keys
    · exact rep_of ch810201Q1 Q1.ok Q1.keys
    · exact rep_of ch810201Q2 Q2.ok Q2.keys
    · exact rep_of ch810201Q3 Q3.ok Q3.keys
    · exact rep_of ch810201Q4 Q4.ok Q4.keys
    · exact rep_of ch810201Q5 Q5.ok Q5.keys
    · exact rep_of ch810201Q6 Q6.ok Q6.keys
    · exact rep_of ch810201Q7 Q7.ok Q7.keys
  refine isSimpleGroup_of_reps hps9 enumP.1 (by rw [szP]; norm_num) (by rw [szP]; norm_num) hR ?_
  intro k hk
  rw [szP] at hk
  obtain ⟨h, -, e⟩ := exists_of_forall₂ (forall₂_of_pairK ch810201Cover) k (List.mem_range.2 hk)
  unfold coverK at e
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at e
  rcases e with e | ⟨hh, e⟩
  · left
    rw [getP hk, eqA_id hw9 (permP hk)]
    exact e
  · right
    obtain ⟨t, ht, et⟩ := allN_false e
    simp only [Bool.not_eq_false'] at et
    have hrt := Nat.eq_of_beq_eq_true et
    have htl : t < RI.length := by rw [hRl]; exact ht
    have hrI : rI t = RI[t] := by
      unfold rI
      rw [List.getD_eq_getElem _ _ htl]
    have hmem : rI t ∈ RI := by
      rw [hrI]
      exact List.getElem_mem htl
    have hr504 : rI t < 504 := by
      have := (hR _ hmem).1
      rwa [szP] at this
    refine ⟨h, by rw [szP]; exact hh, rI t, hmem, ?_⟩
    have pq : permB 9 4 (cj 9 4 (PE.T h) (PE.T k)) = true :=
      CFSG.KC.PGrp.permB_pcomp hw9 (permP hh) (CFSG.KC.PGrp.permB_pcomp hw9 (permP hk)
        (CFSG.KC.Misc.ArrEnum.permB_pinvS hw9 (permP hh)))
    rw [getP hh, getP hk, getP hr504, conj_unpack' hw9 (permP hh) (permP hk)]
    change eqA 9 (unpack 9 4 (cj 9 4 (PE.T h) (PE.T k))) (unpack 9 4 (PE.T (rI t))) = true
    rw [eqA_unpack' hw9 pq (permP hr504), hrt]
    exact Nat.beq_refl _

end CertificateChecks.KernelU38Three

end
