module

public import Certificates.Kernel.HeLoc.FiveLBase
public import Certificates.Kernel.HeLoc.FiveTab
public import Certificates.Kernel.HeLoc.ChainFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.FiveL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB CFSG.RankThree.Native
open CFSG.RankThree.PartOne CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Mathieu
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch


theorem eq_of_P {f f' : Nat → Nat} {x y : Equiv.Perm (Fin 8330)} (hf : RepF 8330 f x)
    (hf' : RepF 8330 f' y) (hx : x ∈ heP) (hy : y ∈ heP) (h : eqOnL Five.bs f f' = true) :
    x = y :=
  Five.faithful x (heP_le_heAutGroup hx) y (heP_le_heAutGroup hy) (iff_of_true hx hy)
    fun b hb => by
      rw [← hf b (Five.bs_lt b hb), ← hf' b (Five.bs_lt b hb)]
      exact (eqOnL_iff _ _ _).1 h b hb

theorem eqA_P {t u : Array Nat} {x y : Equiv.Perm (Fin 8330)} {f f' : Nat → Nat}
    (ht : Rep 8330 t x) (hu : Rep 8330 u y) (hf : RepF 8330 f x) (hf' : RepF 8330 f' y)
    (hx : x ∈ heP) (hy : y ∈ heP) (h : eqOnL Five.bs f f' = true) : eqA 8330 t u = true :=
  (eqA_iff ht hu).2 (eq_of_P hf hf' hx hy h)

theorem eqA_R {t u : Array Nat} {x y : Equiv.Perm (Fin 8330)} {f f' : Nat → Nat}
    (ht : Rep 8330 t x) (hu : Rep 8330 u y) (hf : RepF 8330 f x) (hf' : RepF 8330 f' y)
    (hx : x ∈ heAutGroup) (hy : y ∈ heAutGroup) (hxy : x ∈ heP ↔ y ∈ heP)
    (h : eqOnL Five.bs f f' = true) : eqA 8330 t u = true :=
  (eqA_iff ht hu).2 (Five.faithful x hx y hy hxy fun b hb => by
    rw [← hf b (Five.bs_lt b hb), ← hf' b (Five.bs_lt b hb)]
    exact (eqOnL_iff _ _ _).1 h b hb)

theorem neA_P {t u : Array Nat} {x y : Equiv.Perm (Fin 8330)} {f f' : Nat → Nat}
    (ht : Rep 8330 t x) (hu : Rep 8330 u y) (hf : RepF 8330 f x) (hf' : RepF 8330 f' y)
    (h : eqOnL Five.bs f f' = false) : eqA 8330 t u = false := by
  rw [Bool.eq_false_iff]
  intro he
  have e := (eqA_iff ht hu).1 he
  rw [e] at hf
  rw [eqOnL_of_eq Five.bs_lt hf hf'] at h
  exact absurd h (by decide)

theorem hmulP : ∀ a ∈ heP, ∀ b ∈ heP, (a * b ∈ heP ↔ (a ∈ heP ↔ b ∈ heP)) :=
  fun a ha b hb => iff_of_true (heP.mul_mem ha hb) (iff_of_true ha hb)

theorem qgens_eq (k : Nat) (hk : k < 2) : heFiveQGens[k]! = unpack 8330 14 (A k) := by
  rw [heFiveQGens]
  interval_cases k
  · rw [lit2_0]
    exact arr_eq 0 (by norm_num)
  · rw [lit2_1]
    exact arr_eq 1 (by norm_num)

theorem qgs : ∀ k < 2, Rep 8330 heFiveQGens[k]! (gp k) := fun k hk => by
  rw [qgens_eq k hk]
  exact rep_gp k (by omega)

theorem qg : ∀ k < 2, RepF 8330 (pa k) (gp k) := fun k hk => repF_pa k (by omega)

theorem qg_inP : ∀ k < 2, gp k ∈ heP := by
  intro k hk
  interval_cases k
  · exact gp_inP 0 (by norm_num) fl_P.1
  · exact gp_inP 1 (by norm_num) fl_P.2.1

theorem tree : TreeOK 2 25 Q.P Q.L := treeOK_of fun i hi h0 => by
  have h := allN_spec kTree i hi
  rwa [beq_zero_false h0] at h

theorem tq_inP {i : Nat} (hi : i < 25) : treePerm gp Q.P Q.L i ∈ heP :=
  (trQ_spec tree hmulP qg_inP (fun k hk => iff_of_true (qg_inP k hk) rfl) (fun _ _ => by decide)
    25 i hi.le hi).1

theorem edges : ∀ i < 25, ∀ k < 2, QE i k < 25 ∧
    treeArr 8330 heFiveQGens Q.P Q.L (QE i k) =
      compA 8330 heFiveQGens[k]! (treeArr 8330 heFiveQGens Q.P Q.L i) :=
  edges_of_edgeAtK tree qg qgs hmulP qg_inP (fun k hk => iff_of_true (qg_inP k hk) rfl)
    (fun _ _ => by decide) Five.bs_lt
    (fun x hx y hy _ hb => Five.faithful x (heP_le_heAutGroup hx) y (heP_le_heAutGroup hy)
      (iff_of_true hx hy) hb) fun i hi => allN_spec kEdge i hi

theorem keys_inj : ∀ a < 25, ∀ b < 25,
    keyA 8330 heFiveKeys (treeArr 8330 heFiveQGens Q.P Q.L a) =
      keyA 8330 heFiveKeys (treeArr 8330 heFiveQGens Q.P Q.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := qkey) fun j hj => allN_spec kSort j hj
  intro a ha b hb e
  rw [keyA_treeArr tree qg qgs Five.keys_lt ha, keyA_treeArr tree qg qgs Five.keys_lt hb] at e
  exact hk a ha b hb e

theorem pts_eq : heFiveQCert.pts =
    Array.ofFn (n := 25) fun i => treeArr 8330 heFiveQGens Q.P Q.L i.val :=
  enumBfs_tree tree qgs (by rfl) (by norm_num) (by norm_num) keys_inj edges kReplay

theorem enum_ok : enumOK 8330 heFiveQGens heFiveKeys heFiveQCert = true :=
  enumOK_tree tree qgs (by rfl) (by norm_num) (by norm_num) keys_inj edges

theorem pt_get {k : Nat} (hk : k < 25) :
    heFiveQCert.pts[k]! = treeArr 8330 heFiveQGens Q.P Q.L k := by
  rw [pts_eq, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem rep_pt {k : Nat} (hk : k < 25) :
    Rep 8330 heFiveQCert.pts[k]! (treePerm gp Q.P Q.L k) := by
  rw [pt_get hk]
  exact rep_treeArr tree qgs k hk

theorem repF_qv {k : Nat} (hk : k < 25) : RepF 8330 (qv k) (treePerm gp Q.P Q.L k) :=
  repF_trV tree qg 25 k hk.le hk

theorem lines : linesOKG 5 25 6 8330 heFiveQGens heFiveKeys heFiveQCert heFiveLines = true := by
  have hN : heFiveQCert.pts.size = 25 := by rw [pts_eq, Array.size_ofFn]
  simp only [linesOKG, Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨⟨⟨⟨⟨enum_ok, hN⟩, fun k hk => ?_⟩, fun k hk => ?_⟩, fun j hj => ?_⟩, fun j hj => ?_⟩
  ·
    have hu := tq_inP hk
    exact eqA_P (rep_powArr (rep_pt hk) 5) rep_idA (RepF.powF (repF_qv hk) 5) RepF.one
      (heP.pow_mem hu 5) heP.one_mem (allN_spec kPow k hk)
  ·
    have hc := allN_spec kCover k hk
    unfold coverAt at hc
    rw [CFSG.KS.SporSch.strictB_val] at hc
    rw [Bool.or_eq_true, List.any_eq_true]
    by_cases hw : QW.getD k 0 = 0
    · rw [hw] at hc
      exact Or.inl (eqA_P (rep_pt hk) rep_idA (repF_qv hk) RepF.one (tq_inP hk) heP.one_mem hc)
    · rw [show Nat.beq (QW.getD k 0) 0 = false from Bool.eq_false_iff.2 fun h =>
        hw (Nat.eq_of_beq_eq_true h)] at hc
      simp only [bAnd_iff, Nat.blt_eq] at hc
      obtain ⟨h1, h2, h3, h4⟩ := hc
      refine Or.inr ⟨QW.getD k 0 / 8, List.mem_range.2 h1, ?_⟩
      rw [List.any_eq_true]
      refine ⟨QW.getD k 0 % 8, List.mem_range.2 h3, ?_⟩
      exact eqA_P (rep_pt hk) (rep_powArr (rep_line _ h1) _) (repF_qv hk)
        (RepF.powF (repF_ln _ h1) _) (tq_inP hk) (heP.pow_mem (lp_inP _ h1) _) h4
  ·
    intro j' hj'
    have hd := allN_spec (allN_spec kDist j hj) j' hj'
    unfold distAt at hd
    rw [Bool.or_eq_true, allLt_iff]
    by_cases e : j = j'
    · exact Or.inl (by simp [e])
    · right
      intro m hm
      rw [show Nat.beq j j' = false from Bool.eq_false_iff.2 fun h => e (Nat.eq_of_beq_eq_true h)]
        at hd
      have h1 := allN_spec hd m hm
      rw [Bool.not_eq_true'] at h1
      rw [Bool.not_eq_true']
      exact neA_P (rep_line j hj) (rep_powArr (rep_line j' hj') m) (repF_ln j hj)
        (RepF.powF (repF_ln j' hj') m) (by simpa using h1)
  ·
    have hl := allN_spec kLine j hj
    unfold lineAt at hl
    simp only [bAnd_iff, Nat.blt_eq, Bool.not_eq_true'] at hl
    obtain ⟨h1, h2, h3, h4⟩ := hl
    refine ⟨⟨⟨CFSG.RankThree.Native.F2.validA_of_rep (rep_line j hj), ?_⟩, ?_⟩, ?_⟩
    · exact eqA_P (rep_powArr (rep_line j hj) 5) rep_idA (RepF.powF (repF_ln j hj) 5) RepF.one
        (heP.pow_mem (lp_inP j hj) 5) heP.one_mem h1
    · rw [Bool.not_eq_true']
      exact neA_P (rep_line j hj) rep_idA (repF_ln j hj) RepF.one h2
    · rw [List.any_eq_true]
      refine ⟨heFiveQCert.pts[LQ.getD j 0]!, ?_, ?_⟩
      · rw [getElem!_pos _ _ (by rw [hN]; exact h3)]
        exact Array.getElem_mem_toList _
      · exact eqA_P (rep_line j hj) (rep_pt h3) (repF_ln j hj) (repF_qv h3) (lp_inP j hj)
          (tq_inP h3) ((eqOnL_iff _ _ _).2 fun b hb => ((eqOnL_iff _ _ _).1 h4 b hb).symm)

theorem qsift : allLt heFiveQGens.size
    (fun l => siftA 8330 heLevels heBase.toArray 0 heFiveQGens[l]!) = true := by
  rw [allLt_iff]
  intro l hl
  have hl2 : l < 2 := hl
  rw [show heLevels = rawLevels 8330 heStrongArrs heBase.toArray from rfl,
    mem_heP_iff_siftA (qgs l hl2)]
  exact qg_inP l hl2

theorem cs_eq (j : Nat) (hj : j < 11) : heFiveCase0Arrs[j]! = unpack 8330 14 (S50.S j) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound S50T.all j hj
  rw [← S50T.eq] at h
  rw [heFiveCase0Arrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  change hexTable 4 8330 (8330 * j) heFiveCase0Hex = _
  rw [h, Nat.eq_of_beq_eq_true (allN_spec k5Bind j hj)]

theorem binds0 : Binds 8330 14 S50.S 11 9 S50.BP heFiveCase0Arrs
    (heFiveCase0Base.map Fin.val).toArray :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [heFiveCase0Arrs], cs_eq, by decide,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec k5Base t ht)⟩

theorem words0 : heFiveCase0Words = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 11 derivs0 := by
  decide

theorem heGen_eq (k : Nat) (hk : k < 2) : heGen k = unpack 8330 14 (HeC.S k) := by
  have h := He2112.gen_eq k hk
  rw [heGenArrs, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn] at h
  exact h

theorem chain0 : caseChainOK3 8330 heFiveCase0Arrs heFiveCase0BaseArr heFiveCase0Words
    (heGen 0) (heGen 1) heUArr = true := by
  have hg := k5Gen
  rw [bAnd_iff] at hg
  have hU : Rep 8330 heFiveCase0Arrs[2]! heAutU := by
    rw [cs_eq 2 (by norm_num)]
    have hall := CFSG.KC.Misc.Clos.forall_of_chunks 833 10 _ fun c hc => by
      have h := allN_spec k5U c hc
      unfold u5B at h
      exact h
    intro x
    rw [Five.unpackGet x.2]
    have h1 := hall x (by omega)
    rw [CFSG.KS.SporSch.blt_true x.2] at h1
    rw [Nat.eq_of_beq_eq_true h1]
    exact Five.hU x x.2
  exact case_chain binds0 S50.head S50.ho (by norm_num) k5Perm words0
    (Nat.eq_of_beq_eq_true k5Prod)
    (by rw [cs_eq 0 (by norm_num), heGen_eq 0 (by norm_num), Nat.eq_of_beq_eq_true hg.1])
    (by rw [cs_eq 1 (by norm_num), heGen_eq 1 (by norm_num), Nat.eq_of_beq_eq_true hg.2]) hU
    (by norm_num)

theorem sift0_iff {g : Array Nat} {G : Equiv.Perm (Fin 8330)} (hG : Rep 8330 g G) :
    siftA 8330 heFiveRLevels heFiveCase0BaseArr 0 g = true ↔ G ∈ heAutGroup :=
  case_sift_iff (by norm_num) (by simp [heFiveCase0Arrs]) (by decide) chain0 hG

theorem faith0 : CFSG.Sporadic.Schreier.BaseFaithful heAutGroup heFiveKeys ∧
    ∀ j < heFiveCase0Arrs.size, permOfArr 8330 heFiveCase0Arrs[j]! ∈ heAutGroup :=
  case_faithful (by norm_num) (by simp [heFiveCase0Arrs]) (by decide) chain0

theorem trans : transOKG 6 8330 heFiveTransporters heFiveLines heFiveRec heFiveRLevels
    heFiveCase0BaseArr = true := by
  unfold transOKG
  rw [allLt_iff]
  intro j hj
  have hH : Rep 8330 heFiveTransporters[j]! (gp (2 + j)) := by
    rw [trans_eq j hj]
    exact rep_gp _ (by omega)
  have hL0 : lp 0 = gp 8 := by
    rw [lp, gp_one, one_mul, inv_one, mul_one]
  have hc := rep_conjA (CFSG.RankThree.Native.F2.validA_of_rep hH) (rep_line 0 (by norm_num))
  rw [CFSG.RankThree.Native.permOfArr_eq_of_rep hH, hL0] at hc
  simp only [Bool.and_eq_true]
  refine ⟨⟨CFSG.RankThree.Native.F2.validA_of_rep hH, (sift0_iff hH).2 (gp_mem _ (by omega)).1⟩,
    ?_⟩
  rw [rec_zero j hj]
  exact (eqA_iff hc (rep_line j hj)).2 rfl

theorem qfacts : (linesOKG 5 25 6 8330 heFiveQGens heFiveKeys heFiveQCert heFiveLines = true ∧
    allLt heFiveQGens.size (fun l => siftA 8330 heLevels heBase.toArray 0 heFiveQGens[l]!) =
      true ∧
    transOKG 6 8330 heFiveTransporters heFiveLines heFiveRec heFiveRLevels heFiveCase0BaseArr =
      true ∧
    allLt 6 (fun j => (List.range 1).any fun i => heFiveRec.getD j 0 == i) = true ∧
    heFiveRec.getD 0 0 = 0) :=
  ⟨lines, qsift, trans, by
    rw [allLt_iff]
    intro j hj
    rw [rec_zero j hj]
    decide, rec_zero 0 (by norm_num)⟩

end CertificateChecks.KernelHeLoc.FiveL

end
