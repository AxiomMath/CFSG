module

public import Certificates.Kernel.HeLoc.SevenBase
public import Certificates.Kernel.HeLoc.SevenQ
public import Certificates.Kernel.HeLoc.Seven0ChainK
public import Certificates.Kernel.HeLoc.ChainFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB CFSG.RankThree.Native
open CFSG.RankThree.PartOne CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Mathieu
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch


theorem fl_rep : FL.getD 59 0 = 0 ∧ FL.getD 65 0 = 0 ∧ FL.getD 70 0 = 0 ∧ FL.getD 0 0 = 0 ∧
    FL.getD 1 0 = 0 := by decide

theorem rep_inP (i : Nat) (hi : i < 3) : gp (repIx i) ∈ heP := by
  have h := fl_rep
  interval_cases i
  · exact (gp_mem 59 (by norm_num)).2.2 h.1
  · exact (gp_mem 65 (by norm_num)).2.2 h.2.1
  · exact (gp_mem 70 (by norm_num)).2.2 h.2.2.1

theorem rc_lt (j : Nat) : rc j < 3 := Nat.mod_lt _ (by norm_num)

theorem lp_inP (j : Nat) (hj : j < 57) : lp j ∈ heP := by
  have hh := (gp_mem (2 + j) (by omega)).1
  have hr := rep_inP (rc j) (rc_lt j)
  rw [lp, he_mul_mem_iff (heAutGroup.mul_mem hh (heP_le_heAutGroup hr)) (heAutGroup.inv_mem hh),
    he_mul_mem_iff hh (heP_le_heAutGroup hr), inv_mem_iff]
  constructor
  · intro h
    exact h.2 hr
  · intro h
    exact ⟨fun _ => hr, fun _ => h⟩

theorem qgens_eq (k : Nat) (hk : k < 2) : heSevenQGens[k]! = unpack 8330 14 (A k) := by
  rw [heSevenQGens]
  interval_cases k
  · rw [lit2_0]
    exact arr_eq 0 (by norm_num)
  · rw [lit2_1]
    exact arr_eq 1 (by norm_num)

theorem qgs : ∀ k < 2, Rep 8330 heSevenQGens[k]! (gp k) := fun k hk => by
  rw [qgens_eq k hk]
  exact rep_gp k (by omega)

theorem qg : ∀ k < 2, RepF 8330 (pa k) (gp k) := fun k hk => repF_pa k (by omega)

theorem qg_inP : ∀ k < 2, gp k ∈ heP := by
  intro k hk
  interval_cases k
  · exact (gp_mem 0 (by norm_num)).2.2 fl_rep.2.2.2.1
  · exact (gp_mem 1 (by norm_num)).2.2 fl_rep.2.2.2.2

theorem hmulP : ∀ a ∈ heP, ∀ b ∈ heP, (a * b ∈ heP ↔ (a ∈ heP ↔ b ∈ heP)) :=
  fun a ha b hb => iff_of_true (heP.mul_mem ha hb) (iff_of_true ha hb)

theorem tree : TreeOK 2 343 Q.P Q.L := treeOK_of fun i hi h0 => by
  have h := allN_spec kTree i hi
  rwa [beq_zero_false h0] at h

theorem tq_inP {i : Nat} (hi : i < 343) : treePerm gp Q.P Q.L i ∈ heP :=
  (trQ_spec tree hmulP qg_inP (fun k hk => iff_of_true (qg_inP k hk) rfl) (fun _ _ => by decide)
    343 i hi.le hi).1

theorem edges : ∀ i < 343, ∀ k < 2, QE i k < 343 ∧
    treeArr 8330 heSevenQGens Q.P Q.L (QE i k) =
      compA 8330 heSevenQGens[k]! (treeArr 8330 heSevenQGens Q.P Q.L i) :=
  edges_of_edgeAtK tree qg qgs hmulP qg_inP (fun k hk => iff_of_true (qg_inP k hk) rfl)
    (fun _ _ => by decide) bs_lt
    (fun x hx y hy _ hb => faithful x (heP_le_heAutGroup hx) y (heP_le_heAutGroup hy)
      (iff_of_true hx hy) hb) fun i hi => allN_spec kEdge i hi

theorem keys_lt : ∀ p ∈ heSevenKeys, p < 8330 := by decide

theorem keys_inj : ∀ a < 343, ∀ b < 343,
    keyA 8330 heSevenKeys (treeArr 8330 heSevenQGens Q.P Q.L a) =
      keyA 8330 heSevenKeys (treeArr 8330 heSevenQGens Q.P Q.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := qkey) fun j hj => allN_spec kSort j hj
  intro a ha b hb e
  rw [keyA_treeArr tree qg qgs keys_lt ha, keyA_treeArr tree qg qgs keys_lt hb] at e
  exact hk a ha b hb e

theorem pts_eq : heSevenQCert.pts =
    Array.ofFn (n := 343) fun i => treeArr 8330 heSevenQGens Q.P Q.L i.val :=
  enumBfs_tree tree qgs (by rfl) (by norm_num) (by norm_num) keys_inj edges kReplay

theorem enum_ok : enumOK 8330 heSevenQGens heSevenKeys heSevenQCert = true :=
  enumOK_tree tree qgs (by rfl) (by norm_num) (by norm_num) keys_inj edges

theorem pt_get {k : Nat} (hk : k < 343) :
    heSevenQCert.pts[k]! = treeArr 8330 heSevenQGens Q.P Q.L k := by
  rw [pts_eq, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem rep_pt {k : Nat} (hk : k < 343) :
    Rep 8330 heSevenQCert.pts[k]! (treePerm gp Q.P Q.L k) := by
  rw [pt_get hk]
  exact rep_treeArr tree qgs k hk

theorem repF_qv {k : Nat} (hk : k < 343) : RepF 8330 (qv k) (treePerm gp Q.P Q.L k) :=
  repF_trV tree qg 343 k hk.le hk

theorem eqA_P {t u : Array Nat} {x y : Equiv.Perm (Fin 8330)} {f f' : Nat → Nat}
    (ht : Rep 8330 t x) (hu : Rep 8330 u y) (hf : RepF 8330 f x) (hf' : RepF 8330 f' y)
    (hx : x ∈ heP) (hy : y ∈ heP) (h : eqOnL bs f f' = true) : eqA 8330 t u = true :=
  (eqA_iff ht hu).2 (eq_of_P hf hf' hx hy h)

theorem neA_P {t u : Array Nat} {x y : Equiv.Perm (Fin 8330)} {f f' : Nat → Nat}
    (ht : Rep 8330 t x) (hu : Rep 8330 u y) (hf : RepF 8330 f x) (hf' : RepF 8330 f' y)
    (h : eqOnL bs f f' = false) : eqA 8330 t u = false := by
  rw [Bool.eq_false_iff]
  intro he
  have e := (eqA_iff ht hu).1 he
  rw [e] at hf
  rw [eqOnL_of_eq bs_lt hf hf'] at h
  exact absurd h (by decide)

theorem lines : linesOKG 7 343 57 8330 heSevenQGens heSevenKeys heSevenQCert heSevenLines =
    true := by
  have hN : heSevenQCert.pts.size = 343 := by rw [pts_eq, Array.size_ofFn]
  simp only [linesOKG, Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨⟨⟨⟨⟨enum_ok, hN⟩, fun k hk => ?_⟩, fun k hk => ?_⟩, fun j hj => ?_⟩, fun j hj => ?_⟩
  ·
    have hu := tq_inP hk
    exact eqA_P (rep_powArr (rep_pt hk) 7) rep_idA (RepF.powF (repF_qv hk) 7) RepF.one
      (heP.pow_mem hu 7) heP.one_mem (allN_spec kPow k hk)
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
    have hd := allN_spec (if h : j < 19 then by exact allN_spec kDist0 j h
      else if h' : j < 38 then by
        have := allN_spec kDist1 (j - 19) (by omega)
        rwa [show Nat.add 19 (j - 19) = j by change 19 + _ = _; omega] at this
      else by
        have := allN_spec kDist2 (j - 38) (by omega)
        rwa [show Nat.add 38 (j - 38) = j by change 38 + _ = _; omega] at this) j' hj'
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
    · exact eqA_P (rep_powArr (rep_line j hj) 7) rep_idA (RepF.powF (repF_ln j hj) 7) RepF.one
        (heP.pow_mem (lp_inP j hj) 7) heP.one_mem h1
    · rw [Bool.not_eq_true']
      exact neA_P (rep_line j hj) rep_idA (repF_ln j hj) RepF.one h2
    · rw [List.any_eq_true]
      refine ⟨heSevenQCert.pts[LQ.getD j 0]!, ?_, ?_⟩
      · rw [getElem!_pos _ _ (by rw [hN]; exact h3)]
        exact Array.getElem_mem_toList _
      · exact eqA_P (rep_line j hj) (rep_pt h3) (repF_ln j hj) (repF_qv h3) (lp_inP j hj)
          (tq_inP h3) ((eqOnL_iff _ _ _).2 fun b hb => ((eqOnL_iff _ _ _).1 h4 b hb).symm)

theorem cs_eq (j : Nat) (hj : j < 10) : heSevenCase0Arrs[j]! = unpack 8330 14 (S70.S j) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound S70T.all j hj
  rw [← S70T.eq] at h
  rw [heSevenCase0Arrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  change hexTable 4 8330 (8330 * j) heSevenCase0Hex = _
  rw [h, Nat.eq_of_beq_eq_true (allN_spec k0Bind j hj)]

theorem binds0 : Binds 8330 14 S70.S 10 14 S70.BP heSevenCase0Arrs
    (heSevenCase0Base.map Fin.val).toArray :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [heSevenCase0Arrs], cs_eq, by decide,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec k0Base t ht)⟩

theorem words0 : heSevenCase0Words = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 10 derivs0 := by
  decide

theorem heGen_eq (k : Nat) (hk : k < 2) : heGen k = unpack 8330 14 (HeC.S k) := by
  have h := He2112.gen_eq k hk
  rw [heGenArrs, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn] at h
  exact h

theorem chain0 : caseChainOK3 8330 heSevenCase0Arrs heSevenCase0BaseArr heSevenCase0Words
    (heGen 0) (heGen 1) heUArr = true := by
  have hg := k0Gen
  rw [bAnd_iff] at hg
  have hU : Rep 8330 heSevenCase0Arrs[2]! heAutU := by
    rw [cs_eq 2 (by norm_num)]
    have hall := CFSG.KC.Misc.Clos.forall_of_chunks 833 10 _ fun c hc => by
      have h := allN_spec k0U c hc
      unfold u0B at h
      exact h
    intro x
    rw [Five.unpackGet x.2]
    have h1 := hall x (by omega)
    rw [CFSG.KS.SporSch.blt_true x.2] at h1
    rw [Nat.eq_of_beq_eq_true h1]
    exact Five.hU x x.2
  exact case_chain binds0 S70.head S70.ho (by norm_num) k0Perm words0
    (Nat.eq_of_beq_eq_true k0Prod)
    (by rw [cs_eq 0 (by norm_num), heGen_eq 0 (by norm_num), Nat.eq_of_beq_eq_true hg.1])
    (by rw [cs_eq 1 (by norm_num), heGen_eq 1 (by norm_num), Nat.eq_of_beq_eq_true hg.2]) hU
    (by norm_num)

theorem sift0_iff {g : Array Nat} {G : Equiv.Perm (Fin 8330)} (hG : Rep 8330 g G) :
    siftA 8330 heSevenRLevels heSevenCase0BaseArr 0 g = true ↔ G ∈ heAutGroup :=
  case_sift_iff (by norm_num) (by simp [heSevenCase0Arrs]) (by decide) chain0 hG

theorem gp_one (r : Nat) (hr : r < 3) : gp (2 + r) = 1 := by
  have h := allN_spec kId r hr
  have hA : A (2 + r) = pidn 8330 14 := Nat.eq_of_beq_eq_true h
  refine (repF_pa (2 + r) (by omega)).unique fun x hx => ?_
  rw [pa, hA, CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) hx]
  rfl

theorem rec_small : ∀ r < 3, heSevenRec.getD r 0 = r := by decide

theorem trans : transOKG 57 8330 heSevenTransporters heSevenLines heSevenRec heSevenRLevels
    heSevenCase0BaseArr = true := by
  unfold transOKG
  rw [allLt_iff]
  intro j hj
  have hH : Rep 8330 heSevenTransporters[j]! (gp (2 + j)) := by
    rw [trans_eq j hj]
    exact rep_gp _ (by omega)
  have hr := rec_lt j hj
  set r := heSevenRec.getD j 0 with hrdef
  have hr57 : r % 57 = r := Nat.mod_eq_of_lt (by omega)
  have hr3 : rc j = r := Nat.mod_eq_of_lt hr
  have hLr : lp r = gp (repIx r) := by
    rw [lp, gp_one r hr, one_mul, inv_one, mul_one]
    have : rc r = r := by
      unfold rc
      rw [rec_small r hr]
      exact Nat.mod_eq_of_lt hr
    rw [this]
  have hc := rep_conjA (CFSG.RankThree.Native.F2.validA_of_rep hH) (rep_line r (by omega))
  rw [CFSG.RankThree.Native.permOfArr_eq_of_rep hH, hLr] at hc
  simp only [Bool.and_eq_true]
  refine ⟨⟨CFSG.RankThree.Native.F2.validA_of_rep hH, (sift0_iff hH).2 (gp_mem _ (by omega)).1⟩, ?_⟩
  rw [hr57]
  refine (eqA_iff hc (rep_line j hj)).2 ?_
  rw [lp, hr3]

open Certificates in
open CFSG.RankThree.PartOne CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB in
theorem facts :
    linesOKG 7 343 57 8330 heSevenQGens heSevenKeys heSevenQCert heSevenLines = true ∧
      allLt heSevenQGens.size (fun l => siftA 8330 heLevels heBase.toArray 0 heSevenQGens[l]!) =
        true ∧
      transOKG 57 8330 heSevenTransporters heSevenLines heSevenRec heSevenRLevels
        heSevenCase0BaseArr = true ∧
      allLt 57 (fun j => (List.range 3).any fun i => heSevenRec.getD j 0 == i) = true ∧
      heSevenRec.getD 0 0 = 0 ∧
      heSevenRec.getD 1 0 = 1 ∧
      heSevenRec.getD 2 0 = 2 := by
  refine ⟨lines, ?_, trans, ?_, rec_small 0 (by norm_num), rec_small 1 (by norm_num),
    rec_small 2 (by norm_num)⟩
  rotate_left
  · rw [allLt_iff]
    intro j hj
    rw [List.any_eq_true]
    exact ⟨_, List.mem_range.2 (rec_lt j hj), beq_self_eq_true _⟩
  rw [allLt_iff]
  intro l hl
  have hl2 : l < 2 := hl
  rw [show heLevels = rawLevels 8330 heStrongArrs heBase.toArray from rfl,
    mem_heP_iff_siftA (qgs l hl2)]
  exact qg_inP l hl2

end CertificateChecks.KernelHeLoc.Seven

end
