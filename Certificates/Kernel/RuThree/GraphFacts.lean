module

public import Certificates.Kernel.RuThree.GraphT
public import CFSG.Certificates.Kernel.HeLoc.TreeTabSound
public import Certificates.Kernel.RuThree.Facts
public import Certificates.Kernel.Misc.RuThreeM10.Facts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuThree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc CFSG.KC.J2H
open CFSG.KC.B3S3K CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.HexFlat
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
open CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier
open CFSG.Certificates CFSG.Certificates.Native CFSG.EvenSporadicStandard.RuStd.S2

@[expose] noncomputable def gpM (k : Nat) : Equiv.Perm (Fin 11) := permOfArr 11 ruThreeM[k]!

theorem ng3 : KernelMisc.RuThreeM10.ET.ng = 3 :=
  Nat.eq_of_beq_eq_true KernelMisc.RuThreeM10.n0.2.2.2

theorem mUnpack {k : Nat} (hk : k < 3) :
    ruThreeM[k]! = unpack 11 4 (KernelMisc.RuThreeM10.ET.G k) :=
  KernelMisc.RuThreeM10.bindT.2 k (by rw [ng3]; exact hk)

theorem mRep {k : Nat} (hk : k < 3) : Rep 11 ruThreeM[k]! (gpM k) := by
  refine rep_of_validA ?_
  rw [mUnpack hk]
  exact validA_of (KernelMisc.RuThreeM10.pGT k (by rw [ng3]; exact hk))

theorem unpackGet11 {p x : Nat} (hx : x < 11) : (unpack 11 4 p)[x]! = pg 4 (mask 4) p x := by
  rw [unpack, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem mRepF {k : Nat} (hk : k < 3) : RepF 11 (gM k) (gpM k) := fun x hx => by
  rw [← (mRep hk) ⟨x, hx⟩, mUnpack hk, unpackGet11 hx]
  rfl

theorem bs11_lt : ∀ b ∈ bs11, b < 11 := by decide

theorem mem_bs11 (z : Fin 11) : z.val ∈ bs11 := by
  have := z.2
  simp only [bs11, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem eq11 {x y : Equiv.Perm (Fin 11)}
    (h : ∀ b (hb : b ∈ bs11), (x ⟨b, bs11_lt b hb⟩ : Nat) = y ⟨b, bs11_lt b hb⟩) : x = y :=
  Equiv.ext fun z => Fin.ext (h z.val (mem_bs11 z))

theorem eqOnL11 {f g : Nat → Nat} {x y : Equiv.Perm (Fin 11)} (hf : RepF 11 f x)
    (hg : RepF 11 g y) (h : eqOnL bs11 f g = true) : x = y :=
  eq11 fun b hb => by
    rw [← hf b (bs11_lt b hb), ← hg b (bs11_lt b hb)]
    exact (eqOnL_iff bs11 f g).1 h b hb

theorem m0_ok : eqA 11 ruThreeM[0]! (idA 11) = true :=
  (eqA_iff (mRep (by norm_num)) rep_idA).2 (eqOnL11 (mRepF (by norm_num)) RepF.one kM0)

theorem all_bs11 : ∀ x < 11, x ∈ bs11 := by decide

section Ru


theorem mt_repF : ∀ j < 2160, RepF 11 (rd4 (MT j)) (treePerm gpM C0.P C0.L j) :=
  repF_tab ctree (fun k hk => mRepF hk) all_bs11 fun i hi => Orb.allN_iff.1 kTabT i hi

theorem edgesM : ∀ i < 2160, ∀ k < 3, CE i k < 2160 ∧
    treeArr 11 ruThreeM C0.P C0.L (CE i k) =
      compA 11 ruThreeM[k]! (treeArr 11 ruThreeM C0.P C0.L i) :=
  edges_of_edgeTK ctree (fun k hk => mRepF hk) (fun k hk => mRep hk) all_bs11
    (fun i hi => Orb.allN_iff.1 kTabT i hi) fun i hi => Orb.allN_iff.1 kEdgeT i hi

@[expose] noncomputable def gam (i : Nat) : Array Nat :=
  pairArr 4060 11 (treeArr 4060 ruThreeC0Gens C0.P C0.L i) (treeArr 11 ruThreeM C0.P C0.L i)

theorem gam_blk1 (i : Nat) : blk1 4060 (gam i) = treeArr 4060 ruThreeC0Gens C0.P C0.L i :=
  blk1_pairArr (size_treeArr i)

theorem gam_blk2 (i : Nat) : blk2 4060 11 (gam i) = treeArr 11 ruThreeM C0.P C0.L i :=
  blk2_pairArr (size_treeArr i)

theorem gam_zero : gam 0 = prodRoot 4060 11 := by
  rw [gam, treeArr_zero, treeArr_zero, prodRoot]

theorem gam_act {i k : Nat} (hi : i < 2160) (hk : k < 3) :
    prodAct 4060 11 ruThreeC0Gens ruThreeM k (gam i) = gam (CE i k) := by
  rw [prodAct, gam_blk1, gam_blk2, gam, (cedges i hi k hk).2, (edgesM i hi k hk).2]

theorem gam_valid {i : Nat} (hi : i < 2160) : prodValid 4060 11 (gam i) = true := by
  rw [prodValid, gam_blk1, gam_blk2,
    CFSG.RankThree.Native.F2.validA_of_rep (rep_treeArr ctree cgs i hi),
    CFSG.RankThree.Native.F2.validA_of_rep (rep_treeArr ctree (fun k hk => mRep hk) i hi)]
  rfl

theorem gam_key (i : Nat) :
    prodKey 4060 ruThreeKeys (gam i) = keyA 4060 ruThreeKeys (treeArr 4060 ruThreeC0Gens C0.P C0.L i) := by
  rw [prodKey, gam_blk1]

@[expose] noncomputable def GS : Finset (Array Nat) := (Finset.range 2160).image gam

theorem mem_GS (x : Array Nat) : x ∈ GS ↔ ∃ i < 2160, gam i = x := by
  simp [GS]

theorem gam_inj : ∀ a < 2160, ∀ b < 2160, gam a = gam b → a = b := fun a ha b hb e =>
  ckeys_inj a ha b hb (by rw [← gam_key, ← gam_key, e])

theorem card_GS : GS.card = 2160 := by
  rw [GS, Finset.card_image_of_injOn fun a ha b hb e =>
    gam_inj a (by simpa using ha) b (by simpa using hb) e, Finset.card_range]

theorem reach_GS (x : Array Nat) :
    CFSG.KC.Bfs.Reach (prodAct 4060 11 ruThreeC0Gens ruThreeM) ruThreeC0Gens.size
      (prodRoot 4060 11) x ↔ x ∈ GS := by
  constructor
  · intro h
    induction h with
    | root => exact (mem_GS _).2 ⟨0, by norm_num, gam_zero⟩
    | step k hk _ ih =>
      obtain ⟨i, hi, rfl⟩ := (mem_GS _).1 ih
      rw [gsize] at hk
      exact (mem_GS _).2 ⟨CE i k, (cedges i hi k hk).1, (gam_act hi hk).symm⟩
  · intro h
    obtain ⟨i, hi, rfl⟩ := (mem_GS _).1 h
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      rcases Nat.eq_zero_or_pos i with rfl | h0
      · rw [gam_zero]
        exact CFSG.KC.Bfs.Reach.root
      · obtain ⟨hp, hl⟩ := ctree i hi h0
        have e : gam i = prodAct 4060 11 ruThreeC0Gens ruThreeM (C0.L i) (gam (C0.P i)) := by
          rw [prodAct, gam_blk1, gam_blk2, gam, treeArr_pos ⟨h0, hp⟩, treeArr_pos ⟨h0, hp⟩]
        rw [e]
        exact CFSG.KC.Bfs.Reach.step (C0.L i) (by rw [gsize]; exact hl)
          (ih (C0.P i) hp (by omega) ((mem_GS _).2 ⟨C0.P i, by omega, rfl⟩))

theorem gcert_eq : ruThreeGraphCert = arrBfs (prodAct 4060 11 ruThreeC0Gens ruThreeM)
    ruThreeC0Gens.size (prodKey 4060 ruThreeKeys) (prodRoot 4060 11) 2180 := rfl

theorem spec : arrCertOK (prodAct 4060 11 ruThreeC0Gens ruThreeM) ruThreeC0Gens.size
      (prodValid 4060 11) (prodKey 4060 ruThreeKeys) (prodRoot 4060 11) ruThreeGraphCert = true ∧
    (∀ x, x ∈ ruThreeGraphCert.pts ↔ x ∈ GS) ∧ ruThreeGraphCert.pts.size = GS.card := by
  have h := CFSG.KC.Bfs.arrBfs_spec (act := prodAct 4060 11 ruThreeC0Gens ruThreeM)
    (ngen := ruThreeC0Gens.size) (valid := prodValid 4060 11) (key := prodKey 4060 ruThreeKeys)
    (root := prodRoot 4060 11) (fuel := 2180) GS reach_GS
    (fun x hx => by
      obtain ⟨i, hi, rfl⟩ := (mem_GS _).1 hx
      exact gam_valid hi)
    (fun x hx y hy e => by
      obtain ⟨a, ha, rfl⟩ := (mem_GS _).1 hx
      obtain ⟨b, hb, rfl⟩ := (mem_GS _).1 hy
      rw [gam_key, gam_key] at e
      rw [ckeys_inj a ha b hb e])
    (by rw [card_GS]; norm_num)
  rw [gcert_eq]
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem graph_ok : prodOK 4060 11 ruThreeC0Gens ruThreeM ruThreeKeys ruThreeGraphCert = true := by
  simp only [prodOK, Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨⟨by rw [gsize]; rfl, fun k hk => ?_⟩, spec.1⟩
  rw [gsize] at hk
  rw [CFSG.RankThree.Native.F2.validA_of_rep (cgs k hk),
    CFSG.RankThree.Native.F2.validA_of_rep (mRep hk)]
  exact ⟨rfl, rfl⟩

theorem size_ok : ruThreeGraphCert.pts.size = 2160 := by
  rw [spec.2.2, card_GS]

theorem tree_rep (j : Nat) (hj : j < 2160) :
    Rep 4060 (treeArr 4060 ruThreeC0Gens C0.P C0.L j) (treePerm gpC C0.P C0.L j) :=
  rep_treeArr ctree cgs j hj

theorem cv_repF (j : Nat) (hj : j < 2160) : RepF 4060 (cv j) (treePerm gpC C0.P C0.L j) :=
  repF_trV ctree cg 2160 j hj.le hj

theorem ker_at {j : Nat} (hj : j < 2160) :
    (!eqA 11 (treeArr 11 ruThreeM C0.P C0.L j) (idA 11) ||
      eqA 4060 (treeArr 4060 ruThreeC0Gens C0.P C0.L j) (idA 4060) ||
      eqA 4060 (treeArr 4060 ruThreeC0Gens C0.P C0.L j) ruThreeLines[0]! ||
      eqA 4060 (treeArr 4060 ruThreeC0Gens C0.P C0.L j)
        (compA 4060 ruThreeLines[0]! ruThreeLines[0]!)) = true := by
  have hk := Orb.allN_iff.1 kKerT j hj
  unfold kerAtT at hk
  rw [strictB_tab] at hk
  unfold kerAt at hk
  have hrM := rep_treeArr ctree (fun k hk => mRep hk) j hj
  have hfM := mt_repF j hj
  cases h1 : eqOnL bs11 (rd4 (MT j)) (fun y => y)
  · have e : eqA 11 (treeArr 11 ruThreeM C0.P C0.L j) (idA 11) = false := by
      cases h2 : eqA 11 (treeArr 11 ruThreeM C0.P C0.L j) (idA 11)
      · rfl
      · have he := (eqA_iff hrM rep_idA).1 h2
        rw [eqOnL_of_eq bs11_lt hfM (he ▸ RepF.one)] at h1
        exact absurd h1 (by decide)
    rw [e]
    rfl
  · rw [h1] at hk
    have hm := c_mem hj
    cases h2 : eqOnL bs (cv j) (fun y => y)
    · rw [h2] at hk
      cases h3 : eqOnL bs (cv j) x0
      · rw [h3] at hk
        have e := eqOnL_rep (tree_rep j hj) (rep_compA x0_rep x0_rep) (cv_repF j hj)
          (x0_repF.comp x0_repF) hm (ruP.mul_mem x0_mem x0_mem) hk
        rw [e]
        simp
      · have e := eqOnL_rep (tree_rep j hj) x0_rep (cv_repF j hj) x0_repF hm x0_mem h3
        rw [e]
        simp
    · have e := eqOnL_rep (tree_rep j hj) rep_idA (cv_repF j hj) RepF.one hm ruP.one_mem h2
      rw [e]
      simp

theorem ker_ok : ruThreeKernelOK = true := by
  rw [ruThreeKernelOK, allLt_iff]
  intro i hi
  have hmem : ruThreeGraphCert.pts[i]! ∈ GS := by
    refine (spec.2.1 _).1 ?_
    rw [getElem!_pos _ i hi]
    exact Array.getElem_mem hi
  obtain ⟨j, hj, hje⟩ := (mem_GS _).1 hmem
  rw [← hje, gam_blk1, gam_blk2]
  exact ker_at hj

open CFSG.EvenSporadicStandard.RuStd.S2 CFSG.RankThree.PartOne CFSG.RankThree.Native
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.RuSchreier in
open Certificates in
theorem ok24947 :
    prodOK 4060 11 ruThreeC0Gens ruThreeM ruThreeKeys ruThreeGraphCert = true ∧
      ruThreeGraphCert.pts.size = 2160 ∧ ruThreeKernelOK = true ∧
      eqA 11 ruThreeM[0]! (idA 11) = true :=
  ⟨graph_ok, size_ok, ker_ok, m0_ok⟩

end Ru

end CertificateChecks.KernelRuThree

end
