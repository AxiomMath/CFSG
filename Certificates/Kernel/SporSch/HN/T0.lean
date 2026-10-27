module

public import Certificates.Kernel.SporSch.HN.T0Rec
public import Certificates.Kernel.SporSch.HN.T0Cl0
public import Certificates.Kernel.SporSch.HN.T0Cl1
public import Certificates.Kernel.SporSch.HN.T0Cl2
public import Certificates.Kernel.SporSch.HN.T0Cl3
public import Certificates.Kernel.SporSch.HN.T0Pts
public import Certificates.Kernel.SporSch.HN.T0Inv
public import Certificates.Kernel.SporSch.HN.T0Adj0
public import Certificates.Kernel.SporSch.HN.T0Adj1
public import Certificates.Kernel.SporSch.HN.T0Rank
public import Certificates.Kernel.SporSch.HN.PtCR
public import Certificates.Kernel.SporSch.HN.Pt2085
public import CFSG.Certificates.Kernel.SporSch.HNT0Pts
public import CFSG.Certificates.Kernel.SporSch.HNT0Rank
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporHNT0
public import Certificates.Certificate2087
public import Certificates.Certificate2094
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107
import CFSG.Certificates.Kernel.Common.ForallTree
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import CFSG.Certificates.Kernel.BfsPinSound

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSporSch.HNT0

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS CFSG.KS.EnumBase CFSG.KS.SporSch CFSG.KS.Ord
open CFSG.KD.HNT0 CFSG.KS.HNT0 CFSG.KD.LgHNX
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore CFSG.KS.HNArr
open CFSG.LocalAnalysis.UniquenessCase.UC22.F10.HNRank
open CertificateChecks.KernelSporSch.HNPtC (gcode letR genR letR_gcode genR_mat wordGT_mat T4_mat
  letters_c4)
open Matrix

local notation "OMat" => ordMat 5 133 13 1729

#kc_forall_tree recAll (fun s => sliceK 16384 64 (recK 192 8 255 4 G T PL) s = true) 256
  CertificateChecks.KernelSporSch.HNT0.ch10509r
#kc_forall_tree clAll (fun s => sliceK 16384 64 (clK 192 8 255 4 16384 G T POS) s = true) 256
  CertificateChecks.KernelSporSch.HNT0.ch10509c
#kc_forall_tree censAll (fun s => strictB (maskL INV)
  (fun IM => sliceK 16384 1024 (censK 8 255 BP T IM) s) = true) 16
  CertificateChecks.KernelSporSch.HNT0.ch10509v
#kc_forall_tree adjAll (fun s => sliceK 687 8 (adjK 687 8 255 BP 24 IL AL PR KB) s = true) 86
  CertificateChecks.KernelSporSch.HNT0.ch10509a
#kc_forall_tree subAll (fun j => subK AL PR DF DFO ZP j = true) 343
  CertificateChecks.KernelSporSch.HNT0.ch10509d

theorem rec_ok : ∀ k < 16384, recK 192 8 255 4 G T PL k = true :=
  sliceK_spec (L := 64) (S := 256) (by norm_num) (by norm_num) recAll

theorem cl_ok : ∀ k < 16384, clK 192 8 255 4 16384 G T POS k = true :=
  sliceK_spec (L := 64) (S := 256) (by norm_num) (by norm_num) clAll

theorem cens_ok : ∀ k < 16384, censK 8 255 BP T (maskL INV) k = true :=
  sliceK_spec (L := 1024) (S := 16) (by norm_num) (by norm_num) fun s hs => by
    have := censAll s hs
    rwa [strictB_eq] at this

theorem adj_ok : ∀ a < 687, adjK 687 8 255 BP 24 IL AL PR KB a = true :=
  sliceK_spec (L := 8) (S := 86) (by norm_num) (by norm_num) adjAll

theorem om_facts : OM.length = 192 ∧ (∀ x ∈ OM, x < 1140000) ∧
    ∀ i < 192, ∀ j < 192, OM.getD i 0 = OM.getD j 0 → i = j :=
  omK_spec (by norm_num) om

theorem om21 : ∀ x ∈ OM, x < 2 ^ 21 := fun x hx => by
  have := om_facts.2.1 x hx
  omega

theorem om_lt (i : ℕ) : OM.getD i 0 < nPts := by
  rcases Nat.lt_or_ge i OM.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    exact om_facts.2.1 _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]
    norm_num

noncomputable def pt (i : ℕ) : X := ⟨OM.getD i 0, om_lt i⟩

theorem vL_pt (i : ℕ) :
    vL (pt i : ℕ) = HNXP.xvec TX (OM.getD i 0) := by
  change vL (OM.getD i 0) = _
  rw [vL_eq (om_lt i), HNPt2103.PK_eq (om_lt i)]

theorem pt_inj : ∀ i < 192, ∀ j < 192, pt i = pt j → i = j := fun i hi j hj e =>
  om_facts.2.2 i hi j hj (congrArg Fin.val e)

theorem rep_of_pts {g : JH} {W t : ℕ} (hW : Canon 5 133 13 W)
    (hm : OMat W = matJ g) (h : ptsK 192 TX MS CM3 M W OM t = true) : Rep pt 192 g t := by
  have hs := ptsK_sound HNPt2103.consts_parts.1 HNPt2103.consts_parts.2 hW om21 h
  intro i hi
  refine ⟨(hs i hi).1, vL_injective ?_⟩
  rw [← mat_vL, vL_pt, vL_pt, (hs i hi).2, hm]

theorem faithful_of {p : ℕ → X} {v : ℕ → Fin 133 → ZMod 5} {n : ℕ} {RK : List ℕ}
    {R : Matrix (Fin 133) (Fin 133) (ZMod 5)} (hp : ∀ i, vL (p i : ℕ) = v i)
    (hlen : RK.length = 133) (hlt : ∀ x ∈ RK, x < n)
    (hRI : ∀ r < 133, R *ᵥ v (RK.getD r 0) = fun l => if l.val = r then 1 else 0) :
    ∀ g h : JH, (∀ i < n, g • p i = h • p i) → g = h := by
  intro g h e
  apply matJ_injective
  set B : Matrix (Fin 133) (Fin 133) (ZMod 5) := Matrix.of fun r k => v (RK.getD k 0) r
  have hRB : R * B = 1 := by
    ext l k
    have e1 := congrFun (hRI k k.isLt) l
    simp only [Matrix.mulVec, dotProduct] at e1
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [B, Matrix.of_apply]
    rw [e1]
    by_cases hlk : l = k
    · rw [if_pos (congrArg Fin.val hlk), if_pos hlk]
    · rw [if_neg (fun e => hlk (Fin.ext e)), if_neg hlk]
  have hBR : B * R = 1 := (mul_eq_one_comm (M := Matrix (Fin 133) (Fin 133) (ZMod 5))).mp hRB
  have hgB : matJ g * B = matJ h * B := by
    ext r k
    have hk : RK.getD k 0 < n := by
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact k.isLt)]
      exact hlt _ (List.getElem_mem _)
    have e1 : vL ((g • p (RK.getD k 0) : X) : ℕ) = vL ((h • p (RK.getD k 0) : X) : ℕ) := by
      rw [e _ hk]
    rw [← mat_vL, ← mat_vL, hp] at e1
    have e2 := congrFun e1 r
    simp only [Matrix.mulVec, dotProduct] at e2
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [B, Matrix.of_apply]
    exact e2
  calc matJ g = matJ g * B * R := by rw [Matrix.mul_assoc, hBR, Matrix.mul_one]
    _ = matJ h * B * R := by rw [hgB]
    _ = matJ h := by rw [Matrix.mul_assoc, hBR, Matrix.mul_one]

theorem faithful : ∀ g h : JH, (∀ i < 192, g • pt i = h • pt i) → g = h := by
  obtain ⟨hlen, hlt, -, hRI⟩ := rankK_sound HNPt2103.consts_parts.1 (by norm_num) om21 rank
  exact faithful_of vL_pt hlen hlt hRI

noncomputable def gens (j : ℕ) : JH :=
  CFSG.KS.HNArr.wJ g4 (t0Words.getD j [])

theorem genR_g4 {j : ℕ} (hj : j < 10) :
    genR j = jR (g4 j) := by
  rw [genR, g4]
  rcases Nat.lt_or_ge j 9 with h9 | h9
  · rw [if_pos h9, if_pos h9]
    exact congrArg jR (HNPt2085.wJ_sL _ (letters_c4.2.1 j h9))
  · obtain rfl : j = 9 := by omega
    rw [if_neg (by omega), if_pos rfl, if_neg (by omega), x4J, HNPt2085.seedWordJ_eq]
    exact congrArg (fun x => jR (seedJ InvData.x4Root * x)) (HNPt2085.wJ_sL _ letters_c4.2.2.1)

theorem letR_lJ {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ 10) : letR (gcode l) = jR (lJ g4 l) := by
  rw [letR_gcode ⟨hl.1, by omega⟩, lJ]
  by_cases hp : 0 < l
  · rw [if_pos hp, if_pos hp, genR_g4 (by omega)]
  · rw [if_neg hp, if_neg hp, genR_g4 (by omega), map_inv]

theorem prod_letR : ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 10) →
      ((w.map gcode).map letR).prod = jR (CFSG.KS.HNArr.wJ g4 w)
  | [], _ => by rw [List.map_nil, List.map_nil, List.prod_nil, CFSG.KS.HNArr.wJ, map_one]
  | l :: w, hw => by
    rw [List.map_cons, List.map_cons, List.prod_cons, CFSG.KS.HNArr.wJ, map_mul,
      letR_lJ (hw l List.mem_cons_self),
      prod_letR w fun z hz => hw z (List.mem_cons_of_mem l hz)]

theorem t0_codes : t0Words.map (List.map gcode) =
    [[20, 3, 9, 9, 7, 20], [18, 20, 4], [20, 4, 9, 9, 6, 20], [5]] := by
  decide +kernel

theorem t0_letters : ∀ w ∈ t0Words, ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 10 := by
  decide +kernel

theorem rep_gens : ∀ j < 4, Rep pt 192 (gens j) (G j) := by
  have key : ∀ j < 4, ∀ cs : List ℕ, (t0Words.getD j []).map gcode = cs →
      ptsK 192 TX MS CM3 M (wordC CFSG.KD.HNPtC.GT cs) OM (G j) = true →
      Rep pt 192 (gens j) (G j) := by
    intro j hj cs hcs h
    have hw : t0Words.getD j [] ∈ t0Words := by
      rw [List.getD_eq_getElem _ _ (by simpa [t0Words] using hj)]
      exact List.getElem_mem _
    have hc : ∀ c ∈ cs, c < 22 := by
      rw [← hcs]
      intro c hc
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hc
      have := t0_letters _ hw l hl
      unfold gcode
      split <;> omega
    obtain ⟨h1, h2⟩ := wordGT_mat cs hc
    refine rep_of_pts h1 ?_ h
    rw [h2, ← hcs, prod_letR _ (t0_letters _ hw), matR_jR]
    rfl
  intro j hj
  interval_cases j
  · exact key 0 (by norm_num) _ rfl pts_w0
  · exact key 1 (by norm_num) _ rfl pts_w1
  · exact key 2 (by norm_num) _ rfl pts_w2
  · exact key 3 (by norm_num) _ rfl pts_w3

theorem rep_t4 : Rep pt 192 t4J GT4 := by
  obtain ⟨h1, h2⟩ := T4_mat
  refine rep_of_pts h1 ?_ pts_t4
  rw [h2, t4J_eq]
  exact congrArg matJ (HNPt2085.wJ_sL _ letters_c4.2.2.2.2)

theorem exists_el : ∀ k < 16384, ∃ g ∈ genSub gens 4, Rep pt 192 g (T k) :=
  exists_rep (by norm_num) rep_gens rec_ok

noncomputable def el (k : ℕ) : JH :=
  if h : k < 16384 then Classical.choose (exists_el k h) else 1

theorem el_spec {k : ℕ} (hk : k < 16384) : el k ∈ genSub gens 4 ∧ Rep pt 192 (el k) (T k) := by
  rw [el, dif_pos hk]
  exact Classical.choose_spec (exists_el k hk)

theorem bp_lt : ∀ p ∈ BP, p < 192 := by decide +kernel

theorem el_inj_base : ∀ k < 16384, ∀ l < 16384,
    (∀ p ∈ BP, el k • pt p = el l • pt p) → k = l :=
  enum_inj pt_inj keys bp_lt fun k hk => (el_spec hk).2

theorem el_surj : ∀ x ∈ genSub gens 4, ∃ k < 16384, el k = x :=
  enum_surj (by norm_num) faithful rep_gens (by norm_num) rec_ok cl_ok fun k hk => (el_spec hk).2

theorem el_inj : ∀ k < 16384, ∀ l < 16384, el k = el l → k = l :=
  fun k hk l hl e => el_inj_base k hk l hl fun p _ => by rw [e]

theorem enumFacts : EnumFacts pt 192 16384 4 gens el BP T where
  rep := fun k hk => (el_spec hk).2
  mem := fun k hk => (el_spec hk).1
  surj := el_surj
  base := fun _ hx _ hy h => eq_of_base el_surj el_inj_base hx hy h
  ptinj := pt_inj
  bp := bp_lt

theorem el_eq {k : ℕ} (hk : k < 16384) {g : JH} {t : ℕ} (hg : Rep pt 192 g t) (ht : T k = t) :
    el k = g :=
  eq_of_rep faithful (el_spec hk).2 (by rw [ht]; exact hg)

theorem genSub_eq : genSub gens 4 = hnT0 := by
  have hT4 : bAnd(Nat.blt T4I 16384, Nat.beq (T T4I) GT4) = true := t4i
  rw [bAnd_eq, Bool.and_eq_true, blt_eq, decide_eq_true_eq] at hT4
  refine le_antisymm ?_ ?_
  · rw [genSub, hnT0, Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    refine Subgroup.subset_closure ?_
    simp only [t0Gens, Set.mem_setOf_eq, List.mem_cons, List.mem_map]
    refine Or.inr ⟨t0Words.getD j [], ?_, rfl⟩
    rw [List.getD_eq_getElem _ _ (by simpa [t0Words] using hj)]
    exact List.getElem_mem _
  · rw [hnT0, Subgroup.closure_le]
    intro x hx
    simp only [t0Gens, Set.mem_setOf_eq, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨w, hw, rfl⟩
    · rw [← el_eq hT4.1 rep_t4 (Nat.eq_of_beq_eq_true hT4.2)]
      exact (el_spec hT4.1).1
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
      refine Subgroup.subset_closure ⟨j, by simpa [t0Words] using hj, ?_⟩
      rw [gens, List.getD_eq_getElem _ _ hj]

theorem inv_zp : el (INV.getD ZP 0) = t4J := by
  have hz : bAnd(Nat.blt ZP 687, Nat.beq (IL ZP) GT4) = true := zp
  rw [bAnd_eq, Bool.and_eq_true, blt_eq, decide_eq_true_eq] at hz
  have hlen : INV.length = 687 := by rw [← lenK_eq]; exact Nat.eq_of_beq_eq_true inv_len
  obtain ⟨-, hlt, hf⟩ := invLK_spec INV 0 0 inv_list
  have hzl : ZP < INV.length := by omega
  have e : INV.getD ZP 0 = INV[ZP] := by simp [List.getD_eq_getElem?_getD, hzl]
  have h1 := (hf ZP hzl).1
  rw [Nat.zero_add, Nat.eq_of_beq_eq_true hz.2] at h1
  rw [e]
  exact el_eq (hlt _ (List.getElem_mem hzl)).2 rep_t4 h1.symm

theorem facts : HNT0Facts := by
  have hlen : INV.length = 687 := by rw [← lenK_eq]; exact Nat.eq_of_beq_eq_true inv_len
  have hz : bAnd(Nat.blt ZP 687, Nat.beq (IL ZP) GT4) = true := zp
  rw [bAnd_eq, Bool.and_eq_true, blt_eq, decide_eq_true_eq] at hz
  have hzQ : ∀ x ∈ genSub gens 4, x * el (INV.getD ZP 0) = el (INV.getD ZP 0) * x := by
    intro x hx
    rw [inv_zp]
    have hx' : x ∈ hnT0 := by
      rw [← genSub_eq]
      exact hx
    have := hnT0_le_centralizer hx'
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  obtain ⟨h1, h2, h3⟩ := enumFacts.rank_facts el_inj cens_ok inv_list hlen (by norm_num) adj_ok
    hz.1 hzQ root subAll eb
  have hcard := card_genSub (fun k hk => (el_spec hk).1) el_surj el_inj
  rw [genSub_eq] at h1 h2 h3 hcard
  rw [inv_zp] at h2
  exact ⟨by rw [hcard]; norm_num, h1, h2, h3⟩

end CertificateChecks.KernelSporSch.HNT0

end
