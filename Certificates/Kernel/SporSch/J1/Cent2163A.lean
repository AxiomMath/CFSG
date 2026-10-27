module

public import Certificates.Kernel.SporSch.J1.ChainCK
public import Certificates.Kernel.SporSch.J1.Count
public import Certificates.Kernel.SporSch.J1.ClsBfs
public import Certificates.Kernel.SporSch.J1.CentK
public import CFSG.Certificates.Kernel.SporSch.PtCntSound
public import CFSG.Certificates.Kernel.SporSch.J1CentSound
public import CFSG.Sporadic.Schreier.J1CentData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch.MOC CFSG.KS.SporSch.CIdx
open CFSG.KS.SporSch.J1C CFSG.KS.KeyBfs CFSG.KS.Tbl CFSG.KS.SporSch.PtCnt
open CFSG.Sporadic.Schreier CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

noncomputable abbrev ea : Equiv.Perm (Fin 3080) := permOfArr 3080 j1Chain.strongArrs[0]!

noncomputable abbrev eb : Equiv.Perm (Fin 3080) := permOfArr 3080 j1Chain.strongArrs[1]!

noncomputable abbrev GJ : Subgroup (Equiv.Perm (Fin 3080)) := Gen 3080 j1Chain.strongArrs 2

noncomputable abbrev eJ (j : Nat) : Equiv.Perm (Fin 3080) :=
  el 3080 j1Chain.strongArrs j1Chain.baseArr 3 j

theorem n32 : (3080 : Nat) < 2 ^ 32 := by norm_num

theorem ea_mem : ea ∈ GJ := Subgroup.subset_closure ⟨⟨0, by norm_num⟩, rfl⟩

theorem eb_mem : eb ∈ GJ := Subgroup.subset_closure ⟨⟨1, by norm_num⟩, rfl⟩

theorem prepS (j : Nat) (hj : j < 4) :
    PRep 3080 12 (J1L.S j) (permOfArr 3080 j1Chain.strongArrs[j]!) ∧
      PRep 3080 12 (J1L.SI j) (permOfArr 3080 j1Chain.strongArrs[j]!)⁻¹ :=
  prep_PS bindsJL (perms chainCK) hj

theorem rep_listTbl_of_bind {l : List Nat} {P : Nat} (hb : bindListK 3080 12 P l = true)
    {g : Equiv.Perm (Fin 3080)} (hg : PRep 3080 12 P g) :
    CFSG.Sporadic.Th.Rep 3080 (listTbl 3080 l) g := by
  intro x hx
  have ha := CFSG.KS.Raw.toArray_eq_of_bindListK hb
  have hx' : x < l.length := by
    have := congrArg Array.size ha
    simp only [List.size_toArray, unpack, Array.size_ofFn] at this
    omega
  have e : l.getD x 0 = (g ⟨x, hx⟩ : Nat) := by
    have e1 : l[x] = (unpack 3080 12 P)[x]! := by
      rw [← ha, getElem!_pos l.toArray x (by simpa using hx'), List.getElem_toArray]
    rw [List.getD_eq_getElem _ _ hx', e1, unpack_get hx]
    exact hg ⟨x, hx⟩
  rw [CFSG.Sporadic.Th.idx_of_lt _ hx, listTbl, CFSG.Sporadic.Th.ap_ofFn _ hx,
    UInt32.toNat_ofNat', e, Nat.mod_eq_of_lt ((g ⟨x, hx⟩).isLt.trans n32)]
  rfl

theorem rep_A : CFSG.Sporadic.Th.Rep 3080 j1ATbl ea := by
  rw [j1ATbl, lA_eq]
  exact rep_listTbl_of_bind bindA (prepS 0 (by norm_num)).1

theorem rep_B : CFSG.Sporadic.Th.Rep 3080 j1BTbl eb := by
  rw [j1BTbl, lB_eq]
  exact rep_listTbl_of_bind bindB (prepS 1 (by norm_num)).1

theorem rep_AI : CFSG.Sporadic.Th.Rep 3080 j1AInvTbl ea⁻¹ := invT_rep n32 rep_A

theorem rep_BI : CFSG.Sporadic.Th.Rep 3080 j1BInvTbl eb⁻¹ := invT_rep n32 rep_B

theorem ordK_J : ordK J1L.LR 3 = 175560 := by
  have h : Nat.beq (ordK J1L.LR 3) 175560 = true := by quickRfl
  exact Nat.eq_of_beq_eq_true h

theorem card_GJ : Nat.card GJ = 175560 := by
  rw [card_gen chainCK, ordK_J]

theorem rep_toTable' (g : Equiv.Perm (Fin 3080)) : CFSG.Sporadic.Th.Rep 3080 (toTable g) g :=
  rep_toTable n32 g

theorem orderTwo_len : (j1OrderTables 2).length = 1463 := by
  have h1 : Nat.ble (rcnt (J1L.LR 0)) (J1PC.CS.length * 64) = true := by quickRfl
  have h2 : Nat.blt (64 * (rcnt (J1L.LR 1) * rcnt (J1L.LR 2))) 1048576 = true := by quickRfl
  have h3 : Nat.beq (J1PC.CS.map (· % 1048576)).sum 1463 = true := by quickRfl
  rw [orderTables_eq, ptLen_sound chainCK (mx := 2) (by norm_num) (Nat.le_of_ble_eq_true h1)
    J1PC.hc (by rw [Nat.blt_eq] at h2; exact h2)]
  exact Nat.eq_of_beq_eq_true h3

noncomputable abbrev gl (l : Nat) : Equiv.Perm (Fin 3080) := if l = 0 then ea else eb

theorem gl_mem (l : Nat) : gl l ∈ GJ := by
  unfold gl
  split
  · exact ea_mem
  · exact eb_mem

theorem gl_eq {l : Nat} (hl : l < 2) : gl l = permOfArr 3080 j1Chain.strongArrs[l]! := by
  unfold gl
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · rw [ite_eq_left rfl]
  · rw [ite_eq_right (by norm_num)]

theorem prep_gl {l : Nat} (hl : l < 2) :
    PRep 3080 12 (J1L.S l) (gl l) ∧ PRep 3080 12 (J1L.SI l) (gl l)⁻¹ := by
  rw [gl_eq hl]
  exact prepS l (by omega)

theorem bfsB : BfsFacts 3080 j1Chain.strongArrs j1Chain.baseArr 3 (ordK J1L.LR 3)
      (fun l g => gl l * g * (gl l)⁻¹) 2 J1PB.c J1PB.J J1PB.PA J1PB.LB J1PB.POS ∧
    J1PB.c ≤ 2000 ∧ J1PB.J 0 = J1PB.jR := by
  have hc : J1PB.c ≤ 23 * 64 := by
    have h : Nat.ble J1PB.c (23 * 64) = true := by quickRfl
    exact Nat.le_of_ble_eq_true h
  refine bfs_facts chainCK (N := ordK J1L.LR 3) (c := J1PB.c) (cap := 2000) (jR := J1PB.jR)
    (ng := 2) (stp := stpC 12 (mask 12) J1L.S J1L.SI) (σ := fun l g => gl l * g * (gl l)⁻¹)
    (J := J1PB.J) (PA := J1PB.PA) (LB := J1PB.LB) (POS := J1PB.POS) (SRT := J1PB.SRT)
    (SRI := J1PB.SRI) rfl ?_ J1PB.hd ?_
  · intro l hl f g hf hg
    obtain ⟨h1, h2⟩ := prep_gl hl
    refine ⟨fun y => ?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ (gl_mem l) hg)
      (Subgroup.inv_mem _ (gl_mem l))⟩
    unfold stpC
    rw [h2 y, hf, h1, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  · have hb := elems_of_blocks hc J1PB.hb
    intro k hk
    have := hb k hk
    unfold bfsPtG at this
    rw [show Nat.blt k J1PB.c = true by rw [Nat.blt_eq]; exact hk] at this
    exact this

theorem eJ_root : eJ J1PB.jR = ea := by
  have hj : J1PB.jR < ordK J1L.LR 3 := by
    rw [← bfsB.2.2]
    exact bfsB.1.lt 0 bfsB.1.c_pos
  exact (eqB_iff_eq chainCK (acts_elJ chainCK _) (fun y => (prepS 0 (by norm_num)).1 y)
    (el_mem chainCK hj) ea_mem).1 J1PB.root

theorem pair0 {α : Type} [Inhabited α] (a b : α) : (#[a, b] : Array α)[0]! = a := by
  rw [getElem!_pos _ 0 (by simp)]
  rfl

theorem pair1 {α : Type} [Inhabited α] (a b : α) : (#[a, b] : Array α)[1]! = b := by
  rw [getElem!_pos _ 1 (by simp)]
  rfl

theorem size_pair {α : Type} (a b : α) : (#[a, b] : Array α).size = 2 := rfl

theorem gens_rep {l : Nat} (hl : l < 2) :
    CFSG.Sporadic.Th.Rep 3080 j1GenTbls[l]! (gl l) ∧
      CFSG.Sporadic.Th.Rep 3080 j1GenInvTbls[l]! (gl l)⁻¹ := by
  unfold j1GenTbls j1GenInvTbls gl
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · rw [pair0, pair0, ite_eq_left rfl]
    exact ⟨rep_A, rep_AI⟩
  · rw [pair1, pair1, ite_eq_right (by norm_num)]
    exact ⟨rep_B, rep_BI⟩

theorem replayB : KReplay 3080 (fun l y => conjT 3080 j1GenTbls[l]! j1GenInvTbls[l]! y) 2 j1ATbl
    J1PB.c (fun k => toTable (eJ (J1PB.J k))) J1PB.PA J1PB.LB
    (fun h l => J1PB.POS (h * 2 + l)) := by
  have R := replay_of_bfs chainCK bfsB.1 rfl
    (st := fun l y => conjT 3080 j1GenTbls[l]! j1GenInvTbls[l]! y) (fun l hl k _ => by
      obtain ⟨h1, h2⟩ := gens_rep hl
      exact conjT_eq_toTable n32 h1 h2 (rep_toTable' _))
  have e : toTable (eJ (J1PB.J 0)) = j1ATbl := by
    rw [bfsB.2.2, eJ_root]
    exact (toTable_ext n32 (by rw [j1ATbl, listTbl, Array.size_ofFn]) rep_A).symm
  rw [e] at R
  exact R

theorem conjClosure_eq' : conjClosure 3080 j1GenTbls j1GenInvTbls j1ATbl 2000 =
    (Array.ofFn (n := J1PB.c) fun i => toTable (eJ (J1PB.J i.val)),
      Array.ofFn (n := J1PB.c) fun i => J1PB.PA i.val,
      Array.ofFn (n := J1PB.c) fun i => J1PB.LB i.val) := by
  have h := keyBfs_replay replayB bfsB.2.1
  rewrite [CFSG.KS.KeyBfs.conjClosure_eq, show j1GenTbls.size = 2 from size_pair j1ATbl j1BTbl]
  beta_reduce at h
  exact h

theorem c_B : J1PB.c = 1463 := rfl

theorem getElem!_ofFn' {α : Type} [Inhabited α] {m : Nat} (f : Fin m → α) {i : Nat} (hi : i < m) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem tblEq_refl (n : Nat) (T : Table) : tblEq n T T = true := by
  unfold tblEq
  rw [CFSG.Sporadic.Th.allIn_eq_true]
  intro i _ _
  exact beq_self_eq_true _

private theorem repsOK_one (n : Nat) (gens gensInv : Array Table) (X : List Table) (r : Table)
    (cap : Nat) :
    repsOK n gens gensInv X [r] cap = true ↔
      (conjTreeOK n gens gensInv r (conjClosure n gens gensInv r cap).1
          (conjClosure n gens gensInv r cap).2.1 (conjClosure n gens gensInv r cap).2.2 = true ∧
        keysDistinct n (conjClosure n gens gensInv r cap).1.toList = true) ∧
      (conjClosure n gens gensInv r cap).1.size = X.length := by
  unfold repsOK
  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, Bool.and_eq_true, beq_iff_eq]

theorem reps_facts : repsOK 3080 j1GenTbls j1GenInvTbls (j1OrderTables 2) [j1ATbl] 2000 = true ∧
    (conjClosure 3080 j1GenTbls j1GenInvTbls j1ATbl 2000).1.size = 1463 := by
  have R := replayB
  refine ⟨?_, by rewrite [conjClosure_eq', Array.size_ofFn]; exact c_B⟩
  rw [repsOK_one]
  rewrite [conjClosure_eq', orderTwo_len]
  simp only [Array.size_ofFn]
  refine ⟨⟨?_, ?_⟩, c_B⟩
  · unfold conjTreeOK
    simp only [Bool.and_eq_true, decide_eq_true_eq, Array.size_ofFn,
      CFSG.Sporadic.Th.allIn_eq_true]
    refine ⟨⟨R.pos_cnt, ?_⟩, fun k hk1 hk => ?_⟩
    · rw [getElem!_ofFn' _ R.pos_cnt]
      change tblEq 3080 (toTable (eJ (J1PB.J 0))) j1ATbl = true
      rw [← R.root_eq]
      exact tblEq_refl _ _
    · obtain ⟨t1, t2, t3⟩ := R.tree k (by omega) hk
      rw [getElem!_ofFn' _ hk, getElem!_ofFn' _ hk, getElem!_ofFn' _ hk,
        getElem!_ofFn' _ (t1.trans hk)]
      refine ⟨⟨t1, by simpa [j1GenTbls] using t2⟩, ?_⟩
      change tblEq 3080 (toTable (eJ (J1PB.J k))) _ = true
      rw [t3]
      exact tblEq_refl _ _
  · apply keysDistinct_of_nodup
    rw [List.nodup_iff_injective_get]
    intro x y e
    simp only [List.get_eq_getElem, List.getElem_map, Array.getElem_toList,
      Array.getElem_ofFn] at e
    have hx : x.val < J1PB.c := by simpa using x.isLt
    have hy : y.val < J1PB.c := by simpa using y.isLt
    exact Fin.ext (R.inj x hx y hy e)

abbrev clsB : Set (Equiv.Perm (Fin 3080)) := {x | ∃ k < J1PB.c, eJ (J1PB.J k) = x}

theorem clsB_mem {k : Nat} (hk : k < J1PB.c) : eJ (J1PB.J k) ∈ GJ :=
  el_mem chainCK (bfsB.1.lt k hk)

theorem clsB_conj : ∀ k < J1PB.c, ∃ g ∈ GJ, g * ea * g⁻¹ = eJ (J1PB.J k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨1, Subgroup.one_mem _, by rw [bfsB.2.2, eJ_root]; group⟩
    · obtain ⟨t1, t2, t3⟩ := bfsB.1.tree k hk0 hk
      obtain ⟨-, c2, -⟩ := bfsB.1.close (J1PB.PA k) (by omega) (J1PB.LB k) t2
      rw [t3] at c2
      obtain ⟨g, hg, e⟩ := ih _ t1 (by omega)
      have c2' : eJ (J1PB.J k) =
          gl (J1PB.LB k) * eJ (J1PB.J (J1PB.PA k)) * (gl (J1PB.LB k))⁻¹ := c2
      refine ⟨gl (J1PB.LB k) * g, Subgroup.mul_mem _ (gl_mem _) hg, ?_⟩
      rw [c2', ← e]
      group

theorem clsB_iff (x : Equiv.Perm (Fin 3080)) : x ∈ clsB ↔ ∃ g ∈ GJ, g * ea * g⁻¹ = x := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact clsB_conj k hk
  · rintro ⟨g, hg, rfl⟩
    have hfin : clsB.Finite := (Set.finite_lt_nat J1PB.c).image _ |>.subset fun x ⟨k, hk, e⟩ =>
      ⟨k, hk, e⟩
    have hcl := conj_closed (kO := 2) (S := j1Chain.strongArrs) hfin (fun j hj x hx => by
      obtain ⟨k, hk, rfl⟩ := hx
      obtain ⟨c1, c2, -⟩ := bfsB.1.close k hk j hj
      have c2' : eJ (J1PB.J (J1PB.POS (k * 2 + j))) = gl j * eJ (J1PB.J k) * (gl j)⁻¹ := c2
      exact ⟨_, c1, by rw [c2', gl_eq hj]⟩) g hg ea ⟨0, bfsB.1.c_pos, by rw [bfsB.2.2, eJ_root]⟩
    exact hcl

theorem clsB_ncard : clsB.ncard = 1463 := by
  have : clsB = (fun k => eJ (J1PB.J k)) '' {k | k < J1PB.c} := by
    ext x
    simp [clsB]
  have hi : Set.InjOn (fun k => eJ (J1PB.J k)) {k | k < J1PB.c} := fun a ha b hb e =>
    bfsB.1.inj a ha b hb (el_inj chainCK (bfsB.1.lt a ha) (bfsB.1.lt b hb) e)
  rw [this, hi.ncard_image, show {k | k < J1PB.c} = ((Finset.range J1PB.c : Finset Nat) : Set Nat)
    by ext; simp, Set.ncard_coe_finset, Finset.card_range, c_B]

theorem card_cent : Nat.card {g : Equiv.Perm (Fin 3080) // g ∈ GJ ∧ g * ea = ea * g} = 120 := by
  have h := card_cent_mul GJ ea_mem clsB_iff
  rw [clsB_ncard, card_GJ] at h
  omega

noncomputable abbrev centL : List (Equiv.Perm (Fin 3080)) :=
  (((products (trLists 3080 j1Chain.strongArrs j1Chain.baseArr 0 3)).map (1 * ·)).filter
    fun h => decide (h * ea = ea * h)).reverse ++ []

theorem cent_forall₂ : List.Forall₂ (CFSG.Sporadic.Th.Rep 3080) j1CentTables centL := by
  unfold j1CentTables
  rw [tables_eq]
  refine filterProducts_spec (P := fun h => h * ea = ea * h) (fun T g hTg => ?_)
    (forall₂_levTables chainCK) (CFSG.Sporadic.Th.Rep.idT n32) List.Forall₂.nil
  unfold commT
  rw [tblEq_iff_eq (CFSG.Sporadic.Th.Rep.compT rep_A hTg) (CFSG.Sporadic.Th.Rep.compT hTg rep_A)]
  exact eq_comm

theorem mem_centL (x : Equiv.Perm (Fin 3080)) : x ∈ centL ↔ x ∈ GJ ∧ x * ea = ea * x := by
  obtain ⟨hm, -⟩ := products_spec chainCK 3 0 (by omega)
  simp only [centL, List.append_nil, List.mem_reverse, List.mem_filter, List.mem_map, one_mul,
    exists_eq_right, decide_eq_true_eq, hm, fix_zero]

theorem centL_len : centL.length = 120 := by
  have := card_filter chainCK (P := fun h => h * ea = ea * h)
  rw [card_cent] at this
  simp only [centL, List.append_nil, List.length_reverse, ← List.countP_eq_length_filter,
    List.countP_map]
  rw [this]
  rfl

theorem centZ :
    (∀ k < J1PZ.cK, J1PZ.K k < 175560 ∧ eJ (J1PZ.K k) * ea = ea * eJ (J1PZ.K k)) ∧
    (∀ k < J1PZ.cK, ∀ k' < J1PZ.cK, J1PZ.K k = J1PZ.K k' → k = k') ∧
    ∀ k < J1PZ.cK, eJ (J1PZ.K k) = 1 ∨ eJ (J1PZ.K k) ^ 15 ≠ 1 ∨
      (∃ h < J1PZ.cK, (eJ (J1PZ.K k) * eJ (J1PZ.K h) * eJ (J1PZ.K k) *
        (eJ (J1PZ.K h))⁻¹) ^ 15 ≠ 1) ∨
      ∃ h < J1PZ.cK, ∃ h2 < J1PZ.cK, (eJ (J1PZ.K k) * eJ (J1PZ.K h) * eJ (J1PZ.K k) *
        (eJ (J1PZ.K h))⁻¹ * eJ (J1PZ.K h2) * eJ (J1PZ.K k) * (eJ (J1PZ.K h2))⁻¹) ^ 15 ≠ 1 :=
  cent_facts chainCK (N := 175560) (mo := 15) (cK := J1PZ.cK) (r := ea)
    (R := elemT 3080 (3080 * 12) J1L.LR J1L.TR 3 J1PZ.jR) (K := J1PZ.K) (W1 := J1PZ.W1)
    (W2 := J1PZ.W2) (W3 := J1PZ.W3) (W4 := J1PZ.W4) ordK_J.symm
    (fun y => by
      have e : eJ J1PZ.jR = ea := eJ_root
      rw [← e]
      exact apL_elemT chainCK _ y) ea_mem (by
      have hc : J1PZ.cK ≤ 2 * 64 := by
        have h : Nat.ble J1PZ.cK (2 * 64) = true := by quickRfl
        exact Nat.le_of_ble_eq_true h
      exact elems_of_blocks hc J1PZ.hb)

theorem centZ_all (x : Equiv.Perm (Fin 3080)) (hx : x ∈ GJ ∧ x * ea = ea * x) :
    ∃ k < J1PZ.cK, eJ (J1PZ.K k) = x := by
  obtain ⟨h1, h2, -⟩ := centZ
  let Kset : Set (Equiv.Perm (Fin 3080)) := (fun k => eJ (J1PZ.K k)) '' {k | k < J1PZ.cK}
  let Cset : Set (Equiv.Perm (Fin 3080)) := {g | g ∈ GJ ∧ g * ea = ea * g}
  have hsub : Kset ⊆ Cset := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨el_mem chainCK (by rw [ordK_J]; exact (h1 k hk).1), (h1 k hk).2⟩
  have hi : Set.InjOn (fun k => eJ (J1PZ.K k)) {k | k < J1PZ.cK} := fun a ha b hb e =>
    h2 a ha b hb (el_inj chainCK (by rw [ordK_J]; exact (h1 a ha).1)
      (by rw [ordK_J]; exact (h1 b hb).1) e)
  have hK : Kset.ncard = 120 := by
    rw [hi.ncard_image, show {k | k < J1PZ.cK} = ((Finset.range J1PZ.cK : Finset Nat) : Set Nat)
      by ext; simp, Set.ncard_coe_finset, Finset.card_range]
    rfl
  have hC : Cset.ncard = 120 := by
    rw [← Nat.card_coe_set_eq]
    exact card_cent
  have := Set.eq_of_subset_of_ncard_le hsub (by rw [hK, hC])
  have hxC : x ∈ Cset := hx
  rw [← this] at hxC
  obtain ⟨k, hk, e⟩ := hxC
  exact ⟨k, hk, e⟩

theorem cent_facts' : j1CentTables.length = 120 ∧ oddWitnessOK 3080 15 j1CentTables = true := by
  have hF := cent_forall₂
  refine ⟨hF.length_eq.trans centL_len, oddWitnessOK_of n32 hF fun x hx => ?_⟩
  obtain ⟨k, hk, rfl⟩ := centZ_all x ((mem_centL x).1 hx)
  obtain ⟨h1, -, h3⟩ := centZ
  have hmem : ∀ h < J1PZ.cK, eJ (J1PZ.K h) ∈ centL := fun h hh =>
    (mem_centL _).2 ⟨el_mem chainCK (by rw [ordK_J]; exact (h1 h hh).1), (h1 h hh).2⟩
  rcases h3 k hk with e | e | ⟨h, hh, e⟩ | ⟨h, hh, h2, hh2, e⟩
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr (Or.inl ⟨_, hmem h hh, e⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨_, hmem h hh, _, hmem h2 hh2, e⟩))

end CertificateChecks.KernelSporSch.J1

end
