module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesPackage
public import Certificates.Kernel.SuzNine.Clos
public import Certificates.Kernel.SuzNine.Elt
public import Certificates.Kernel.SuzNine.Orb
public import CFSG.Certificates.Kernel.SuzNine.PermKey
public import CFSG.Sporadic.SuzOddCore.SmallAut
import CFSG.Certificates.Kernel.Misc.PermClosOrbit
import CFSG.Certificates.Kernel.Spor.BaseSep
import Certificates.Kernel.Sporadic.SuzInv.Inner1
import Certificates.Kernel.Sporadic.SuzInv.Full1
import CFSG.Sporadic.SuzOddCore.CTIBase
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoSetupSylow
import Certificates.Data.ExceptionalSL3

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSuzNine

open CFSG.Sporadic.SuzOddCore CFSG.KC.SuzNine CFSG.KC.Misc.Clos CFSG.KS.Raw.Orb CFSG.KC.LQT
open CFSG.Certificates CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
open scoped Pointwise


theorem prep_unique {P : ℕ} {g h : Equiv.Perm (Fin 1782)} (hg : PRep 1782 11 P g)
    (hh : PRep 1782 11 P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem eq_of_prep {P Q : ℕ} {g : Equiv.Perm (Fin 1782)} (hP : P >>> (1782 * 11) = 0)
    (hQ : Q >>> (1782 * 11) = 0) (hp : PRep 1782 11 P g) (hq : PRep 1782 11 Q g) : P = Q :=
  CFSG.KS.PF.eq_of_fields (by norm_num) hP hQ fun i hi => (hp ⟨i, hi⟩).trans (hq ⟨i, hi⟩).symm

theorem pc_shr (p q : ℕ) : pc p q >>> (1782 * 11) = 0 :=
  CFSG.KS.PF.pcomp_shr _ _ (by norm_num) (by norm_num)

theorem idP_shr : idP >>> (1782 * 11) = 0 := CFSG.KS.PF.pidn_shr (by norm_num) (by norm_num)

theorem hw_shr (z : ℤ) (w : List ℤ) : hw (z :: w) >>> (1782 * 11) = 0 := by
  unfold hw
  rw [wordK_cons]
  exact CFSG.KS.PF.pcomp_shr _ _ (by norm_num) (by norm_num)

theorem prep_idP : PRep 1782 11 idP 1 := prep_pidn (by norm_num) (by norm_num)

theorem prep_pc {P Q : ℕ} {g h : Equiv.Perm (Fin 1782)} (hP : PRep 1782 11 P g)
    (hQ : PRep 1782 11 Q h) : PRep 1782 11 (pc P Q) (g * h) :=
  prep_pcomp (by norm_num) hP hQ

theorem ap_fin (c : Equiv.Perm (Fin 1782)) (p : Fin 1782) : ap c p = c p := by
  simp [ap]

theorem fldK_prep_lt {P : ℕ} {g : Equiv.Perm (Fin 1782)} (h : PRep 1782 11 P g) {p : ℕ}
    (hp : p < 1782) : fldK P p = ap g p := by
  rw [fldK_of_prep h ⟨p, hp⟩]
  simp [ap, hp]

theorem prep_HG {k : ℕ} (hk : k < 10) : PRep 1782 11 (HG k) (invInnerGen 1 k) := by
  have h := rep_invInnerGen (i := 1) (j := k) (by norm_num)
    (by rw [CertificateChecks.KernelSpor.SuzInv.gensI1.1]; exact hk)
  rw [CertificateChecks.KernelSpor.SuzInv.gensI1.2 k hk] at h
  exact prep_of_rep h

theorem gen_mem {k : ℕ} (hk : k < 10) : invInnerGen 1 k ∈ invE 1 :=
  invInnerGen_mem (by norm_num) (by rw [CertificateChecks.KernelSpor.SuzInv.gensI1.1]; exact hk)

theorem posProd_mem_invE (wd : List ℤ) (hw : ∀ z ∈ wd, z.toNat - 1 < 10) :
    posProd (invInnerGen 1) wd ∈ invE 1 := by
  unfold posProd
  refine (invE 1).list_prod_mem fun x hx => ?_
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
  exact gen_mem (hw z hz)

theorem invE_le_suzM : invE 1 ≤ suzM := by
  rw [invE_eq_centM (i := 1) (by norm_num), centM]
  exact inf_le_right

theorem invE_le_centz : invE 1 ≤ Subgroup.centralizer ({suzInv 1} : Set (Equiv.Perm (Fin 1782))) := by
  rw [invE_eq_centM (i := 1) (by norm_num), centM]
  exact inf_le_left

noncomputable def fP (k : ℕ) : Equiv.Perm (Fin 1782) :=
  if h : k < (invFullChain 1).originalCount then (invFullChain 1).original.get ⟨k, h⟩ else 1

theorem fullCount : (invFullChain 1).originalCount = 6 := by
  rw [← (invFullChain_arrays (i := 1) (by norm_num)).orig_size]
  exact CertificateChecks.KernelSpor.SuzInv.gensF1.1

theorem prep_fP {k : ℕ} (hk : k < 6) :
    PRep 1782 11 (CertificateChecks.KernelSpor.SuzInvT1.F (1 + k)) (fP k) := by
  have hk' : k < (invFullChain 1).originalCount := by rw [fullCount]; exact hk
  have h := (invFullChain_arrays (i := 1) (by norm_num)).orig ⟨k, hk'⟩
  rw [CertificateChecks.KernelSpor.SuzInv.gensF1.2 k hk] at h
  unfold fP
  rw [dif_pos hk']
  exact prep_of_rep h

theorem invD_le_closure_fP :
    invD 1 ≤ Subgroup.closure {g | ∃ k < 6, fP k = g} := by
  rw [invD, RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
  intro g hg
  obtain ⟨⟨k, hk⟩, rfl⟩ := (schreier_vector_mem_toList_iff_get _ g).1 hg
  refine Subgroup.subset_closure ⟨k, by rw [← fullCount]; exact hk, ?_⟩
  unfold fP
  rw [dif_pos hk]

theorem ext_facts : (∀ t < 6, fldK idKey t = [0, 1, 2, 3, 4, 8].getD t 0) ∧
    (∀ j < 4, ∀ t < 6, fldK idKey (6 * (j + 1) + t) = fldK (UGT j) (fldK idKey t)) ∧
    Nat.shiftRight idKey 330 = 0 := by
  obtain ⟨h1, h2⟩ := P.andB_iff.1 ext_chk
  obtain ⟨h2, h3⟩ := P.andB_iff.1 h2
  refine ⟨fun t ht => Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h1 t ht), fun j hj t ht =>
    Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec (CFSG.KS.allN_spec h2 j hj) t ht),
    Nat.eq_of_beq_eq_true h3⟩

noncomputable def uG (j : ℕ) : Equiv.Perm (Fin 1782) := posProd (invInnerGen 1) (UW.getD j [])

theorem prep_UGT {j : ℕ} (hj : j < 4) : PRep 1782 11 (UGT j) (uG j) := by
  have h := CFSG.KS.allN_spec g_chk j hj
  obtain ⟨h1, h2⟩ := P.andB_iff.1 h
  obtain ⟨h2, h3⟩ := P.andB_iff.1 h2
  rw [Nat.eq_of_beq_eq_true h3]
  exact prep_wordK_pos (fun k hk => prep_HG hk) HG _ h1 h2

theorem uG_mem {j : ℕ} (hj : j < 4) : uG j ∈ invE 1 := by
  interval_cases j <;> exact posProd_mem_invE _ (by decide)

theorem hid : ∀ t < 30, fldK idKey t < 1782 := by
  have h6 : ∀ t < 6, fldK idKey t < 1782 := fun t ht => by
    rw [ext_facts.1 t ht]
    interval_cases t <;> decide
  intro t ht
  by_cases h : t < 6
  · exact h6 t h
  · have e : t = 6 * (t / 6 - 1 + 1) + t % 6 := by omega
    rw [e, ext_facts.2.1 _ (by omega) _ (Nat.mod_lt _ (by norm_num)),
      fldK_of_prep (prep_UGT (j := t / 6 - 1) (by omega)) ⟨_, h6 _ (Nat.mod_lt _ (by norm_num))⟩]
    exact Fin.isLt _

theorem idKey_eq' : idKey = permKey 1 := idKey_eq hid ext_facts.2.2

theorem permKey_inj {a b : Equiv.Perm (Fin 1782)} (ha : a ∈ suzM) (hb : b ∈ suzM)
    (h : permKey a = permKey b) : a = b := by
  have hab : ∀ p : Fin 1782, (p : ℕ) ∈ [0, 1, 2, 3, 4, 8] → a p = b p := by
    intro p hp
    obtain ⟨t, ht, e⟩ := List.getElem_of_mem hp
    have ht6 : t < 6 := by simpa using ht
    have h1 : fldK (permKey a) t = fldK (permKey b) t := by rw [h]
    rw [fldK_permKey a (by omega), fldK_permKey b (by omega), ext_facts.1 t ht6,
      List.getD_eq_getElem _ _ ht, e, ap_fin, ap_fin] at h1
    exact Fin.ext h1
  have hc : b⁻¹ * a ∈ smallChain.originalSubgroup := by
    rw [smallChain_originalSubgroup]
    exact suzM.mul_mem (suzM.inv_mem hb) ha
  have h1 := RawSchreierDatum.eq_one_of_fixes_base smallChain smallChain_valid hc fun i => by
    have hm : smallChain.base.get i ∈ smallChain.base.toList :=
      schreier_vector_get_mem_toList _ _
    rw [smallChain_base_toList] at hm
    have hp : ((smallChain.base.get i : Fin 1782) : ℕ) ∈ [0, 1, 2, 3, 4, 8] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
      rcases hm with h | h | h | h | h | h <;> rw [h] <;> simp
    rw [Equiv.Perm.mul_apply, hab _ hp]
    simp
  exact (inv_mul_eq_one.1 h1).symm

noncomputable def gensM : List ↥suzM :=
  List.ofFn fun j : Fin 4 => ⟨uG j, invE_le_suzM (uG_mem j.isLt)⟩

noncomputable def UM : Subgroup ↥suzM := Subgroup.closure {g | g ∈ gensM}

noncomputable def UP : Subgroup (Equiv.Perm (Fin 1782)) := UM.map suzM.subtype

theorem gensM_getD {j : ℕ} (hj : j < 4) : ((gensM.getD j 1 : ↥suzM) : Equiv.Perm (Fin 1782)) = uG j := by
  rw [List.getD_eq_getElem _ _ (by simpa [gensM] using hj)]
  interval_cases j <;> rfl

theorem gensM_mem {g : ↥suzM} (hg : g ∈ gensM) : ∃ j < 4, (g : Equiv.Perm (Fin 1782)) = uG j := by
  obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hg
  exact ⟨j, j.isLt, rfl⟩

theorem uG_mem_UP {j : ℕ} (hj : j < 4) : uG j ∈ UP :=
  ⟨⟨uG j, invE_le_suzM (uG_mem hj)⟩, Subgroup.subset_closure
    ((List.mem_ofFn' _ _).2 ⟨⟨j, hj⟩, rfl⟩), rfl⟩

theorem UP_le (H : Subgroup (Equiv.Perm (Fin 1782))) (h : ∀ j < 4, uG j ∈ H) : UP ≤ H := by
  rw [UP, Subgroup.map_le_iff_le_comap, UM, Subgroup.closure_le]
  intro g hg
  obtain ⟨j, hj, e⟩ := gensM_mem hg
  change (g : Equiv.Perm (Fin 1782)) ∈ H
  rw [e]
  exact h j hj

theorem UP_le_suzM : UP ≤ suzM := Subgroup.map_subtype_le _

theorem UP_le_invE : UP ≤ invE 1 := UP_le _ fun _ hj => uG_mem hj

theorem U_facts :
    (∀ k < 8192, ∃ g ∈ UM, permKey (g : Equiv.Perm (Fin 1782)) = UE k) ∧
      (∀ g ∈ UM, ∃ k < 8192, permKey (g : Equiv.Perm (Fin 1782)) = UE k) ∧
      Nat.card {y : ↥suzM // ∃ g ∈ UM, g • (1 : ↥suzM) = y} = 8192 := by
  have hinj : Function.Injective fun c : ↥suzM => permKey (c : Equiv.Perm (Fin 1782)) :=
    fun a b h => Subtype.ext (permKey_inj a.2 b.2 h)
  have hlen : gensM.length = 4 := by simp [gensM]
  have hM : ∀ j < gensM.length, ∀ x : ↥suzM,
      (fun c : ↥suzM => permKey (c : Equiv.Perm (Fin 1782))) (gensM.getD j 1 • x) =
        actK ((fun c : ↥suzM => permKey (c : Equiv.Perm (Fin 1782))) x) (UGT j) := by
    intro j hj x
    rw [hlen] at hj
    simp only [smul_eq_mul, Subgroup.coe_mul]
    rw [gensM_getD hj, actK_permKey (prep_UGT hj) hid]
  have h := orbit_card_proved hinj gensM hM (1 : ↥suzM) (N := 8192) (E := UE) (PA := UPA)
    (SG := USG) (CT := UCT) (by norm_num)
    (fun k hk => by
      have := (P.allN_iff _ _).1 u_tree k hk
      change treeAt actK (permKey 1) UGT gensM.length UE UPA k = true
      rw [← idKey_eq', hlen]
      exact this)
    ((P.allN_iff _ _).1 u_sort)
    (fun k hk => by rw [hlen]; exact (P.allN_iff _ _).1 u_closed k hk)
  refine ⟨fun k hk => ?_, fun g hg => ?_, h.2.2⟩
  · obtain ⟨g, hg, e⟩ := h.1 k hk
    exact ⟨g, hg, by simpa using e⟩
  · obtain ⟨k, hk, e⟩ := h.2.1 g hg
    exact ⟨k, hk, by simpa using e⟩

theorem card_UM : Nat.card UM = 8192 := by
  rw [← U_facts.2.2]
  exact Nat.card_congr
    { toFun := fun g => ⟨g, g, g.2, by simp⟩
      invFun := fun y => ⟨y.1, by obtain ⟨g, hg, e⟩ := y.2; rw [← e]; simpa using hg⟩
      left_inv := fun g => rfl
      right_inv := fun y => rfl }

theorem card_UP : Nat.card UP = 8192 := by
  rw [UP, Subgroup.card_map_of_injective suzM.subtype_injective, card_UM]

theorem prep_z : PRep 1782 11 (CertificateChecks.KernelSpor.SuzInvT1.F 0) (suzInv 1) := by
  have h := rep_suzInv (i := 1) (by norm_num)
  rw [invGraph_check.2.2.2.1 1 (by norm_num), invRepArr,
    CertificateChecks.KernelSpor.SuzInv.run_eq1 (by norm_num)] at h
  exact prep_of_rep h

theorem z_mem_suzM : suzInv 1 ∈ suzM :=
  (suzInv_mem_iff_inM (by norm_num)).2 invT_check.2.2.1

theorem UE_zero : UE 0 = permKey 1 := by
  rw [← idKey_eq']
  exact Nat.eq_of_beq_eq_true ((P.allN_iff _ _).1 u_tree 0 (by norm_num))

theorem UE_z : UE 120 = permKey (suzInv 1) := by
  rw [← Nat.eq_of_beq_eq_true z_chk, idKey_eq', actK_permKey prep_z hid, mul_one]

theorem z_mem_UP : suzInv 1 ∈ UP := by
  obtain ⟨g, hg, e⟩ := U_facts.1 120 (by norm_num)
  rw [UE_z] at e
  exact ⟨g, hg, permKey_inj g.2 z_mem_suzM e⟩

theorem testBit_segK (k j i : ℕ) :
    (segK k j).testBit i = (decide (i < 66) && k.testBit (66 * j + i)) := by
  change ((k >>> (66 * j)) &&& (2 ^ 66 - 1)).testBit i = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem segK_eq {a b j j' : ℕ} (h : ∀ t < 6, fldK a (6 * j + t) = fldK b (6 * j' + t)) :
    segK a j = segK b j' := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_segK, testBit_segK]
  by_cases hi : i < 66
  · have hd : i = 11 * (i / 11) + i % 11 := (Nat.div_add_mod i 11).symm
    have hq : i / 11 < 6 := by omega
    have hr : i % 11 < 11 := Nat.mod_lt _ (by norm_num)
    have ha := testBit_fldK a (6 * j + i / 11) (i % 11)
    have hb := testBit_fldK b (6 * j' + i / 11) (i % 11)
    rw [h _ hq] at ha
    rw [ha] at hb
    simp only [hr, decide_true, Bool.true_and] at hb
    rw [show 66 * j + i = 11 * (6 * j + i / 11) + i % 11 by omega,
      show 66 * j' + i = 11 * (6 * j' + i / 11) + i % 11 by omega, hb]
  · simp [hi]

theorem central_eq (x : Equiv.Perm (Fin 1782)) (hx : x ∈ UP)
    (hc : ∀ y ∈ UP, x * y = y * x) : x = 1 ∨ x = suzInv 1 := by
  obtain ⟨m, hm, rfl⟩ := hx
  obtain ⟨k, hk, e⟩ := U_facts.2.1 m hm
  have hcen : centAt UE UCT k = true := by
    refine (P.allN_iff _ _).2 fun j hj' => ?_
    have hj : j < 4 := hj'
    have hcl := (P.allN_iff _ _).1 ((P.allN_iff _ _).1 u_closed k hk) j hj
    rw [P.letB_eq] at hcl
    have he := Nat.eq_of_beq_eq_true (P.andB_iff.1 hcl).2
    refine Nat.beq_eq.mpr ?_
    change segK (UE k) (j + 1) = segK (UE (UCT (Nat.add (Nat.mul k 4) j))) 0
    rw [he, ← e, actK_permKey (prep_UGT hj) hid]
    refine segK_eq fun t ht => ?_
    have hb : fldK idKey t < 1782 := hid t (by omega)
    rw [fldK_permKey _ (by omega), fldK_permKey _ (by omega), Nat.mul_zero, Nat.zero_add,
      ext_facts.2.1 j hj t ht, fldK_prep_lt (prep_UGT hj) hb, ← ap_mul _ _ hb,
      show (m : Equiv.Perm (Fin 1782)) * uG j = uG j * m from hc _ (uG_mem_UP hj)]
  have hk' := P.impB_iff.1 ((P.allN_iff _ _).1 u_cen k hk) hcen
  rcases P.orB_iff.1 hk' with h0 | h0
  · left
    rw [Nat.eq_of_beq_eq_true h0, UE_zero] at e
    exact permKey_inj m.2 (one_mem _) e
  · right
    rw [Nat.eq_of_beq_eq_true h0, UE_z] at e
    exact permKey_inj m.2 z_mem_suzM e

theorem z_central : ∀ y ∈ UP, suzInv 1 * y = y * suzInv 1 := fun y hy =>
  (Subgroup.mem_centralizer_singleton_iff.mp (invE_le_centz (UP_le_invE hy))).symm

theorem hNC : suzT ⊓ Subgroup.normalizer (UP : Set (Equiv.Perm (Fin 1782))) ≤ invD 1 := by
  intro r hr
  have hcent : r ∈ Subgroup.centralizer ({suzInv 1} : Set _) :=
    normalizer_le_centralizer_of_center z_mem_UP (suzInv_ne_one (i := 1) (by norm_num))
      z_central central_eq hr.2
  rw [invD_eq_centT (i := 1) (by norm_num), centT]
  exact ⟨hcent, hr.1⟩

theorem UP_le_invD : UP ≤ invD 1 := UP_le_invE.trans (invE_le_invD (i := 1) (by norm_num))

noncomputable def CSub (c : ℕ) : SubMulAction (Equiv.Perm (Fin 1782)) (Finset (Fin 1782)) where
  carrier := {s | s.card = c}
  smul_mem' g s hs := by
    change (g • s).card = c
    rw [Finset.card_smul_finset]
    exact hs

theorem smul_val {c : ℕ} (g : Equiv.Perm (Fin 1782)) (s : ↥(CSub c)) :
    ((g • s : ↥(CSub c)) : Finset (Fin 1782)) = (s : Finset (Fin 1782)).map g.toEmbedding := by
  change g • (s : Finset (Fin 1782)) = _
  rw [Finset.smul_finset_def, Finset.map_eq_image]
  rfl

noncomputable def encS {c : ℕ} (s : ↥(CSub c)) : ℕ := listKey (ptList (s : Finset (Fin 1782)))

theorem ptList_lt {s : Finset (Fin 1782)} : ∀ x ∈ ptList s, x < 2 ^ 11 := fun x hx => by
  obtain ⟨y, -, rfl⟩ := (mem_ptList s x).1 hx
  exact lt_of_lt_of_le y.2 (by norm_num)

theorem encS_inj (c : ℕ) : Function.Injective (encS (c := c)) := by
  intro a b h
  have hl : ptList (a : Finset (Fin 1782)) = ptList (b : Finset (Fin 1782)) := by
    have hla : (ptList (a : Finset (Fin 1782))).length = c := by rw [ptList_length]; exact a.2
    have hlb : (ptList (b : Finset (Fin 1782))).length = c := by rw [ptList_length]; exact b.2
    refine List.ext_getElem (hla.trans hlb.symm) fun t h1 h2 => ?_
    have := congrArg (fun k => fldK k t) h
    simp only [encS] at this
    rw [fldK_listKey _ ptList_lt, fldK_listKey _ ptList_lt, List.getD_eq_getElem _ _ h1,
      List.getD_eq_getElem _ _ h2] at this
    exact this
  have hmem : ∀ (s : Finset (Fin 1782)) (x : Fin 1782), x ∈ s ↔ (x : ℕ) ∈ ptList s := by
    intro s x
    rw [mem_ptList]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, e⟩
      rwa [← Fin.ext e]
  apply Subtype.ext
  ext x
  rw [hmem, hmem, hl]

theorem encS_smul {c : ℕ} {P : ℕ} {g : Equiv.Perm (Fin 1782)} (hP : PRep 1782 11 P g)
    (s : ↥(CSub c)) : encS (g • s) = setK c (encS s) P := by
  have h := setK_prep hP (s : Finset (Fin 1782))
  have hc : (s : Finset (Fin 1782)).card = c := s.2
  rw [hc] at h
  rw [encS, encS, smul_val, h]

noncomputable def finOf (L : List ℕ) : Finset (Fin 1782) := Finset.univ.filter fun y => (y : ℕ) ∈ L

theorem ptList_finOf {L : List ℕ} (hL : L.Pairwise (· < ·)) (hb : ∀ x ∈ L, x < 1782) :
    ptList (finOf L) = L := by
  have hp : (ptList (finOf L)).Perm L := by
    refine (List.perm_ext_iff_of_nodup (ptList_nodup _) (hL.imp ne_of_lt)).2 fun x => ?_
    rw [mem_ptList]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [finOf] using hy
    · intro hx
      exact ⟨⟨x, hb x hx⟩, by simpa [finOf] using hx, rfl⟩
  exact List.Perm.eq_of_pairwise' ((ptList_pairwise _).imp le_of_lt) (hL.imp le_of_lt) hp

theorem finOf_card {L : List ℕ} (hL : L.Pairwise (· < ·)) (hb : ∀ x ∈ L, x < 1782) :
    (finOf L).card = L.length := by
  rw [← ptList_length, ptList_finOf hL hb]

noncomputable def x0 : ↥(CSub 6) := ⟨finOf X0L, finOf_card (by decide) (by decide)⟩

noncomputable def x3 : ↥(CSub 4) := ⟨finOf X3L, finOf_card (by decide) (by decide)⟩

theorem encS_x0 : encS x0 = listKey X0L := by
  rw [encS, x0]
  exact congrArg listKey (ptList_finOf (by decide) (by decide))

theorem encS_x3 : encS x3 = listKey X3L := by
  rw [encS, x3]
  exact congrArg listKey (ptList_finOf (by decide) (by decide))

theorem smul_eq_of_fixL {c : ℕ} {L : List ℕ} {Q : ℕ}
    {g : Equiv.Perm (Fin 1782)} (hP : PRep 1782 11 Q g) (h : fixL L Q = true)
    {s : ↥(CSub c)} (hs : (s : Finset (Fin 1782)) = finOf L) : g • s = s := by
  apply Subtype.ext
  rw [smul_val, hs]
  refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) (by rw [Finset.card_map])
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
  have hxL : (x : ℕ) ∈ L := by simpa [finOf] using hx
  obtain ⟨q, hq, e⟩ := (P.anyL_iff _ _).1 ((P.allL_iff _ _).1 h _ hxL)
  rw [fldK_of_prep hP x] at e
  have e' := Nat.eq_of_beq_eq_true e
  simp only [Equiv.toEmbedding_apply, finOf, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [e']
  exact hq

theorem U_fix : UP ≤ MulAction.stabilizer (Equiv.Perm (Fin 1782)) x0 ⊓
    MulAction.stabilizer (Equiv.Perm (Fin 1782)) x3 := by
  refine UP_le _ fun j hj => ?_
  have h := CFSG.KS.allN_spec fix_chk j hj
  obtain ⟨h0, h3⟩ := P.andB_iff.1 h
  exact ⟨smul_eq_of_fixL (prep_UGT hj) h0 rfl, smul_eq_of_fixL (prep_UGT hj) h3 rfl⟩

noncomputable def hl : List (Equiv.Perm (Fin 1782)) := List.ofFn fun k : Fin 10 => invInnerGen 1 k

noncomputable def gal : List (Equiv.Perm (Fin 1782)) :=
  List.ofFn fun j : Fin 16 => if (j : ℕ) < 10 then invInnerGen 1 j else fP (j - 10)

theorem hl_closure : Subgroup.closure {g | g ∈ hl} = invE 1 := by
  rw [invE_eq_closure (i := 1) (by norm_num), CertificateChecks.KernelSpor.SuzInv.gensI1.1]
  congr 1
  ext g
  simp only [hl, List.mem_ofFn', Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, k.isLt, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

theorem invD_le_gal : invD 1 ≤ Subgroup.closure {g | g ∈ gal} := by
  refine invD_le_closure_fP.trans ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨k, hk, rfl⟩
  refine Subgroup.subset_closure ((List.mem_ofFn' _ _).2 ⟨⟨k + 10, by omega⟩, ?_⟩)
  simp

theorem prep_hl {j : ℕ} (hj : j < hl.length) : PRep 1782 11 (HG j) (hl.getD j 1) := by
  have hj' : j < 10 := by simpa [hl] using hj
  rw [List.getD_eq_getElem _ _ hj]
  simp only [hl, List.getElem_ofFn]
  exact prep_HG hj'

theorem prep_gal {j : ℕ} (hj : j < gal.length) : PRep 1782 11 (GA j) (gal.getD j 1) := by
  have hj' : j < 16 := by simpa [gal] using hj
  rw [List.getD_eq_getElem _ _ hj]
  simp only [gal, List.getElem_ofFn]
  by_cases h : j < 10
  · rw [if_pos h]
    have e : GA j = HG j := by
      unfold GA HG
      rw [show Nat.blt j 10 = true by rw [Nat.blt_eq]; exact h]
    rw [e]
    exact prep_HG h
  · rw [if_neg h]
    have e : GA j = CertificateChecks.KernelSpor.SuzInvT1.F (1 + (j - 10)) := by
      unfold GA
      rw [show Nat.blt j 10 = false by
        rw [Bool.eq_false_iff]
        intro h'
        rw [Nat.blt_eq] at h'
        exact h h']
      congr 1
      change j - 9 = _
      omega
    rw [e]
    exact prep_fP (by omega)

theorem orbit_facts {c N nG : ℕ} (gens : List (Equiv.Perm (Fin 1782))) (G : ℕ → ℕ)
    (hG : ∀ j < gens.length, PRep 1782 11 (G j) (gens.getD j 1)) (hn : gens.length = nG)
    (x : ↥(CSub c)) {E PA SG CT : ℕ → ℕ} (hN : 0 < N)
    (ht : CFSG.KC.LQT.P.allN N (treeAt (setK c) (encS x) G nG E PA) = true)
    (hs : CFSG.KC.LQT.P.allN N (sortAt N E SG) = true)
    (hc : CFSG.KC.LQT.P.allN N (closedAt (setK c) G nG N E CT) = true) :
    (∀ g ∈ Subgroup.closure {g | g ∈ gens}, ∃ k < N, encS (g • x) = E k) ∧
      Nat.card {y : ↥(CSub c) // ∃ g ∈ Subgroup.closure {g | g ∈ gens}, g • x = y} = N := by
  subst hn
  have h := orbit_card_proved (encS_inj c) gens (M := setK c) (G := G)
    (fun j hj y => encS_smul (hG j hj) y) x hN ((P.allN_iff _ _).1 ht) ((P.allN_iff _ _).1 hs)
    ((P.allN_iff _ _).1 hc)
  exact ⟨h.2.1, h.2.2⟩

theorem card_invE : Nat.card ↥(invE 1) = 3317760 := by
  rw [CFSG.Sporadic.SuzOddCore.card_invE (i := 1) (by norm_num), invInnerOrders]
  norm_num

theorem card_stab {c : ℕ} (x : ↥(CSub c)) {N : ℕ}
    (h : Nat.card {y : ↥(CSub c) // ∃ g ∈ Subgroup.closure {g | g ∈ hl}, g • x = y} = N) :
    Nat.card (MulAction.stabilizer ↥(invE 1) x) * N = 3317760 := by
  have h1 := (MulAction.stabilizer ↥(invE 1) x).card_mul_index
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, card_invE] at h1
  rw [← h1, ← h]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
  rw [MulAction.mem_orbit_iff, hl_closure]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, g.2, rfl⟩

theorem card_stab_x0 : Nat.card (MulAction.stabilizer ↥(invE 1) x0) = 73728 := by
  have h := card_stab x0 (orbit_facts hl HG (fun j hj => prep_hl hj) (by simp [hl]) x0
    (N := 45) (by norm_num) (by rw [encS_x0]; exact x0_tree) x0_sort x0_cm).2
  omega

theorem card_stab_x3 : Nat.card (MulAction.stabilizer ↥(invE 1) x3) = 24576 := by
  have h := card_stab x3 (orbit_facts hl HG (fun j hj => prep_hl hj) (by simp [hl]) x3
    (N := 135) (by norm_num) (by rw [encS_x3]; exact x3_tree) x3_sort x3_cm).2
  omega

theorem uniq {c N : ℕ} (x : ↥(CSub c)) {E PA SG CT : ℕ → ℕ} (hN : 0 < N)
    (ht : CFSG.KC.LQT.P.allN N (treeAt (setK c) (encS x) GA 16 E PA) = true)
    (hs : CFSG.KC.LQT.P.allN N (sortAt N E SG) = true)
    (hc : CFSG.KC.LQT.P.allN N (closedAt (setK c) GA 16 N E CT) = true)
    (hm : CFSG.KC.LQT.P.allN N (movedAt c E UGT) = true) (d : Equiv.Perm (Fin 1782))
    (hd : d ∈ invD 1) (hfix : ∀ u ∈ UP, u • (d • x) = d • x) : d • x = x := by
  obtain ⟨k, hk, e⟩ := (orbit_facts gal GA (fun j hj => prep_gal hj) (by simp [gal]) x hN ht hs
    hc).1 d (invD_le_gal hd)
  cases k with
  | zero =>
    have h0 := Nat.eq_of_beq_eq_true ((P.allN_iff _ _).1 ht 0 hN)
    exact encS_inj c (e.trans h0)
  | succ k =>
    have h := P.impB_iff.1 ((P.allN_iff _ _).1 hm (k + 1) hk)
      (by rw [Nat.blt_eq]; exact Nat.succ_pos k)
    refine absurd ((P.allN_iff _ _).2 fun j hj => ?_) (P.notB_iff.1 h)
    rw [← e, ← encS_smul (prep_UGT hj), hfix _ (uG_mem_UP hj)]
    exact Nat.beq_refl _

theorem prep_hw {w : List ℤ} (hpw : posW w = true) :
    PRep 1782 11 (hw w) (posProd (invInnerGen 1) w) := by
  obtain ⟨h1, h2⟩ := P.andB_iff.1 hpw
  exact prep_wordK_pos (fun k hk => prep_HG hk) HG w h1 h2

noncomputable def xE : Equiv.Perm (Fin 1782) := posProd (invInnerGen 1) XW
noncomputable def yE : Equiv.Perm (Fin 1782) := posProd (invInnerGen 1) YW
noncomputable def aE : Equiv.Perm (Fin 1782) := posProd (invInnerGen 1) AW
noncomputable def gE : Equiv.Perm (Fin 1782) := posProd (invInnerGen 1) GW

theorem xyK_facts : posW XW = true ∧ posW YW = true ∧
    pc (hw XW) (pc (hw XW) (hw XW)) = idP ∧ pc (hw YW) (pc (hw YW) (hw YW)) = idP ∧
    pc (hw XW) (hw YW) = pc (hw YW) (hw XW) ∧ hw XW ≠ idP ∧ hw YW ≠ idP ∧ hw YW ≠ hw XW ∧
    hw YW ≠ pc (hw XW) (hw XW) ∧ fixL X0L (hw XW) = true ∧ fixL X0L (hw YW) = true := by
  have h := xy_chk
  unfold xyK at h
  simp only [P.letB_eq] at h
  obtain ⟨h1, h⟩ := P.andB_iff.1 h
  obtain ⟨h2, h⟩ := P.andB_iff.1 h
  obtain ⟨h3, h⟩ := P.andB_iff.1 h
  obtain ⟨h4, h⟩ := P.andB_iff.1 h
  obtain ⟨h5, h⟩ := P.andB_iff.1 h
  obtain ⟨h6, h⟩ := P.andB_iff.1 h
  obtain ⟨h7, h⟩ := P.andB_iff.1 h
  obtain ⟨h8, h⟩ := P.andB_iff.1 h
  obtain ⟨h9, h⟩ := P.andB_iff.1 h
  obtain ⟨h10, h11⟩ := P.andB_iff.1 h
  exact ⟨h1, h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5,
    fun e => P.notB_iff.1 h6 (by rw [e]; exact Nat.beq_refl _),
    fun e => P.notB_iff.1 h7 (by rw [e]; exact Nat.beq_refl _),
    fun e => P.notB_iff.1 h8 (by rw [e]; exact Nat.beq_refl _),
    fun e => P.notB_iff.1 h9 (by rw [e]; exact Nat.beq_refl _), h10, h11⟩

theorem agK_facts : posW AW = true ∧ posW GW = true ∧
    pc (hw AW) (pc (hw AW) (hw AW)) = idP ∧ hw AW ≠ idP ∧
    pc (hw GW) (hw AW) = pc (pc (hw AW) (hw AW)) (hw GW) ∧ fixL X0L (hw AW) = true ∧
    fixL X3L (hw AW) = true := by
  have h := ag_chk
  unfold agK at h
  simp only [P.letB_eq] at h
  obtain ⟨h1, h⟩ := P.andB_iff.1 h
  obtain ⟨h2, h⟩ := P.andB_iff.1 h
  obtain ⟨h3, h⟩ := P.andB_iff.1 h
  obtain ⟨h4, h⟩ := P.andB_iff.1 h
  obtain ⟨h5, h⟩ := P.andB_iff.1 h
  obtain ⟨h6, h7⟩ := P.andB_iff.1 h
  exact ⟨h1, h2, Nat.eq_of_beq_eq_true h3,
    fun e => P.notB_iff.1 h4 (by rw [e]; exact Nat.beq_refl _), Nat.eq_of_beq_eq_true h5, h6, h7⟩

theorem prep_xE : PRep 1782 11 (hw XW) xE := prep_hw xyK_facts.1
theorem prep_yE : PRep 1782 11 (hw YW) yE := prep_hw xyK_facts.2.1
theorem prep_aE : PRep 1782 11 (hw AW) aE := prep_hw agK_facts.1
theorem prep_gE : PRep 1782 11 (hw GW) gE := prep_hw agK_facts.2.1

theorem pow_three_of {P : ℕ} {g : Equiv.Perm (Fin 1782)} (hP : PRep 1782 11 P g)
    (h : pc P (pc P P) = idP) : g ^ 3 = 1 := by
  have h1 := prep_pc hP (prep_pc hP hP)
  rw [h] at h1
  rw [pow_three]
  exact (prep_unique h1 prep_idP)

theorem ne_of_prep {P Q : ℕ} {g h : Equiv.Perm (Fin 1782)} (hP : P >>> (1782 * 11) = 0)
    (hQ : Q >>> (1782 * 11) = 0) (hp : PRep 1782 11 P g) (hq : PRep 1782 11 Q h) (hne : P ≠ Q) :
    g ≠ h := fun e => hne (eq_of_prep hP hQ hp (e ▸ hq))

theorem x_pow : xE ^ 3 = 1 := pow_three_of prep_xE xyK_facts.2.2.1
theorem y_pow : yE ^ 3 = 1 := pow_three_of prep_yE xyK_facts.2.2.2.1
theorem a_pow : aE ^ 3 = 1 := pow_three_of prep_aE agK_facts.2.2.1

theorem xy_comm : xE * yE = yE * xE := by
  have h2 := prep_pc prep_yE prep_xE
  rw [← xyK_facts.2.2.2.2.1] at h2
  exact prep_unique (prep_pc prep_xE prep_yE) h2

theorem x_ne : xE ≠ 1 := ne_of_prep (hw_shr _ _) idP_shr prep_xE prep_idP xyK_facts.2.2.2.2.2.1
theorem y_ne : yE ≠ 1 := ne_of_prep (hw_shr _ _) idP_shr prep_yE prep_idP xyK_facts.2.2.2.2.2.2.1
theorem a_ne : aE ≠ 1 := ne_of_prep (hw_shr _ _) idP_shr prep_aE prep_idP agK_facts.2.2.2.1

theorem y_not_mem : yE ∉ Subgroup.zpowers xE := by
  intro hmem
  have hord : orderOf xE = 3 := orderOf_eq_prime x_pow x_ne
  have hfin : IsOfFinOrder xE := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, x_pow⟩
  rw [IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf hfin, hord] at hmem
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨k, hk, hky⟩ := hmem
  interval_cases k
  · exact y_ne (by rw [← hky, pow_zero])
  · exact ne_of_prep (hw_shr _ _) (hw_shr _ _) prep_yE prep_xE xyK_facts.2.2.2.2.2.2.2.1
      (by rw [← hky, pow_one])
  · exact ne_of_prep (hw_shr _ _) (pc_shr _ _) prep_yE (prep_pc prep_xE prep_xE)
      xyK_facts.2.2.2.2.2.2.2.2.1 (by rw [← hky, pow_two])

theorem ga_rel : gE * aE * gE⁻¹ = aE⁻¹ := by
  have h2 := prep_pc (prep_pc prep_aE prep_aE) prep_gE
  rw [← agK_facts.2.2.2.2.1] at h2
  have h : gE * aE = (aE * aE) * gE := prep_unique (prep_pc prep_gE prep_aE) h2
  have hinv : aE⁻¹ = aE * aE := by
    rw [inv_eq_iff_mul_eq_one, ← pow_three, a_pow]
  rw [h, hinv]
  group

theorem x_mem : xE ∈ invE 1 := posProd_mem_invE _ (by decide)
theorem y_mem : yE ∈ invE 1 := posProd_mem_invE _ (by decide)
theorem a_mem : aE ∈ invE 1 := posProd_mem_invE _ (by decide)
theorem g_mem : gE ∈ invE 1 := posProd_mem_invE _ (by decide)

theorem x_fix : xE • x0 = x0 := smul_eq_of_fixL prep_xE xyK_facts.2.2.2.2.2.2.2.2.2.1 rfl
theorem y_fix : yE • x0 = x0 := smul_eq_of_fixL prep_yE xyK_facts.2.2.2.2.2.2.2.2.2.2 rfl
theorem a_fix : aE • x3 = x3 := smul_eq_of_fixL prep_aE agK_facts.2.2.2.2.2.2 rfl

noncomputable abbrev NT : Subgroup ↥suzT := suzM.subgroupOf suzT
noncomputable abbrev iNT : ↥NT ≃* ↥suzM := Subgroup.subgroupOfEquivOfLe suzM_le_suzT
noncomputable abbrev UN : Subgroup ↥NT := (UP.subgroupOf suzT).subgroupOf NT
noncomputable abbrev CN : Subgroup ↥suzT := (invD 1).subgroupOf suzT

theorem CT_inf_suzM : invD 1 ⊓ suzM = invE 1 := by
  rw [invD_eq_centT (i := 1) (by norm_num), invE_eq_centM (i := 1) (by norm_num),
    centT, centM, inf_assoc, inf_eq_right.2 suzM_le_suzT]

theorem twoPart_top_suzM : CFSG.QuasithinUnique.twoPart (⊤ : Subgroup ↥suzM) = 8192 := by
  have hfac : (448345497600 : ℕ).factorization 2 = 13 := by
    rw [show (448345497600 : ℕ) = 2 ^ 13 * 54729675 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [CFSG.QuasithinUnique.twoPart, Subgroup.card_top, suzM_card_chain, hfac]
  norm_num

theorem UN_card : Nat.card UN = 8192 := by
  rw [UN]
  rw [← Subgroup.card_map_of_injective (f := NT.subtype) NT.subtype_injective]
  rw [Subgroup.subgroupOf_map_subtype]
  rw [← Subgroup.card_map_of_injective (f := suzT.subtype) suzT.subtype_injective]
  have hmap : ((UP.subgroupOf suzT) ⊓ NT).map suzT.subtype = UP := by
    rw [inf_eq_left.mpr (by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (UP_le_suzM (Subgroup.mem_subgroupOf.mp hx))),
      Subgroup.map_subgroupOf_eq_of_le (UP_le_suzM.trans suzM_le_suzT)]
  rw [hmap, card_UP]

theorem twoPart_top_NT : CFSG.QuasithinUnique.twoPart (⊤ : Subgroup ↥NT) = 8192 := by
  have htop : Nat.card (⊤ : Subgroup ↥NT) = Nat.card (⊤ : Subgroup ↥suzM) := by
    rw [Subgroup.card_top, Subgroup.card_top]
    exact Nat.card_congr iNT.toEquiv
  rw [CFSG.QuasithinUnique.twoPart, htop, ← CFSG.QuasithinUnique.twoPart, twoPart_top_suzM]

theorem UN_sylow : CFSG.QuasithinUnique.IsSylowTwoOf UN ⊤ :=
  CFSG.QuasithinUnique.isSylowTwoOf_of_card_eq le_top
    (IsPGroup.of_card (p := 2) (n := 13) (by rw [UN_card]; norm_num))
    (by rw [UN_card, twoPart_top_NT])

theorem UN_T : UN.map NT.subtype = UP.subgroupOf suzT := by
  rw [UN, Subgroup.subgroupOf_map_subtype]
  exact inf_eq_left.mpr (by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (UP_le_suzM (Subgroup.mem_subgroupOf.mp hx)))

theorem UN_hNC : (⊤ : Subgroup ↥suzT) ⊓
    Subgroup.normalizer ((UN.map NT.subtype : Subgroup ↥suzT) : Set ↥suzT) ≤ CN := by
  rw [UN_T, ← Subgroup.subgroupOf_normalizer_eq (UP_le_suzM.trans suzM_le_suzT)]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  exact Subgroup.mem_subgroupOf.mpr (hNC ⟨x.2, Subgroup.mem_subgroupOf.mp hx.2⟩)

theorem UN_hUC : UN.map NT.subtype ≤ CN := by
  rw [UN_T]
  intro x hx
  exact Subgroup.mem_subgroupOf.mpr (UP_le_invD (Subgroup.mem_subgroupOf.mp hx))

theorem UN_mem {u : ↥NT} (hu : u ∈ UN) : ((u : ↥suzT) : Equiv.Perm (Fin 1782)) ∈ UP :=
  Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hu)

theorem UN_hAut : ∀ α : MulAut ↥NT, ∃ r ∈ (⊤ : Subgroup ↥suzT),
    ∀ n : ↥NT, ((α n : ↥NT) : ↥suzT) = r * n * r⁻¹ := by
  intro α
  let β : MulAut ↥suzM := (iNT.symm.trans α).trans iNT
  obtain ⟨r, hr⟩ := suzConjT_bijective.surjective β
  refine ⟨r, Subgroup.mem_top _, fun n => ?_⟩
  have h : ((β (iNT n) : ↥suzM) : Equiv.Perm (Fin 1782)) = r * (iNT n : Equiv.Perm (Fin 1782)) *
      (r : Equiv.Perm (Fin 1782))⁻¹ := by
    rw [← hr]
    exact suzConjT_apply r (iNT n)
  apply Subtype.ext
  simpa [β, iNT, Subgroup.subgroupOfEquivOfLe_apply_coe,
    Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe, Subgroup.coe_mk] using h

theorem UN_unique {c : ℕ} (x : ↥(CSub c))
    (hu : ∀ d ∈ invD 1, (∀ u ∈ UP, u • (d • x) = d • x) → d • x = x) :
    ∀ d ∈ (⊤ : Subgroup ↥suzT) ⊓ CN,
      (∀ u ∈ UN, ((u : ↥NT) : ↥suzT) • (d • x) = d • x) → d • x = x := by
  intro d hd hfix
  refine hu d (Subgroup.mem_subgroupOf.mp hd.2) fun u hu' => ?_
  let uNT : ↥NT := iNT.symm ⟨u, UP_le_suzM hu'⟩
  have hcoe : ((uNT : ↥suzT) : Equiv.Perm (Fin 1782)) = u :=
    Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe suzM_le_suzT _
  have huNT : uNT ∈ UN := by
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ?_)
    rw [hcoe]
    exact hu'
  have h := hfix uNT huNT
  rw [← hcoe]
  exact h

theorem UN_fix {c : ℕ} (x : ↥(CSub c)) (hx : UP ≤ MulAction.stabilizer (Equiv.Perm (Fin 1782)) x) :
    ∀ u ∈ UN, ((u : ↥NT) : ↥suzT) • x = x := fun u hu => hx (UN_mem hu)

theorem card_CN {c : ℕ} (x : ↥(CSub c)) :
    Nat.card ((CN ⊓ MulAction.stabilizer ↥suzT x).subgroupOf NT) =
      Nat.card (MulAction.stabilizer ↥(invE 1) x) := by
  rw [← Subgroup.card_map_of_injective (f := NT.subtype) NT.subtype_injective]
  rw [Subgroup.subgroupOf_map_subtype]
  rw [← Subgroup.card_map_of_injective (f := suzT.subtype) suzT.subtype_injective]
  rw [← Subgroup.card_map_of_injective (f := (invE 1).subtype) (invE 1).subtype_injective]
  suffices e : ((CN ⊓ MulAction.stabilizer ↥suzT x) ⊓ NT).map suzT.subtype =
      (MulAction.stabilizer ↥(invE 1) x).map (invE 1).subtype by rw [e]
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyT : (y : Equiv.Perm (Fin 1782)) ∈ invD 1 := Subgroup.mem_subgroupOf.mp hy.1.1
    have hyM : (y : Equiv.Perm (Fin 1782)) ∈ suzM := Subgroup.mem_subgroupOf.mp hy.2
    have hyE : (y : Equiv.Perm (Fin 1782)) ∈ invE 1 := by rw [← CT_inf_suzM]; exact ⟨hyT, hyM⟩
    exact ⟨⟨y, hyE⟩, hy.1.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have hyE : (y : Equiv.Perm (Fin 1782)) ∈ invD 1 ⊓ suzM := by
      rw [CT_inf_suzM]
      exact y.2
    exact ⟨⟨y, suzM_le_suzT hyE.2⟩, ⟨⟨Subgroup.mem_subgroupOf.mpr hyE.1, hy⟩,
      Subgroup.mem_subgroupOf.mpr hyE.2⟩, rfl⟩

theorem toT_mem_NT {g : Equiv.Perm (Fin 1782)} (hg : g ∈ invE 1) :
    (⟨g, suzM_le_suzT (invE_le_suzM hg)⟩ : ↥suzT) ∈ NT :=
  Subgroup.mem_subgroupOf.mpr (invE_le_suzM hg)

theorem toT_mem_CN {g : Equiv.Perm (Fin 1782)} (hg : g ∈ invE 1) :
    (⟨g, suzM_le_suzT (invE_le_suzM hg)⟩ : ↥suzT) ∈ CN :=
  Subgroup.mem_subgroupOf.mpr (invE_le_invD (i := 1) (by norm_num) hg)

theorem toT_pow {g : Equiv.Perm (Fin 1782)} (hg : g ∈ invE 1) (h : g ^ 3 = 1) :
    (⟨g, suzM_le_suzT (invE_le_suzM hg)⟩ : ↥suzT) ^ 3 = 1 :=
  Subtype.ext (by simpa using h)

theorem package744109 : IndexNinePackage ↥(suzM.subgroupOf suzT) ∧
    IndexThreePackage ↥(suzM.subgroupOf suzT) := by
  have hx0 : UP ≤ MulAction.stabilizer (Equiv.Perm (Fin 1782)) x0 := fun u hu => (U_fix hu).1
  have hx3 : UP ≤ MulAction.stabilizer (Equiv.Perm (Fin 1782)) x3 := fun u hu => (U_fix hu).2
  have hu0 := uniq x0 (N := 45) (by norm_num) (by rw [encS_x0]; exact x0_tree_a) x0_sort x0_ca
    x0_moved
  have hu3 := uniq x3 (N := 135) (by norm_num) (by rw [encS_x3]; exact x3_tree_a) x3_sort x3_ca
    x3_moved
  refine ⟨indexNinePackage_of_unique_fixed (R := ↥suzT) (N := NT) (U := UN) (A := ⊤) (C := CN)
    (x₀ := x0) UN_sylow UN_hAut UN_hNC UN_hUC (UN_fix x0 hx0) (UN_unique x0 hu0)
    (by rw [card_CN, card_stab_x0, UN_card]) (toT_mem_NT x_mem) (toT_mem_NT y_mem)
    (toT_mem_CN x_mem) (toT_mem_CN y_mem) x_fix y_fix (toT_pow x_mem x_pow) (toT_pow y_mem y_pow)
    (Subtype.ext xy_comm) (fun h => x_ne (congrArg Subtype.val h)) ?_,
    indexThreePackage_of_unique_fixed (R := ↥suzT) (N := NT) (U := UN) (A := ⊤) (C := CN)
    (x₀ := x3) UN_sylow UN_hAut UN_hNC UN_hUC (UN_fix x3 hx3) (UN_unique x3 hu3)
    (by rw [card_CN, card_stab_x3, UN_card]) (toT_mem_NT a_mem) (toT_mem_NT g_mem)
    (toT_mem_CN a_mem) a_fix (toT_pow a_mem a_pow) (fun h => a_ne (congrArg Subtype.val h))
    (Subtype.ext (by simpa using ga_rel))⟩
  intro hy
  apply y_not_mem
  rw [Subgroup.mem_zpowers_iff] at hy ⊢
  obtain ⟨k, hk⟩ := hy
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

end CertificateChecks.KernelSuzNine

end
