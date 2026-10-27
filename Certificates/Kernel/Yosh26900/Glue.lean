
module

public import Certificates.Data.Yosh26900Spec
public import Certificates.Kernel.Yosh26900.Checks
public import CFSG.Certificates.Kernel.Yosh26900Sound
public import CFSG.Certificates.Kernel.Yosh26900Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshExt
public import CFSG.Monster.B.Mathieu.Order
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Yosh26900

open Finset CFSG.KC.Ord CFSG.KC.LQT CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Yosh26900
open CFSG.Sporadic.SmallOddCore CFSG.GH74.M12 CFSG.EvenSporadicStandard.M12Std
open CFSG.EvenSporadicStandard.M12Std.Yosh.Spec

@[expose] def ev12 (σ : Equiv.Perm (Fin 12)) (i : ℕ) : ℕ := if h : i < 12 then (σ ⟨i, h⟩ : ℕ) else i

theorem code_extHom (σ : Equiv.Perm (Fin 12)) : code (Yosh.extHom σ) = ofFn 14 (ev12 σ) := by
  rw [ofFn_eq]
  refine (code_of_vals _ fun i hi => ?_).symm
  change ev12 σ i = vals (Yosh.extHom σ) ((⟨i, hi⟩ : Fin 14) : ℕ)
  rw [vals_fin]
  unfold ev12
  by_cases h : i < 12
  · rw [dif_pos h, Yosh.extHom_apply_lt σ ⟨i, hi⟩ h]
  · rw [dif_neg h, Yosh.extHom_apply_ge σ ⟨i, hi⟩ h]

theorem code_tauP : code Yosh.tauP = P.swap 14 12 13 :=
  (code_swap (⟨12, by omega⟩ : Fin 14) ⟨13, by omega⟩).symm

theorem tp_tbl14 (σ : Equiv.Perm (Fin 12)) : tp 14 (Yosh.tbl14 σ) = Yosh.extHom σ :=
  CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep (co2Rep_natArr_iff.2 (Yosh.rep_tbl14 σ))

theorem tp_tauT : tp 14 Yosh.tauT = Yosh.tauP :=
  CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep (co2Rep_natArr_iff.2 Yosh.rep_tauT)

theorem g_e : P.swap 14 12 13 = eC := Nat.eq_of_beq_eq_true (by quickRfl)

theorem g_e3 : SC 3 = eC := Nat.eq_of_beq_eq_true (by quickRfl)

theorem g_E : ofFn 14 (ev12 bfE) = SC 4 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem g_N : ofFn 14 (ev12 bfN) = SC 5 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem g_F : ofFn 14 (ev12 bfF) = SC 6 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem g_s : ofFn 14 (ev12 Yosh.sP) = s0C := Nat.eq_of_beq_eq_true (by quickRfl)

theorem g_s7 : SC 7 = s0C := Nat.eq_of_beq_eq_true (by quickRfl)

theorem g_c : pow 14 (SC 6) 4 = cC := Nat.eq_of_beq_eq_true (by quickRfl)

theorem g_u : ofFn 14 (ev12 Yosh.u1P) = u1C := Nat.eq_of_beq_eq_true (by quickRfl)

theorem g_e2 : pow 14 eC 2 = one 14 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem g_c2 : pow 14 cC 2 = one 14 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem g_s3 : pow 14 s0C 3 = one 14 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem g_c1 : cC ≠ one 14 := fun h => (P.notB_iff.1 (by quickRfl : notB (Nat.beq cC (one 14)) = true))
  (by rw [h]; exact Nat.beq_refl _)

theorem g_s1 : s0C ≠ one 14 := fun h => (P.notB_iff.1 (by quickRfl : notB (Nat.beq s0C (one 14)) = true))
  (by rw [h]; exact Nat.beq_refl _)

theorem code_eK : code (eK : Equiv.Perm (Fin 14)) = eC := by
  change code (tp 14 Yosh.tauT) = eC
  rw [tp_tauT, code_tauP, g_e]

theorem code_fK : code (fK : Equiv.Perm (Fin 14)) = SC 6 := by
  change code (tp 14 (Yosh.tbl14 bfF)) = SC 6
  rw [tp_tbl14, code_extHom, g_F]

theorem code_coe_mul (a b : ↥yK) :
    code ((a * b : ↥yK) : Equiv.Perm (Fin 14)) =
      mul 14 (code (a : Equiv.Perm (Fin 14))) (code (b : Equiv.Perm (Fin 14))) := by
  rw [Subgroup.coe_mul, code_mul hn14]

theorem code_coe_pow (a : ↥yK) (k : ℕ) :
    code ((a ^ k : ↥yK) : Equiv.Perm (Fin 14)) = pow 14 (code (a : Equiv.Perm (Fin 14))) k := by
  rw [Subgroup.coe_pow, code_pow hn14]

theorem code_cK : code (cK : Equiv.Perm (Fin 14)) = cC := by
  change code ((fK ^ 4 : ↥yK) : Equiv.Perm (Fin 14)) = cC
  rw [code_coe_pow, code_fK, g_c]

theorem code_sK : code (sK : Equiv.Perm (Fin 14)) = s0C := by
  change code (tp 14 (Yosh.tbl14 Yosh.sP)) = s0C
  rw [tp_tbl14, code_extHom, g_s]

theorem code_u1 : code (tp 14 Yosh.u1T) = u1C := by
  change code (tp 14 (Yosh.tbl14 Yosh.u1P)) = u1C
  rw [tp_tbl14, code_extHom, g_u]

@[expose] noncomputable def ygP : List (Equiv.Perm (Fin 14)) :=
  [Yosh.tauP, Yosh.extHom bfE, Yosh.extHom bfN, Yosh.extHom bfF, Yosh.extHom Yosh.sP]

theorem ygP_mem : ∀ l < 5, ygP.getD l 1 ∈ yK := by
  intro l hl
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4) with rfl | rfl | rfl | rfl | rfl
  · change Yosh.tauP ∈ yK
    rw [← tp_tauT]
    exact tp_mem_yK (by simp [Yosh.yGens])
  · change Yosh.extHom bfE ∈ yK
    rw [← tp_tbl14]
    exact tp_mem_yK (by simp [Yosh.yGens])
  · change Yosh.extHom bfN ∈ yK
    rw [← tp_tbl14]
    exact tp_mem_yK (by simp [Yosh.yGens])
  · change Yosh.extHom bfF ∈ yK
    rw [← tp_tbl14]
    exact tp_mem_yK (by simp [Yosh.yGens])
  · change Yosh.extHom Yosh.sP ∈ yK
    rw [← tp_tbl14]
    exact tp_mem_yK (by simp [Yosh.yGens])

theorem code_ygP : ∀ l < 5, YG l = code (ygP.getD l 1) := by
  intro l hl
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4) with rfl | rfl | rfl | rfl | rfl
  · change SC 3 = code Yosh.tauP
    rw [code_tauP, g_e, g_e3]
  · change SC 4 = code (Yosh.extHom bfE)
    rw [code_extHom, g_E]
  · change SC 5 = code (Yosh.extHom bfN)
    rw [code_extHom, g_N]
  · change SC 6 = code (Yosh.extHom bfF)
    rw [code_extHom, g_F]
  · change SC 7 = code (Yosh.extHom Yosh.sP)
    rw [code_extHom, g_s, g_s7]

@[expose] noncomputable def wordP (m : ℕ) : Equiv.Perm (Fin 14) :=
  Nat.rec (motive := fun _ => Equiv.Perm (Fin 14)) 1 (fun i acc => acc * ygP.getD (GW i) 1) m

theorem wordP_spec : ∀ m, (∀ i < m, GW i < 5) → wordP m ∈ yK ∧ code (wordP m) = wordF YG GW m
  | 0, _ => ⟨Subgroup.one_mem _, code_one.symm⟩
  | m + 1, h => by
    obtain ⟨h1, h2⟩ := wordP_spec m fun i hi => h i (by omega)
    have hl := h m (by omega)
    refine ⟨Subgroup.mul_mem _ h1 (ygP_mem _ hl), ?_⟩
    change code (wordP m * ygP.getD (GW m) 1) = mul 14 (wordF YG GW m) (YG (GW m))
    rw [← code_mul hn14, h2, code_ygP _ hl]

theorem hGW : ∀ i < 4, GW i < 5 := fun i hi =>
  P.blt_iff.1 ((P.allN_iff _ _).1 (P.andB_iff.1 y_gw).2 i hi)

@[expose] noncomputable def gK : ↥yK := ⟨wordP 4, (wordP_spec 4 hGW).1⟩

theorem code_gK : code (gK : Equiv.Perm (Fin 14)) = gC :=
  (wordP_spec 4 hGW).2.trans (Nat.eq_of_beq_eq_true (P.andB_iff.1 y_gw).1)

@[expose] noncomputable def gl : List (Equiv.Perm (Fin 14)) :=
  [Yosh.extHom Yosh.sP, Yosh.tauP, wordP 4, Yosh.tauP, Yosh.extHom bfE, Yosh.extHom bfN,
    Yosh.extHom bfF, Yosh.extHom Yosh.sP]

theorem hG : ∀ j < gl.length, SC j = Clos.pcode (gl.getD j 1) := by
  intro j hj
  change j < 8 at hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SC 0 = code (Yosh.extHom Yosh.sP)
    rw [code_extHom, g_s]
    rfl
  · change SC 1 = code Yosh.tauP
    rw [code_tauP, g_e]
    rfl
  · change SC 2 = code (gK : Equiv.Perm (Fin 14))
    rw [code_gK]
    rfl
  · change SC 3 = code Yosh.tauP
    rw [code_tauP, g_e, g_e3]
  · change SC 4 = code (Yosh.extHom bfE)
    rw [code_extHom, g_E]
  · change SC 5 = code (Yosh.extHom bfN)
    rw [code_extHom, g_N]
  · change SC 6 = code (Yosh.extHom bfF)
    rw [code_extHom, g_F]
  · change SC 7 = code (Yosh.extHom Yosh.sP)
    rw [code_extHom, g_s, g_s7]

theorem closure_gl : Subgroup.closure {g | g ∈ gl} = yK := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [gl, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ygP_mem 4 (by norm_num)
    · exact ygP_mem 0 (by norm_num)
    · exact (wordP_spec 4 hGW).1
    · exact ygP_mem 0 (by norm_num)
    · exact ygP_mem 1 (by norm_num)
    · exact ygP_mem 2 (by norm_num)
    · exact ygP_mem 3 (by norm_num)
    · exact ygP_mem 4 (by norm_num)
  · rw [yK, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ Yosh.yGens := hx
    simp only [Yosh.yGens, Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with rfl | rfl | rfl | rfl | rfl
    · rw [tp_tauT]
      exact Subgroup.subset_closure (by simp [gl])
    · rw [tp_tbl14]
      exact Subgroup.subset_closure (by simp [gl])
    · rw [tp_tbl14]
      exact Subgroup.subset_closure (by simp [gl])
    · rw [tp_tbl14]
      exact Subgroup.subset_closure (by simp [gl])
    · rw [tp_tbl14]
      exact Subgroup.subset_closure (by simp [gl])

@[expose] noncomputable def tl : List (Equiv.Perm (Fin 14)) :=
  [Yosh.tauP, Yosh.extHom bfE, Yosh.extHom bfN, Yosh.extHom bfF]

theorem hGT : ∀ j < tl.length, YG j = Clos.pcode (tl.getD j 1) := by
  intro j hj
  change j < 4 at hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · exact code_ygP 0 (by norm_num)
  · exact code_ygP 1 (by norm_num)
  · exact code_ygP 2 (by norm_num)
  · exact code_ygP 3 (by norm_num)

theorem closure_tl : Subgroup.closure {g | g ∈ tl} = tK := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [tl, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · rw [← tp_tauT]
      exact Subgroup.subset_closure ⟨_, by simp [Yosh.tGens], rfl⟩
    · rw [← tp_tbl14]
      exact Subgroup.subset_closure ⟨_, by simp [Yosh.tGens], rfl⟩
    · rw [← tp_tbl14]
      exact Subgroup.subset_closure ⟨_, by simp [Yosh.tGens], rfl⟩
    · rw [← tp_tbl14]
      exact Subgroup.subset_closure ⟨_, by simp [Yosh.tGens], rfl⟩
  · rw [tK, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ Yosh.tGens := hx
    simp only [Yosh.tGens, Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with rfl | rfl | rfl | rfl
    · rw [tp_tauT]
      exact Subgroup.subset_closure (by simp [tl])
    · rw [tp_tbl14]
      exact Subgroup.subset_closure (by simp [tl])
    · rw [tp_tbl14]
      exact Subgroup.subset_closure (by simp [tl])
    · rw [tp_tbl14]
      exact Subgroup.subset_closure (by simp [tl])

theorem closK : (∀ k < 384, ∃ g ∈ yK, code g = KE k) ∧ Nat.card yK = 384 ∧
    ∀ g ∈ yK, ∃ k < 384, code g = KE k := by
  obtain ⟨h1, -, h3⟩ := Clos.clos_card (Clos.pcode_enc hn14) gl hG (by norm_num)
    ((P.allN_iff _ _).1 y_tree) ((P.allN_iff _ _).1 y_sort)
  obtain ⟨h4, h5⟩ := h3 ((P.allN_iff _ _).1 y_closed)
  rw [closure_gl] at h1 h4 h5
  exact ⟨h1, h4, h5⟩

theorem closT : (∀ j < 128, ∃ g ∈ tK, code g = TE j) ∧ Nat.card tK = 128 ∧
    ∀ g ∈ tK, ∃ j < 128, code g = TE j := by
  obtain ⟨h1, -, h3⟩ := Clos.clos_card (Clos.pcode_enc hn14) tl hGT (by norm_num)
    ((P.allN_iff _ _).1 t_tree) ((P.allN_iff _ _).1 t_sort)
  obtain ⟨h4, h5⟩ := h3 ((P.allN_iff _ _).1 t_closed)
  rw [closure_tl] at h1 h4 h5
  exact ⟨h1, h4, h5⟩

noncomputable def xK (k : ℕ) : ↥yK :=
  if h : k < 384 then ⟨(closK.1 k h).choose, (closK.1 k h).choose_spec.1⟩ else 1

theorem code_xK {k : ℕ} (hk : k < 384) : code (xK k : Equiv.Perm (Fin 14)) = KE k := by
  rw [xK, dif_pos hk]
  exact (closK.1 k hk).choose_spec.2

theorem eq_xK {y : ↥yK} {k : ℕ} (hk : k < 384) (h : code (y : Equiv.Perm (Fin 14)) = KE k) :
    y = xK k :=
  Subtype.ext (code_inj hn14 (by rw [h, code_xK hk]))

theorem exists_xK (y : ↥yK) : ∃ k < 384, y = xK k := by
  obtain ⟨k, hk, he⟩ := closK.2.2 y y.2
  exact ⟨k, hk, eq_xK hk he⟩

theorem hX : ∀ k < 384, KE k = code (xK k : Equiv.Perm (Fin 14)) := fun _ hk => (code_xK hk).symm

theorem encK : Clos.ClosEnc (fun y : ↥yK => code (y : Equiv.Perm (Fin 14))) (mul 14) (one 14) where
  enc_one := by
    change code ((1 : ↥yK) : Equiv.Perm (Fin 14)) = one 14
    rw [Subgroup.coe_one, ← code_one]
  enc_mul a b := code_coe_mul a b
  inj a b h := Subtype.ext (code_inj hn14 h)

theorem ti_parts : ∀ j < 128, TI j < 384 ∧ KE (TI j) = TE j := by
  intro j hj
  have h := (P.allN_iff _ _).1 t_ti j hj
  unfold tiAt at h
  obtain ⟨h1, h2⟩ := P.andB_iff.1 h
  exact ⟨P.blt_iff.1 h1, Nat.eq_of_beq_eq_true h2⟩

noncomputable def tE (j : ℕ) : ↥yK := xK (TI j)

theorem code_tE {j : ℕ} (hj : j < 128) : code (tE j : Equiv.Perm (Fin 14)) = TE j := by
  rw [tE, code_xK (ti_parts j hj).1, (ti_parts j hj).2]

theorem tE_mem {j : ℕ} (hj : j < 128) : (tE j : Equiv.Perm (Fin 14)) ∈ tK := by
  obtain ⟨g, hg, he⟩ := closT.1 j hj
  rwa [code_inj hn14 (he.trans (code_tE hj).symm)] at hg

theorem exists_tE {t : ↥yK} (ht : (t : Equiv.Perm (Fin 14)) ∈ tK) : ∃ j < 128, t = tE j := by
  obtain ⟨j, hj, he⟩ := closT.2.2 _ ht
  exact ⟨j, hj, Subtype.ext (code_inj hn14 (by rw [he, code_tE hj]))⟩

theorem tE_inj {i j : ℕ} (hi : i < 128) (hj : j < 128) (h : tE i = tE j) : i = j :=
  Clos.sort_distinct ((P.allN_iff _ _).1 t_sort) i hi j hj
    (by rw [← code_tE hi, ← code_tE hj, h])

theorem card_tK_sub (Q : ↥yK → Prop) [DecidablePred Q] :
    Nat.card {t : ↥yK // (t : Equiv.Perm (Fin 14)) ∈ tK ∧ Q t} =
      ((range 128).filter fun j => Q (tE j)).card := by
  rw [← Nat.card_eq_finsetCard]
  symm
  refine Nat.card_eq_of_bijective (fun j => ⟨tE j.1,
    tE_mem (mem_range.1 (mem_filter.1 j.2).1), (mem_filter.1 j.2).2⟩) ⟨?_, ?_⟩
  · intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext (tE_inj (mem_range.1 (mem_filter.1 a.2).1) (mem_range.1 (mem_filter.1 b.2).1) h)
  · rintro ⟨t, ht, hq⟩
    obtain ⟨j, hj, rfl⟩ := exists_tE ht
    exact ⟨⟨j, mem_filter.2 ⟨mem_range.2 hj, hq⟩⟩, rfl⟩

theorem misc_parts : (SC 11 < 384 ∧ KE (SC 11) = mul 14 eC u1C) ∧ (SC 12 < 128 ∧ TE (SC 12) = u1C) ∧
    (SC 13 < 384 ∧ mul 14 (KE (SC 13)) s0C = mul 14 (mul 14 s0C s0C) (KE (SC 13))) ∧
    ord8 gC = true ∧ SC 14 < 128 ∧ pow 14 (TE (SC 14)) 4 ≠ one 14 := by
  have h := y_misc
  unfold miscB at h
  simp only [P.andB_iff, P.notB_iff, P.blt_iff, P.beq_iff] at h
  obtain ⟨-, ⟨h11, h11e⟩, ⟨h12, h12e⟩, ⟨h13, h13e⟩, hg, -, h14, h14e⟩ := h
  exact ⟨⟨h11, h11e⟩, ⟨h12, h12e⟩, ⟨h13, h13e⟩, hg, h14, h14e⟩

theorem uK_eq {u : ↥yK} (hu : (u : Equiv.Perm (Fin 14)) = tp 14 Yosh.tauT * tp 14 Yosh.u1T) :
    u = xK (SC 11) := by
  refine eq_xK misc_parts.1.1 ?_
  have he : code (tp 14 Yosh.tauT) = eC := by rw [tp_tauT, code_tauP, g_e]
  rw [hu, ← code_mul hn14, code_u1, misc_parts.1.2, he]

@[expose] noncomputable def wK (l : ℕ) : ↥yK := [sK, eK, gK].getD l 1

theorem hwK : ∀ l < 3, code (wK l : Equiv.Perm (Fin 14)) = SC l := by
  intro l hl
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl
  · exact code_sK
  · exact code_eK
  · exact code_gK

theorem htK : ∀ k < 384, Clos.treeAt (mul 14) (one 14) SC 8 KE KP k = true :=
  (P.allN_iff _ _).1 y_tree

theorem hlK : ∀ k < 384, Nat.shiftRight (KP k) 24 < 3 := fun k hk =>
  P.blt_iff.1 ((P.allN_iff _ _).1 y_lt3 k hk)

theorem hcl : ∀ j < 384, clsAt KE KP CL SV (SC 0) (SC 1) ecC (SC 2) j = true := by
  intro j hj
  rcases (by omega : j < 96 ∨ (96 ≤ j ∧ j < 192) ∨ (192 ≤ j ∧ j < 288) ∨ (288 ≤ j ∧ j < 384)) with
    h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact (Clos.allR_iff _ _ _).1 y_cls0 j (Nat.zero_le _) (by omega)
  · exact (Clos.allR_iff _ _ _).1 y_cls1 j h1 (by omega)
  · exact (Clos.allR_iff _ _ _).1 y_cls2 j h1 (by omega)
  · exact (Clos.allR_iff _ _ _).1 y_cls3 j h1 (by omega)

theorem survivor (ψ : MulAut ↥yK) (hψ : IsYoshAut ψ) :
    ∃ s < 4, ∀ k < 384, PSs s k = code (ψ (xK k) : Equiv.Perm (Fin 14)) := by
  obtain ⟨he, -, hs, hinv⟩ := hψ
  obtain ⟨j, hj, hψg⟩ := exists_xK (ψ (wK 2))
  have h1 : code (ψ (wK 1) : Equiv.Perm (Fin 14)) = ecC := by
    change code (ψ eK : Equiv.Perm (Fin 14)) = ecC
    rw [he, code_coe_mul, code_eK, code_cK]
    rfl
  have hg8 : wK 2 ^ 8 = 1 ∧ wK 2 ^ 4 ≠ 1 := by
    refine (ord8_iff encK (wK 2)).1 ?_
    change ord8 (code (gK : Equiv.Perm (Fin 14))) = true
    rw [code_gK]
    exact misc_parts.2.2.2.1
  obtain ⟨s, hs4, hsv⟩ := cls_sound encK (fun k hk => code_xK hk) hwK htK hlK hcl hg8 ψ hs h1 hinv
    hj hψg
  refine ⟨s, hs4, ?_⟩
  have himg : ∀ l < 3, code (((ψ : ↥yK →* ↥yK) (wK l)) : Equiv.Perm (Fin 14)) =
      imW s0C ecC (KE (SV s)) l := by
    refine imW_lt (fun y : ↥yK => code (y : Equiv.Perm (Fin 14)))
      (fun l => (ψ : ↥yK →* ↥yK) (wK l)) ?_ h1 ?_
    · change code (ψ sK : Equiv.Perm (Fin 14)) = s0C
      rw [hs, code_sK]
    · change code (ψ (wK 2) : Equiv.Perm (Fin 14)) = KE (SV s)
      rw [hψg, hsv, code_xK hj]
  have hv : ∀ k < 384, vAt KP (PSs s) s0C ecC (KE (SV s)) k = true :=
    (P.allN_iff _ _).1 ((P.allN_iff _ _).1 y_vals s hs4)
  exact vals_sound encK (fun k hk => code_xK hk) hwK htK hlK (ψ : ↥yK →* ↥yK) himg hv

theorem bool01 (b : Bool) {p : Prop} [Decidable p] (h : b = true ↔ p) :
    Bool.rec (motive := fun _ => ℕ) 0 1 b = if p then 1 else 0 := by
  cases b
  · rw [if_neg fun hp => absurd (h.2 hp) (by decide)]
  · rw [if_pos (h.1 rfl)]

theorem epsK_eq (x : ℕ) : epsK x = if img x 12 = 13 then 1 else 0 :=
  bool01 _ P.beq_iff

theorem img_code_lt (y : Equiv.Perm (Fin 14)) {i : ℕ} (hi : i < 14) : img (code y) i = yv y i := by
  rw [img_code' hn14 y hi]
  change vals y ((⟨i, hi⟩ : Fin 14) : ℕ) = yv y i
  rw [vals_fin]
  unfold yv
  rw [dif_pos hi]

theorem epsK_code (y : Equiv.Perm (Fin 14)) : epsK (code y) = epsY y := by
  rw [epsK_eq, img_code_lt y (by norm_num)]
  rfl

theorem invs_eq (n x : ℕ) : invs n x = ∑ j ∈ range n, ∑ i ∈ range j,
    Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.blt (img x j) (img x i)) := by
  have h1 : ∀ j, (∑ i ∈ range j, Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.blt (img x j) (img x i))) =
      Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.add acc
        (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.blt (img x j) (img x i)))) j :=
    fun j => (rec_sum _ j).symm
  simp only [h1]
  exact (rec_sum _ n)

theorem lamK_eq (x : ℕ) : lamK x = ∑ j ∈ range 4, ∑ i ∈ range j, if img x j < img x i then 1 else 0 := by
  change invs 4 x = _
  rw [invs_eq]
  exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => bool01 _ P.blt_iff

theorem lamK_code (y : Equiv.Perm (Fin 14)) : lamK (code y) = lamY y := by
  rw [lamK_eq]
  unfold lamY
  refine sum_congr rfl fun j hj => sum_congr rfl fun i hi => ?_
  have hj' := mem_range.1 hj
  have hi' := mem_range.1 hi
  rw [img_code_lt y (by omega), img_code_lt y (by omega)]

theorem central (ψ : MulAut ↥yK) {s : ℕ}
    (hv : ∀ k < 384, PSs s k = code (ψ (xK k) : Equiv.Perm (Fin 14))) (α : ℕ)
    (hc : ∀ k < 384, cenAt KE (PSs s) cC α k = true) (y : ↥yK) :
    ψ y = y * cK ^ (epsY y + α * lamY y) := by
  obtain ⟨k, hk, rfl⟩ := exists_xK y
  have h := cen_sound hX hv (cK : Equiv.Perm (Fin 14)) (by rw [code_cK]; exact hc) k hk
  apply Subtype.ext
  rw [h, Subgroup.coe_mul, Subgroup.coe_pow, epsK_code, lamK_code]

theorem swap_type (ψ : MulAut ↥yK) {s : ℕ}
    (hv : ∀ k < 384, PSs s k = code (ψ (xK k) : Equiv.Perm (Fin 14))) (hb : badB s = true)
    {u : ↥yK} (hu : (u : Equiv.Perm (Fin 14)) = tp 14 Yosh.tauT * tp 14 Yosh.u1T) :
    SwapType ψ u := by
  rw [uK_eq hu]
  have hiu := misc_parts.1.1
  unfold badB at hb
  rw [P.letB_eq, ← code_xK hiu, hv _ hiu] at hb
  have hT : ∀ j < 128, TE j = code (tE j : Equiv.Perm (Fin 14)) := fun j hj => (code_tE hj).symm
  have hZ : ∀ j < 128, PSs s (TI j) = code (ψ (tE j) : Equiv.Perm (Fin 14)) := fun j hj =>
    hv _ (ti_parts j hj).1
  obtain ⟨hn, h4, h2⟩ := bad_sound hT hZ _ _ hb
  have hmul : ∀ a b : ↥yK, ((a : Equiv.Perm (Fin 14)) * b = (b : Equiv.Perm (Fin 14)) * a ↔
      a * b = b * a) := fun a b => by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, Subtype.coe_inj]
  have hmul' : ∀ a b c : ↥yK, ((a : Equiv.Perm (Fin 14)) * b = (c : Equiv.Perm (Fin 14)) * a ↔
      a * b = c * a) := fun a b c => by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, Subtype.coe_inj]
  refine ⟨?_, ?_, ?_⟩
  · rw [card_tK_sub (fun t => t * xK (SC 11) = xK (SC 11) * t),
      card_tK_sub (fun t => t * ψ (xK (SC 11)) = xK (SC 11) * t),
      filter_congr (fun j _ => (hmul (tE j) (xK (SC 11))).symm),
      filter_congr (fun j _ => (hmul' (tE j) (ψ (xK (SC 11))) (xK (SC 11))).symm)]
    exact hn
  · intro t ht hc
    obtain ⟨j, hj, rfl⟩ := exists_tE ht
    exact Subtype.ext (by rw [Subgroup.coe_pow, h4 j hj ((hmul _ _).2 hc), Subgroup.coe_one])
  · intro t ht hc
    obtain ⟨j, hj, rfl⟩ := exists_tE ht
    exact Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_mul, h2 j hj ((hmul' _ _ _).2 hc), Subgroup.coe_one])

theorem preserves_tK (ψ : MulAut ↥yK) {s : ℕ} (hs : s < 4)
    (hv : ∀ k < 384, PSs s k = code (ψ (xK k) : Equiv.Perm (Fin 14))) (y : ↥yK)
    (hy : (y : Equiv.Perm (Fin 14)) ∈ tK) : (ψ y : Equiv.Perm (Fin 14)) ∈ tK := by
  obtain ⟨j, hj, rfl⟩ := exists_tE hy
  have hT : ∀ j < 128, TE j = code (tE j : Equiv.Perm (Fin 14)) := fun j hj => (code_tE hj).symm
  have hY : ∀ j < 128, PSs s (TI j) = code (ψ (tE j) : Equiv.Perm (Fin 14)) := fun j hj =>
    hv _ (ti_parts j hj).1
  obtain ⟨i, hi, he⟩ := pt_sound hT hY ((P.allN_iff _ _).1 ((P.allN_iff _ _).1 y_pt s hs)) j hj
  rw [he]
  exact tE_mem hi

theorem eq_one_of_code {g : ↥yK} (h : code (g : Equiv.Perm (Fin 14)) = one 14) : g = 1 :=
  Subtype.ext (code_inj hn14 (by rw [h, Subgroup.coe_one, ← code_one]))

theorem ne_one_of_code {g : ↥yK} (h : code (g : Equiv.Perm (Fin 14)) ≠ one 14) : g ≠ 1 :=
  fun h1 => h (by rw [h1, Subgroup.coe_one, ← code_one])

theorem spec_facts : Facts where
  card_yK := closK.2.1
  card_tK := closT.2.1
  u1_mem := by
    obtain ⟨h12, h12e⟩ := misc_parts.2.1
    rw [code_inj hn14 (code_u1.trans (h12e.symm.trans (code_tE h12).symm))]
    exact tE_mem h12
  t8 := by
    obtain ⟨h14, h14e⟩ := misc_parts.2.2.2.2
    refine ⟨tE (SC 14), tE_mem h14, fun h => h14e ?_⟩
    rw [← code_tE h14, code_pow hn14, h, ← code_one]
  e_sq := eq_one_of_code (by rw [code_coe_pow, code_eK, g_e2])
  c_sq := eq_one_of_code (by rw [code_coe_pow, code_cK, g_c2])
  c_ne_one := ne_one_of_code (by rw [code_cK]; exact g_c1)
  s_cube := eq_one_of_code (by rw [code_coe_pow, code_sK, g_s3])
  s_ne_one := ne_one_of_code (by rw [code_sK]; exact g_s1)
  e_comm := by
    intro y
    obtain ⟨k, hk, rfl⟩ := exists_xK y
    have h := cn_sound hX (eK : Equiv.Perm (Fin 14)) (cK : Equiv.Perm (Fin 14))
      (by rw [code_eK, code_cK]; exact (P.allN_iff _ _).1 y_cn) k hk
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, h.1])
  c_comm := by
    intro y
    obtain ⟨k, hk, rfl⟩ := exists_xK y
    have h := cn_sound hX (eK : Equiv.Perm (Fin 14)) (cK : Equiv.Perm (Fin 14))
      (by rw [code_eK, code_cK]; exact (P.allN_iff _ _).1 y_cn) k hk
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, h.2])
  cent_s := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := exists_xK z
    have hz' : (xK k : Equiv.Perm (Fin 14)) * sK = sK * xK k := by
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hz]
    obtain ⟨a, -, b, -, r, -, h⟩ := cs_sound hX (sK : Equiv.Perm (Fin 14))
      (eK : Equiv.Perm (Fin 14)) (cK : Equiv.Perm (Fin 14))
      (by rw [code_sK, code_eK, code_cK]; exact (P.allN_iff _ _).1 y_cs) k hk hz'
    exact ⟨a, b, r, Subtype.ext (by
      rw [← h, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow,
        Subgroup.coe_pow])⟩
  inv_s := by
    obtain ⟨h13, h13e⟩ := misc_parts.2.2.1
    refine ⟨xK (SC 13), encK.inj ?_⟩
    change code ((xK (SC 13) * sK : ↥yK) : Equiv.Perm (Fin 14)) =
      code ((sK * sK * xK (SC 13) : ↥yK) : Equiv.Perm (Fin 14))
    rw [code_coe_mul, code_coe_mul, code_coe_mul, code_xK h13, code_sK, h13e]
  syl_s := by
    intro z h3 h1
    obtain ⟨k, hk, rfl⟩ := exists_xK z
    have h3' : (xK k : Equiv.Perm (Fin 14)) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, h3, Subgroup.coe_one]
    have h1' : (xK k : Equiv.Perm (Fin 14)) ≠ 1 := fun h => h1 (Subtype.ext h)
    obtain ⟨hlt, hc⟩ := syl_sound hX (sK : Equiv.Perm (Fin 14))
      (by rw [code_sK]; exact (P.allN_iff _ _).1 y_syl) k hk h3' h1'
    refine ⟨xK (SY k), ?_⟩
    rcases hc with hc | hc
    · left
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hc])
    · right
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, hc])
  classify := by
    intro ψ hψ
    obtain ⟨s, hs, hv⟩ := survivor ψ hψ
    rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3) with rfl | rfl | rfl | rfl
    · left
      intro y
      have h := central ψ hv 0 ((P.allN_iff _ _).1 y_cen0) y
      rwa [zero_mul, add_zero] at h
    · right
      left
      intro y
      have h := central ψ hv 1 ((P.allN_iff _ _).1 y_cen1) y
      rwa [one_mul] at h
    · right
      right
      intro u hu
      exact swap_type ψ hv y_bad2 hu
    · right
      right
      intro u hu
      exact swap_type ψ hv y_bad3 hu
  pt := by
    intro ψ hψ y hy
    obtain ⟨s, hs, hv⟩ := survivor ψ hψ
    exact preserves_tK ψ hs hv y hy

end CFSG.KD.Yosh26900

end
