module

public import Certificates.Kernel.Fi23C.Final
public import CFSG.Certificates.Kernel.Fi23Tr.Bits
public import Certificates.Kernel.Fi23T.Inst

public section

set_option maxRecDepth 400000

open Pointwise

namespace CertificateChecks.KernelFi23T

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23T CFSG.KC.Fi23C CFSG.KD.Fi23K CFSG.KD.Fi23T
  CFSG.KS.Fi23Tr CertificateChecks.KernelFi23M
open CFSG.Sporadic.Fi23.Native (trData cData tauAct treeActTab dTable genTables PBits pBit pOf pZero
  pImg)
open CFSG.Sporadic.Th.Native (ap Table)
open CFSG.Sporadic.Th (Rep idx_of_lt)
open CertificateChecks.KernelFi23C (cp treeAct_cp rep_alpha rep_beta)

theorem hList_len (Hh : ℕ → ℕ) (r : ℕ) : ∀ c j, (hList Hh r j c).length = c
  | 0, _ => rfl
  | c + 1, j => by rw [hList_succ, List.length_cons, hList_len Hh r c (j + 1)]

theorem hList_getElem' (Hh : ℕ → ℕ) (r : ℕ) : ∀ c j i (h : i < (hList Hh r j c).length),
    (hList Hh r j c)[i] = tb Hh r (j + i)
  | 0, _, _, h => absurd h (by simp [hList])
  | c + 1, j, 0, _ => by simp [hList]
  | c + 1, j, i + 1, h => by
    simp only [hList, List.getElem_cons_succ]
    rw [hList_getElem' Hh r c (j + 1) i]
    congr 1
    omega

theorem hList_get (Hh : ℕ → ℕ) (r c : ℕ) {i : ℕ} (hi : i < c) :
    (hList Hh r 0 c).toArray[i]! = tb Hh r i := by
  rw [getElem!_pos _ i (by rw [List.size_toArray, hList_len]; exact hi), List.getElem_toArray,
    hList_getElem', Nat.zero_add]

theorem hList_size (Hh : ℕ → ℕ) (r c : ℕ) : (hList Hh r 0 c).toArray.size = c := by
  rw [List.size_toArray, hList_len]

theorem mem_hList_arr {Hh : ℕ → ℕ} {r c x : ℕ} :
    x ∈ (hList Hh r 0 c).toArray ↔ ∃ l < c, tb Hh r l = x := by
  rw [List.mem_toArray]
  constructor
  · intro h
    obtain ⟨l, hl, e⟩ := mem_hList Hh r c 0 x h
    exact ⟨l, hl, by rwa [Nat.zero_add] at e⟩
  · rintro ⟨l, hl, rfl⟩
    have h := hList_mem Hh r c 0 l hl
    rwa [Nat.zero_add] at h

theorem hList_ne {Hh : ℕ → ℕ} {r c : ℕ} (hc : 0 < c) : hList Hh r 0 c ≠ [] := by
  intro h
  have e := hList_len Hh r c 0
  rw [h] at e
  simp at e
  omega

theorem o_spec : (∀ i < 1080, tb H 2 i < 31671 ∧ tb H 3 (tb H 2 i) = i) ∧
    (∀ i, i + 1 < 1080 → tb H 2 i < tb H 2 (i + 1)) ∧
    ∀ x < 31671, (tb H 3 x < 1080 ∧ tb H 2 (tb H 3 x) = x) ∨ tb H 3 x = 1080 :=
  listK_spec o_list

theorem cData_eq : cData () = (hList H 2 0 1080).toArray := by
  rw [c_lit]
  refine CertificateChecks.KernelFi23C.natsOf_render _ (hList_ne (by norm_num)) fun n hn => ?_
  obtain ⟨l, hl, rfl⟩ := mem_hList H 2 1080 0 n hn
  rw [Nat.zero_add]
  have := (o_spec.1 l hl).1
  omega

@[expose] noncomputable def O0 : Finset (Fin 31671) := Finset.univ.filter fun x => tb H 3 x.val < 1080

theorem mem_O0 {x : Fin 31671} : x ∈ O0 ↔ tb H 3 x.val < 1080 := by
  rw [O0, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem O0_pt {i : ℕ} (hi : i < 1080) : fp (tb H 2 i) ∈ O0 := by
  obtain ⟨h1, h2⟩ := o_spec.1 i hi
  rw [mem_O0, fp_val h1, h2]
  exact hi

theorem O0_idx {x : Fin 31671} (hx : x ∈ O0) : fp (tb H 2 (tb H 3 x.val)) = x := by
  rw [mem_O0] at hx
  rcases o_spec.2.2 x.val x.isLt with h | h
  · rw [h.2, fp_of]
  · omega

theorem memS_O0 {y : ℕ} (hy : y < 31671) : memS H 2 1080 y = true ↔ fp y ∈ O0 := by
  rw [memS_iff, mem_O0, fp_val hy]

theorem cData_lt : ∀ x ∈ cData (), x < 31671 := by
  intro x hx
  rw [cData_eq, mem_hList_arr] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  exact (o_spec.1 l hl).1

theorem cData_mem {x : ℕ} (hx : x < 31671) : x ∈ cData () ↔ fp x ∈ O0 := by
  rw [cData_eq, mem_hList_arr]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact O0_pt hl
  · intro h
    rw [mem_O0, fp_val hx] at h
    rcases o_spec.2.2 x hx with e | e
    · exact ⟨_, h, e.2⟩
    · omega

@[expose] noncomputable def toF (B : PBits) : Finset (Fin 31671) :=
  Finset.univ.filter fun x => pBit B x.val = true

theorem mem_toF {B : PBits} {x : Fin 31671} : x ∈ toF B ↔ pBit B x.val = true := by
  rw [toF, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem toF_inj {A B : PBits} (hA : Canon A) (hB : Canon B) (h : toF A = toF B) : A = B :=
  canon_ext hA hB fun x hx => by
    have e : (⟨x, hx⟩ : Fin 31671) ∈ toF A ↔ (⟨x, hx⟩ : Fin 31671) ∈ toF B := by rw [h]
    rw [mem_toF, mem_toF] at e
    exact Bool.eq_iff_iff.2 e

theorem pBit_pOf0 {xs : Array ℕ} (hxs : ∀ x ∈ xs, x < 31671) (y : ℕ) :
    pBit (pOf (pZero ()) xs) y = xs.contains y := by
  rw [pBit_pOf size_pZero (fun x hx => by have := hxs x hx; omega), pBit_pZero, Bool.false_or]

theorem canon_pOf0 {xs : Array ℕ} (hxs : ∀ x ∈ xs, x < 31671) : Canon (pOf (pZero ()) xs) := by
  refine ⟨by rw [size_pOf, size_pZero], ?_⟩
  rw [pBit_pOf0 hxs, Bool.eq_false_iff]
  intro h
  rw [Array.contains_iff_mem] at h
  exact absurd (hxs _ h) (lt_irrefl _)

theorem cB_iff {y : ℕ} (hy : y < 31671) :
    pBit (pOf (pZero ()) (cData ())) y = true ↔ fp y ∈ O0 := by
  rw [pBit_pOf0 cData_lt, Array.contains_iff_mem, cData_mem hy]

theorem ap_tab_out (r : ℕ) : ap (tabOf r) 31671 = 0 := by
  unfold ap
  rw [getElem!_neg _ _ (by rw [tabOf_size]; omega)]
  rfl

theorem toF_pImg {T : Table} {g : Equiv.Perm (Fin 31671)} (hT : Rep 31671 T g)
    (hT1 : ap T 31671 < 31671) {B : PBits} (hB : Canon B) :
    Canon (pImg (pZero ()) T B) ∧ toF (pImg (pZero ()) T B) = g • toF B := by
  have hlt : ∀ x < 31672, ap T x < 31671 := fun x hx => by
    rcases Nat.lt_or_ge x 31671 with h | h
    · rw [hT x h, idx_of_lt _ h]
      exact Fin.isLt _
    · have e : x = 31671 := by omega
      rw [e]
      exact hT1
  refine ⟨canon_pImg hlt B, ?_⟩
  ext y
  rw [mem_toF, pBit_pImg size_pZero (fun x hx => by have := hlt x hx; omega), pBit_pZero,
    Finset.mem_smul_finset]
  constructor
  · rintro (h | ⟨x, hx, hb, e⟩)
    · exact absurd h Bool.false_ne_true
    · have hx' := pBit_lt hB hb
      refine ⟨⟨x, hx'⟩, mem_toF.2 hb, Fin.ext ?_⟩
      rw [← e, hT x hx', idx_of_lt _ hx']
  · rintro ⟨x, hx, e⟩
    refine Or.inr ⟨x.val, by omega, mem_toF.1 hx, ?_⟩
    rw [hT x.val x.isLt, idx_of_lt _ x.isLt]
    exact congrArg Fin.val e

theorem acts_fin {p : Equiv.Perm (Fin 31671)} {f : ℕ → ℕ} (hp : ActsAs p f) (x : Fin 31671) :
    (p x).val = f x.val := hp x.val x.isLt

section


theorem alpha_sq : phiX wα * phiX wα = 1 := by
  ext x
  rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, acts_fin phiX_wα, acts_fin phiX_wα]
  exact (ord_pt x.isLt).1

theorem beta_cube : phiX wβ ^ 3 = 1 := by
  ext x
  rw [pow_succ, pow_two, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    acts_fin phiX_wβ, acts_fin phiX_wβ, acts_fin phiX_wβ]
  exact (ord_pt x.isLt).2

theorem alpha_out : ap orbLit.alpha 31671 < 31671 := by
  change ap (tabOf 39) 31671 < 31671
  rw [ap_tab_out]
  norm_num

theorem beta_out : ap orbLit.beta 31671 < 31671 := by
  change ap (tabOf 40) 31671 < 31671
  rw [ap_tab_out]
  norm_num


theorem trData_eq : trData () = (hList H 0 0 3240).toArray := by
  rw [tr_lit]
  refine CertificateChecks.KernelFi23C.natsOf_render _ (hList_ne (by norm_num)) fun n hn => ?_
  obtain ⟨l, hl, rfl⟩ := mem_hList H 0 3240 0 n hn
  rw [Nat.zero_add]
  have := (t_spec.1 l hl).1
  omega

theorem trData_lt : ∀ x ∈ trData (), x < 31671 := by
  intro x hx
  rw [trData_eq, mem_hList_arr] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  exact (t_spec.1 l hl).1

theorem trData_mem {x : ℕ} (hx : x < 31671) : x ∈ trData () ↔ fp x ∈ T0 := by
  rw [trData_eq, mem_hList_arr]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact T0_pt hl
  · intro h
    rw [mem_T0, fp_val hx] at h
    rcases t_spec.2 x hx with e | e
    · exact ⟨_, h, e.2⟩
    · omega

theorem tB_iff {y : ℕ} (hy : y < 31671) :
    pBit (pOf (pZero ()) (trData ())) y = true ↔ fp y ∈ T0 := by
  rw [pBit_pOf0 trData_lt, Array.contains_iff_mem, trData_mem hy]

theorem toF_tB : toF (pOf (pZero ()) (trData ())) = T0 := by
  ext x
  rw [mem_toF, tB_iff x.isLt, fp_of]

theorem canon_tB : Canon (pOf (pZero ()) (trData ())) := canon_pOf0 trData_lt

theorem presO {w : List ℕ} (hw : ∀ p ∈ w, Ltr p) (h : presK G H 2 1080 w = true) :
    wP w • O0 = O0 := by
  refine smul_eq_of_maps fun x hx => ?_
  have h1 := presK_spec h (tb H 3 x.val) (mem_O0.1 hx)
  rw [← O0_idx hx, ← fp_wJ hw (o_spec.1 _ (mem_O0.1 hx)).1, mem_O0,
    fp_val (wJ_lt hw (o_spec.1 _ (mem_O0.1 hx)).1)]
  exact h1

theorem tauAct_eq {k m : ℕ} (hk : k < 31671) (hm : m < 31671) :
    tauAct orbLit (dTable orbLit) (genTables orbLit (-2)) k m = (tau (fp k) (fp m)).val := by
  unfold tauAct
  rw [treeAct_cp k hk m hm, tau, fp_val hk, fp_eq hm]

theorem rep_tab {k : ℕ} (hk : k < 31671) :
    Rep 31671 (treeActTab orbLit (dTable orbLit) (genTables orbLit (-2)) k) (tau (fp k)) := by
  rw [tau, fp_val hk]
  exact CertificateChecks.KernelFi23C.rep_actTab hk

theorem ap_tab {k x : ℕ} (hk : k < 31671) (hx : x < 31671) :
    ap (treeActTab orbLit (dTable orbLit) (genTables orbLit (-2)) k) x = (tau (fp k) (fp x)).val := by
  rw [rep_tab hk x hx, idx_of_lt _ hx, fp_eq hx]
  rfl

end

end CertificateChecks.KernelFi23T

end
