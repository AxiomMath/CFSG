module

public import Certificates.Kernel.Fi23T.Bridge
public import Certificates.Kernel.Fi23T.Small
public import Certificates.Kernel.Fi23T.Pres
public import Certificates.Kernel.Fi23T.TreeS
public import Certificates.Kernel.Fi23T.Roots

public section

set_option maxRecDepth 400000

open Pointwise

namespace CertificateChecks.KernelFi23T

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23T CFSG.KC.Fi23C CFSG.KD.Fi23K CFSG.KD.Fi23T
  CFSG.KS.PC CFSG.KS.Raw.Orb CertificateChecks.KernelFi23M

@[expose] def xiL : List ℕ := [1, 32, 37, 39, 49, 52, 53, 59, 64, 71]

@[expose] def cgL : List ℕ := [1, 32, 37, 39, 49, 52, 53, 59, 64]

@[expose] def kL : List ℕ := [37, 53, 78, 92, 226]

@[expose] def kvL : List ℕ := [1, 146, 189, 218, 222]

@[expose] def ptSet (L : List ℕ) : Set (Fin 31671) := {x | x.val ∈ L}

theorem hList_succ (Hh : ℕ → ℕ) (r j c : ℕ) :
    hList Hh r j (c + 1) = tb Hh r j :: hList Hh r (j + 1) c := rfl

theorem hList_mem (Hh : ℕ → ℕ) (r : ℕ) : ∀ c j l, l < c → tb Hh r (j + l) ∈ hList Hh r j c
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | c + 1, j, l, h => by
    rw [hList_succ, List.mem_cons]
    cases l with
    | zero => exact Or.inl rfl
    | succ l =>
      have h1 := hList_mem Hh r c (j + 1) l (by omega)
      have e : j + 1 + l = j + (l + 1) := by omega
      rw [e] at h1
      exact Or.inr h1

theorem mem_hList (Hh : ℕ → ℕ) (r : ℕ) :
    ∀ c j v, v ∈ hList Hh r j c → ∃ l < c, tb Hh r (j + l) = v
  | 0, _, _, h => absurd h List.not_mem_nil
  | c + 1, j, v, h => by
    rw [hList_succ, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by omega, rfl⟩
    · obtain ⟨l, hl, e⟩ := mem_hList Hh r c (j + 1) v h
      refine ⟨l + 1, by omega, ?_⟩
      have e' : j + (l + 1) = j + 1 + l := by omega
      rw [e', e]

theorem reg_mem {r c : ℕ} {L : List ℕ} (hL : hList H r 0 c = L) {l : ℕ} (hl : l < c) :
    tb H r l ∈ L := by
  have h := hList_mem H r c 0 l hl
  rwa [Nat.zero_add, hL] at h

theorem mem_reg {r c : ℕ} {L : List ℕ} (hL : hList H r 0 c = L) {v : ℕ} (hv : v ∈ L) :
    ∃ l < c, tb H r l = v := by
  rw [← hL] at hv
  obtain ⟨l, hl, e⟩ := mem_hList H r c 0 v hv
  exact ⟨l, hl, by rwa [Nat.zero_add] at e⟩

theorem xi_eq : hList H 40 0 10 = xiL := xi_lit
theorem cg_eq : hList H 41 0 9 = cgL := cg_lit
theorem k_eq : hList H 42 0 5 = kL := k_lit
theorem kv_eq : hList H 43 0 5 = kvL := kv_lit

theorem mem_ptSet {L : List ℕ} {x : Fin 31671} : x ∈ ptSet L ↔ x.val ∈ L := Iff.rfl

theorem fp_ptSet {L : List ℕ} (hL : ∀ v ∈ L, v < 31671) {v : ℕ} (hv : v ∈ L) : fp v ∈ ptSet L := by
  rw [mem_ptSet, fp_val (hL v hv)]
  exact hv

theorem gens_ok {r c : ℕ} {L : List ℕ} (hL : hList H r 0 c = L) (hlt : ∀ v ∈ L, v < 31671) :
    ∀ l < c, tb H r l < 31671 ∧ fp (tb H r l) ∈ ptSet L := fun l hl =>
  ⟨hlt _ (reg_mem hL hl), fp_ptSet hlt (reg_mem hL hl)⟩

theorem root_eq {r j p : ℕ} (h : Nat.beq (tb H r j) p = true) : tb H r j = p := Nat.eq_of_beq_eq_true h

section


theorem orb_node {b gr ng : ℕ} {dom : ℕ → Bool} {X : Set (Fin 31671)}
    (hX : ∀ l < ng, tb H gr l < 31671 ∧ fp (tb H gr l) ∈ X) {s e : ℕ}
    (hN : ∀ j, s ≤ j → j < e → NodeOK b gr ng dom s j) {x : Fin 31671}
    (hcov : tb H b (tb H (b + 3) x.val) = x.val) (h1 : s ≤ tb H (b + 3) x.val)
    (h2 : tb H (b + 3) x.val < e) : x ∈ Orb tau X (fp (tb H b s)) := by
  have h := forest_orb hX hN _ h1 h2
  rwa [hcov, fp_of] at h

theorem wP_smul : ∀ w : List ℕ, (∀ p ∈ w, p < 31671) → ∀ V : Finset (Fin 31671),
    wP w • V = w.foldr (fun p V => tau (fp p) • V) V
  | [], _, V => by rw [wP_nil, one_smul]; rfl
  | p :: w, hw, V => by
    rw [wP_cons, mul_smul, lP_pt (hw p (by simp)), wP_smul w (fun q hq => hw q (by simp [hq])) V]
    rfl

theorem ltr_of {w : List ℕ} (hw : ∀ p ∈ w, p < 31671) : ∀ p ∈ w, Ltr p := fun p hp => Or.inl (hw p hp)

theorem lP_alpha : lP 31710 = phiX wα := by
  rw [lP, if_neg (by norm_num), if_pos rfl]

theorem lP_beta : lP 31711 = phiX wβ := by
  rw [lP, if_neg (by norm_num), if_neg (by norm_num)]

theorem tt_left {a : Fin 31671} {V W : Finset (Fin 31671)} : tau a • V = W ↔ V = tau a • W := by
  constructor
  · rintro rfl
    exact (tsys.τ_τ a V).symm
  · rintro rfl
    exact tsys.τ_τ a W

theorem mem_tau {a y : Fin 31671} {V : Finset (Fin 31671)} : y ∈ tau a • V ↔ tau a y ∈ V :=
  tsys.mem_τ_smul

theorem pres1 {p : ℕ} (hp : p < 31671) (h : presK G H 0 3240 [p] = true) : tau (fp p) • T0 = T0 := by
  have e := pres_eq (ltr_of (w := [p]) (by simpa using hp)) h
  rwa [wP_smul _ (by simpa using hp)] at e

theorem hS0 : ∀ s ∈ ptSet xiL, tau s • T0 = T0 := by
  intro s hs
  rw [mem_ptSet] at hs
  simp only [xiL, List.mem_cons, List.not_mem_nil, or_false] at hs
  rw [← fp_of s]
  rcases hs with h | h | h | h | h | h | h | h | h | h <;> rw [h]
  · exact pres1 (by norm_num) q_1
  · exact pres1 (by norm_num) q_32
  · exact pres1 (by norm_num) q_37
  · exact pres1 (by norm_num) q_39
  · exact pres1 (by norm_num) q_49
  · exact pres1 (by norm_num) q_52
  · exact pres1 (by norm_num) q_53
  · exact pres1 (by norm_num) q_59
  · exact pres1 (by norm_num) q_64
  · exact pres1 (by norm_num) q_71

theorem h00 : tau (fp 0) • T0 = T0 := pres1 (by norm_num) q_0

theorem xi_lt : ∀ v ∈ xiL, v < 31671 := by decide
theorem cg_lt : ∀ v ∈ cgL, v < 31671 := by decide
theorem k_lt : ∀ v ∈ kL, v < 31671 := by decide
theorem kv_lt : ∀ v ∈ kvL, v < 31671 := by decide

theorem hcov0 : ∀ x ∈ T0, x ∈ Orb tau (ptSet xiL) (fp 0) := by
  intro x hx
  have hN : ∀ j, 0 ≤ j → j < 3240 → NodeOK 8 40 10 (domT H) 0 j := nodes_of a_tree
  have hd : domT H x.val = true := by rw [domT_iff x.isLt, fp_of]; exact hx
  obtain ⟨h1, h2⟩ := covK_spec a_cov x.isLt hd
  have h := orb_node (gens_ok xi_eq xi_lt) hN h2 (Nat.zero_le _) h1
  rwa [root_eq root_8_0] at h

theorem q_test {w : List ℕ} (hw : ∀ p ∈ w, Ltr p) (h : qK G H w = true) : wP w • T0 = T0 := by
  have hg : (wP w)⁻¹ ∈ A0 := inv_mem (wP_mem w hw)
  have hq : ∀ q ∈ qL, fp q ∈ (wP w)⁻¹ • T0 := fun q hq =>
    Finset.mem_inv_smul_finset_iff.2 (q_mem hw h hq)
  have eq : qL = 0 :: xiL := rfl
  have e := tsys.q_eq hS0 h00 hcov0 hg (hq 0 (by rw [eq]; exact List.mem_cons_self))
    (fun s hs => by
      rw [← fp_of s]
      exact hq _ (by rw [eq]; exact List.mem_cons_of_mem _ hs))
  calc wP w • T0 = wP w • ((wP w)⁻¹ • T0) := by rw [e]
    _ = T0 := smul_inv_smul _ _

theorem q_pts {w : List ℕ} (hw : ∀ p ∈ w, p < 31671) (h : qK G H w = true) :
    w.foldr (fun p V => tau (fp p) • V) T0 = T0 := by
  rw [← wP_smul w hw]
  exact q_test (ltr_of hw) h

theorem cnt_pts {w : List ℕ} (hw : ∀ p ∈ w, p < 31671) {c : ℕ} (h : cntK G H w c = true) :
    (w.foldr (fun p V => tau (fp p) • V) T0 ∩ T0).card = c := by
  rw [← wP_smul w hw]
  exact cnt_eq (ltr_of hw) h

theorem notT {y : ℕ} (hy : y < 31671) (h : domTc H y = true) : fp y ∉ T0 := (notMem_T0 hy).1 h

theorem wP_apply : ∀ w : List ℕ, (∀ p ∈ w, p < 31671) → ∀ z : Fin 31671,
    wP w z = w.foldr (fun p V => tau (fp p) V) z
  | [], _, _ => rfl
  | p :: w, hw, z => by
    rw [wP_cons, Equiv.Perm.mul_apply, lP_pt (hw p (by simp)),
      wP_apply w (fun q hq => hw q (by simp [hq])) z]
    rfl

theorem domW_pts {w : List ℕ} (hw : ∀ p ∈ w, p < 31671) {y : ℕ} (hy : y < 31671) :
    domW G H w y = true ↔ w.foldr (fun p V => tau (fp p) V) (fp y) ∉ T0 := by
  rw [domW_iff (ltr_of hw) hy, wP_apply w hw]

theorem notW {w : List ℕ} (hw : ∀ p ∈ w, p < 31671) {y : ℕ} (hy : y < 31671)
    (h : domW G H w y = true) : w.foldr (fun p V => tau (fp p) V) (fp y) ∉ T0 :=
  (domW_pts hw hy).1 h

theorem dom_facts : fp 2 ∉ T0 ∧ fp 5 ∉ T0 := by
  have hh := dom_ok
  simp only [bAnd_eq, Bool.and_eq_true] at hh
  obtain ⟨h1, h2, -⟩ := hh
  exact ⟨notT (by norm_num) h1, notT (by norm_num) h2⟩

theorem x0_card : (tau (fp 2) • T0 ∩ T0).card = 360 := by
  have h := cnt_pts (w := [2]) (by decide) x0_cnt
  simpa using h

theorem v0_card : (tau (fp 2) • tau (fp 5) • T0 ∩ T0).card = 324 := by
  have h := cnt_pts (w := [2, 5]) (by decide) cr_5
  simpa using h

theorem lab3 : fp 6617 ∉ T0 ∧ tau (fp 2) • tau (fp 3) • T0 = tau (fp 6617) • T0 := by
  have hh := cr_3
  simp only [bAnd_eq, Bool.and_eq_true] at hh
  obtain ⟨h1, h2⟩ := hh
  have e := q_pts (w := [3, 2, 6617]) (by decide) h1
  simp only [List.foldr] at e
  refine ⟨notT (by norm_num) h2, ?_⟩
  rw [tt_left, tt_left] at e
  exact e.symm

theorem lab8 : fp 8 ∉ T0 ∧ tau (fp 2) • tau (fp 8) • T0 = tau (fp 8) • T0 := by
  have hh := cr_8
  simp only [bAnd_eq, Bool.and_eq_true] at hh
  obtain ⟨h1, h2⟩ := hh
  have e := q_pts (w := [8, 2, 8]) (by decide) h1
  simp only [List.foldr] at e
  refine ⟨notT (by norm_num) h2, ?_⟩
  rw [tt_left] at e
  exact e

theorem d8 : fp 9702 ∉ T0 ∧ tau (fp 8) • tau (fp 2) • tau (fp 5) • T0 = tau (fp 9702) • T0 := by
  have hh := dr_8
  simp only [bAnd_eq, Bool.and_eq_true] at hh
  obtain ⟨h1, h2⟩ := hh
  have e := q_pts (w := [9702, 8, 2, 5]) (by decide) h1
  simp only [List.foldr] at e
  exact ⟨notT (by norm_num) h2, tt_left.1 e⟩

theorem d3_card : (tau (fp 3) • tau (fp 2) • tau (fp 5) • T0 ∩ T0).card = 324 := by
  have h := cnt_pts (w := [3, 2, 5]) (by decide) dr_3
  simpa using h

theorem d17_card : (tau (fp 17) • tau (fp 2) • tau (fp 5) • T0 ∩ T0).card = 324 := by
  have h := cnt_pts (w := [17, 2, 5]) (by decide) dr_17
  simpa using h

theorem ed0 : fp 2176 ∉ tau (fp 8) • T0 ∧
    tau (fp 0) • tau (fp 2) • tau (fp 5) • T0 = tau (fp 2176) • tau (fp 8) • T0 := by
  have hh := er_0
  simp only [bAnd_eq, Bool.and_eq_true] at hh
  obtain ⟨h1, h2⟩ := hh
  have e := q_pts (w := [5, 2, 0, 2176, 8]) (by decide) h1
  simp only [List.foldr] at e
  have h3 := notW (w := [8]) (by decide) (by norm_num) h2
  simp only [List.foldr] at h3
  refine ⟨fun hm => h3 (mem_tau.1 hm), ?_⟩
  rw [tt_left, tt_left, tt_left] at e
  exact e.symm

theorem ed3 : fp 4776 ∉ tau (fp 5) • T0 ∧
    tau (fp 3) • tau (fp 2) • tau (fp 5) • T0 = tau (fp 4776) • tau (fp 5) • T0 := by
  have hh := er_3
  simp only [bAnd_eq, Bool.and_eq_true] at hh
  obtain ⟨h1, h2⟩ := hh
  have e := q_pts (w := [5, 2, 3, 4776, 5]) (by decide) h1
  simp only [List.foldr] at e
  have h3 := notW (w := [5]) (by decide) (by norm_num) h2
  simp only [List.foldr] at h3
  refine ⟨fun hm => h3 (mem_tau.1 hm), ?_⟩
  rw [tt_left, tt_left, tt_left] at e
  exact e.symm

theorem ed3m : fp 3346 ∉ T0 ∧ tau (fp 5) • tau (fp 2) • tau (fp 5) • T0 = tau (fp 3346) • T0 := by
  have hh := er_3m
  simp only [bAnd_eq, Bool.and_eq_true] at hh
  obtain ⟨h1, h2⟩ := hh
  have e := q_pts (w := [3346, 5, 2, 5]) (by decide) h1
  simp only [List.foldr] at e
  exact ⟨notT (by norm_num) h2, tt_left.1 e⟩

theorem mu_cross_facts : fp 27573 ∉ tau (fp 2) • T0 ∧
    tau (fp 8) • T0 = tau (fp 27573) • tau (fp 2) • T0 := by
  have hh := mu_cross
  simp only [bAnd_eq, Bool.and_eq_true] at hh
  obtain ⟨h1, h2⟩ := hh
  have e := q_pts (w := [2, 27573, 8]) (by decide) h1
  simp only [List.foldr] at e
  have h3 := notW (w := [2]) (by decide) (by norm_num) h2
  simp only [List.foldr] at h3
  refine ⟨fun hm => h3 (mem_tau.1 hm), ?_⟩
  rw [tt_left, tt_left] at e
  exact e

theorem ga : phiX wα • T0 = tau (fp 4600) • T0 := by
  have hh := ga_ok
  simp only [bAnd_eq, Bool.and_eq_true] at hh
  obtain ⟨h1, -⟩ := hh
  have e := q_test (w := [4600, 31710]) (by simp only [Ltr]; decide) h1
  rw [wP_cons, wP_cons, wP_nil, mul_one, lP_pt (by norm_num), lP_alpha, mul_smul] at e
  exact tt_left.1 e

theorem gb : phiX wβ • T0 = tau (fp 7) • tau (fp 1558) • T0 := by
  have hh := gb_ok
  simp only [bAnd_eq, Bool.and_eq_true] at hh
  obtain ⟨h1, -⟩ := hh
  have e := q_test (w := [1558, 7, 31711]) (by simp only [Ltr]; decide) h1
  rw [wP_cons, wP_cons, wP_cons, wP_nil, mul_one, lP_pt (by norm_num), lP_pt (by norm_num),
    lP_beta, mul_smul, mul_smul] at e
  rw [tt_left] at e
  exact tt_left.1 e

end

end CertificateChecks.KernelFi23T

end
