
module

public import Certificates.Kernel.LyDce.CoverRoot
public import Certificates.Kernel.LyDce.CoverFr
public import Certificates.Kernel.LyDce.CoverW0
public import Certificates.Kernel.LyDce.CoverW1
public import Certificates.Kernel.LyDce.CoverW2
public import Certificates.Kernel.LyDce.CoverW3
public import Certificates.Kernel.LyDce.Chains
public import Certificates.Kernel.LyBase.Facts
public import CFSG.Certificates.Kernel.LyDce.MaskSound
public import CFSG.Certificates.Kernel.LyDce.CoverSound
public import CFSG.Certificates.Kernel.LyDce.CoverWalkSound
public import CFSG.Certificates.Kernel.LyDce.Lines

public section

namespace CertificateChecks.KernelLyDce

open Equiv MulAction Pointwise CFSG.KC CFSG.KC.Loop CFSG.KC.Benes CFSG.KC.LyDce CFSG.KC.LyBase
  CFSG.KC.LyBenes CFSG.KC.LyGlue CFSG.KC.MonsterConv.Perm CertificateChecks.KernelLy
  CertificateChecks.KernelLyB
  CertificateChecks.KernelLyBase CFSG.Sporadic.Recognition.LyonsSims
  CFSG.Sporadic.Recognition.LyonsSims.LyFinal

noncomputable def wP (w : List Nat) : Perm (Fin Ly0.deg) := Ly0.wG Ly0.gens0 (wZ w)

noncomputable def SG (n : Nat) : Subgroup (Perm (Fin Ly0.deg)) :=
  Subgroup.closure {x | ∃ g ∈ sG.getD n [], x = wP (jwOf g)}

def RS (m : Nat) : Set (Perm (Fin Ly0.deg)) :=
  {x | ∃ p, (nt.getD p (0, 0)).1 = m ∧ x = wP (jwOf (rep.getD p []))}

def O0 : Set (Fin Ly0.deg) := {a | (a : Nat) ∈ o0}

def KeyIs (S : Set (Fin Ly0.deg)) (k : Nat) : Prop := ∃ M, IsMask M S ∧ M % pk = k

noncomputable def Lf (l : Nat) : Set (Fin Ly0.deg) := by
  classical
  exact if h : ∃ g ∈ Ly0.B0, KeyIs (g • O0) (fldW 48 kp l) then h.choose • O0 else ∅

noncomputable def L (i : Fin nL) : Set (Fin Ly0.deg) := Lf i

theorem L_eq (i : Fin nL) : L i = Lf i := by
  unfold L
  rfl

theorem rho_eq (j : Nat) : rho j = Ly0.wG Ly0.gens0 (jZ j) := by
  simpa [wZ] using prod_rho [j]

theorem wP_nil : wP [] = 1 := by simp [wP, wZ]

theorem wP_cons (j : Nat) (w : List Nat) : wP (j :: w) = rho j * wP w := by
  have e : wZ (j :: w) = jZ j ++ wZ w := by simp [wZ]
  simp only [wP, e, Ly0.wG_append, rho_eq]

theorem wP_append (u v : List Nat) : wP (u ++ v) = wP u * wP v := by
  have e : wZ (u ++ v) = wZ u ++ wZ v := by simp [wZ]
  simp only [wP, e, Ly0.wG_append]

theorem wP_mem (w : List Nat) : wP w ∈ Ly0.B0 := wG_wZ_mem w

theorem rho_mem (j : Nat) : rho j ∈ Ly0.B0 := by
  rw [rho_eq]
  exact Ly0.wG_mem Ly0.B0 Ly0.gens0 2 Ly0.gens0_mem _ (jZ_mem j)

theorem rho0_eq : rho 0 = Ly0.cG := by
  rw [rho_eq]
  simp [jZ, Ly0.letterG_pos, Ly0.gens0_zero]

theorem rho1_eq : rho 1 = Ly0.dG := by
  rw [rho_eq]
  simp [jZ, Ly0.letterG_pos, Ly0.gens0_one]

theorem jwOf_nil : jwOf [] = [] := rfl

theorem getD_all {α : Type*} {L : List α} {d : α} {p : α → Bool} (h : L.all p = true)
    (hd : p d = true) (i : Nat) : p (L.getD i d) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases e : L[i]? with
  | none => exact hd
  | some x => exact List.all_eq_true.1 h x (List.mem_of_getElem? e)

theorem lt6_of_all {w : List Nat} (h : ((jwOf w).all fun j => Nat.blt j 6) = true) :
    ∀ j ∈ jwOf w, j < 6 := fun j hj => by
  simpa [Nat.blt_eq] using List.all_eq_true.1 h j hj

theorem sG_lt' (n : Nat) : ∀ g ∈ sG.getD n [], ∀ j ∈ jwOf g, j < 6 := fun g hg =>
  lt6_of_all (List.all_eq_true.1 (getD_all sG_lt rfl n) g hg)

theorem sG_getD_lt (n s : Nat) : ∀ j ∈ jwOf ((sG.getD n []).getD s []), j < 6 :=
  lt6_of_all (getD_all (getD_all sG_lt rfl n) rfl s)

theorem rep_getD_lt (p : Nat) : ∀ j ∈ jwOf (rep.getD p []), j < 6 :=
  lt6_of_all (getD_all rep_lt rfl p)

theorem gen_mem_SG (n s : Nat) : wP (jwOf ((sG.getD n []).getD s [])) ∈ SG n := by
  rw [List.getD_eq_getElem?_getD]
  cases e : (sG.getD n [])[s]? with
  | none => rw [Option.getD_none, jwOf_nil, wP_nil]; exact (SG n).one_mem
  | some g => exact Subgroup.subset_closure ⟨g, List.mem_of_getElem? e, rfl⟩

theorem SG_le (n : Nat) : SG n ≤ Ly0.B0 := by
  rw [SG, Subgroup.closure_le]
  rintro _ ⟨g, -, rfl⟩
  exact wP_mem _

theorem RS_sub (m : Nat) : RS m ⊆ Ly0.B0 := by
  rintro _ ⟨p, -, rfl⟩
  exact wP_mem _

theorem expandG_mem {G : List (List Nat)} {K : Subgroup (Perm (Fin Ly0.deg))}
    (hG : ∀ s, wP (jwOf (G.getD s [])) ∈ K) : ∀ w : List Nat, wP (expandG G w) ∈ K
  | [] => by
    change wP [] ∈ K
    rw [wP_nil]
    exact K.one_mem
  | g :: w => by
    change wP (jwOf (G.getD g []) ++ expandG G w) ∈ K
    rw [wP_append]
    exact K.mul_mem (hG g) (expandG_mem hG w)

section Letters

variable (hc : ∀ a : Fin Ly0.deg, cL a = (Ly0.cG a : Nat))
  (hd : ∀ a : Fin Ly0.deg, dL a = (Ly0.dG a : Nat))
include hc hd

theorem card_SG_ge {n : Nat} (hn : n < 4) : ordS.getD n 0 ≤ Nat.card (SG n) := by
  have h : chainAt n = true := by
    interval_cases n
    exacts [ch0, ch1, ch2, ch3]
  have h' : andB (orbitOK ((sG.getD n []).map fun g => (jwOf g).map NS) (r1.getD n 0)
      (b1.getD n 0) (m1.getD n 0))
      (andB (allFix cL dL (sG.getD n []) (b1.getD n 0) (t2.getD n []))
        (andB (treeOK cL dL ((t2.getD n []).map (expandG (sG.getD n []))) (b2.getD n 0)
          (m2.getD n 0) (O2.getD n []) (T2.getD n []))
          (Nat.ble (ordS.getD n 0) (Nat.mul (m1.getD n 0) (m2.getD n 0))))) = true := h
  obtain ⟨hA, hB⟩ := YModel.Sem.andB_eq h'
  obtain ⟨hB1, hC⟩ := YModel.Sem.andB_eq hB
  obtain ⟨hC1, hC2⟩ := YModel.Sem.andB_eq hC
  have hb1 : b1.getD n 0 < Ly0.deg := by
    simpa [Nat.blt_eq] using getD_all b_lt.1 (by decide : Nat.blt 0 66825 = true) n
  have hb2 : b2.getD n 0 < Ly0.deg := by
    simpa [Nat.blt_eq] using getD_all b_lt.2 (by decide : Nat.blt 0 66825 = true) n
  let β₁ : Fin Ly0.deg := ⟨b1.getD n 0, hb1⟩
  let β₂ : Fin Ly0.deg := ⟨b2.getD n 0, hb2⟩
  have hL : ∀ w ∈ (sG.getD n []).map jwOf, ∀ j ∈ w, j < 6 := by
    intro w hw
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hw
    exact sG_lt' n g hg
  have e : (sG.getD n []).map (fun g => (jwOf g).map NS) =
      ((sG.getD n []).map jwOf).map (fun w => w.map NS) := by
    rw [List.map_map]
    rfl
  rw [e] at hA
  have o1 : m1.getD n 0 ≤ (orbit (SG n) β₁).ncard :=
    orbitOK_sound (SG n) (nets_valid hL) (nets_act hc hd hL (SG n) fun w hw => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hw
      exact Subgroup.subset_closure ⟨g, hg, rfl⟩) β₁ hA
  let K₁ := SG n ⊓ stabilizer (Perm (Fin Ly0.deg)) β₁
  have hfix : ∀ w ∈ t2.getD n [], wP (expandG (sG.getD n []) w) β₁ = β₁ := fun w hw =>
    wG_fix hc hd (allFix_sound hB1 w hw) β₁ List.mem_cons_self
  have o2 : m2.getD n 0 ≤ (orbit K₁ β₂).ncard := by
    refine treeOK_orbit K₁ (fun g => ?_) hC1
    refine ⟨wP (((t2.getD n []).map (expandG (sG.getD n []))).getD g []), ?_,
      fun a => jwPt_wG hc hd (cG_mul_cG hc hd) (dG_pow_three hc hd) _ a⟩
    rw [List.getD_eq_getElem?_getD]
    cases e2 : ((t2.getD n []).map (expandG (sG.getD n [])))[g]? with
    | none =>
      rw [Option.getD_none, wP_nil]
      exact K₁.one_mem
    | some w =>
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? e2)
      exact Subgroup.mem_inf.2 ⟨expandG_mem (gen_mem_SG n) v, mem_stabilizer_iff.2 (hfix v hv)⟩
  have e1 := ncard_orbit_mul_card_inf (SG n) β₁
  have e2 := ncard_orbit_mul_card_inf K₁ β₂
  have hpos : 0 < Nat.card ↥(K₁ ⊓ stabilizer (Perm (Fin Ly0.deg)) β₂) := Nat.card_pos
  have h3 : (orbit K₁ β₂).ncard ≤ Nat.card K₁ := by
    rw [← e2]
    exact Nat.le_mul_of_pos_right _ hpos
  calc ordS.getD n 0 ≤ m1.getD n 0 * m2.getD n 0 := Nat.le_of_ble_eq_true hC2
    _ ≤ (orbit (SG n) β₁).ncard * Nat.card K₁ := Nat.mul_le_mul o1 (o2.trans h3)
    _ = Nat.card (SG n) := e1

def QF (X : Nat) : Prop := ∃ g ∈ Ly0.B0, IsMask (X >>> 131072) (g • O0)

omit hc hd in
theorem o0_lt' : ∀ a ∈ o0, a < Ly0.deg := fun a ha => by
  simpa [Nat.blt_eq] using List.all_eq_true.1 o0_lt a ha

omit hc hd in
theorem isMask_O0 : IsMask (maskOf o0) O0 := isMask_maskOf o0_lt'

theorem qf_net {j : Nat} (hj : j < 6) {X : Nat} (hX : QF X) :
    ∃ g ∈ Ly0.B0, IsMask (X >>> 131072) (g • O0) ∧
      IsMask (net2 (NS j) X >>> 131072) (((rho j)⁻¹ * g) • O0) := by
  obtain ⟨g, hg, hm⟩ := hX
  refine ⟨g, hg, hm, ?_⟩
  rw [mul_smul]
  exact isMask_net2 (by norm_num) (valid_all j hj) (nrep_rho hc hd j hj) hm

theorem qf_step {j : Nat} (hj : j < 6) {X : Nat} (hX : QF X) : QF (net2 (NS j) X) := by
  obtain ⟨g, hg, -, hm⟩ := qf_net hc hd hj hX
  exact ⟨_, Ly0.B0.mul_mem (Ly0.B0.inv_mem (rho_mem j)) hg, hm⟩

omit hc hd in
theorem wk_all : ∀ i < 16, walkSAt i = true := by
  intro i hi
  interval_cases i
  exacts [wk0, wk1, wk2, wk3, wk4, wk5, wk6, wk7, wk8, wk9, wk10, wk11, wk12, wk13, wk14, wk15]

omit hc hd in
theorem cov_parts : covOK dfs = true ∧ incOK kp = true ∧ tabOK tc td ta tb te = true ∧
    root < nL := by
  have h : andB (andB (covOK dfs) (incOK kp)) (andB (tabOK tc td ta tb te) (Nat.blt root nL)) =
    true := cov_all
  obtain ⟨h1, h2⟩ := YModel.Sem.andB_eq h
  obtain ⟨h3, h4⟩ := YModel.Sem.andB_eq h1
  obtain ⟨h5, h6⟩ := YModel.Sem.andB_eq h2
  exact ⟨h3, h4, h5, by simpa [Nat.blt_eq] using h6⟩

theorem entry {l : Nat} (hl : l < nL) :
    ∃ X, QF X ∧ lineS pk kp tc td l X (net2 (NS 0) X) (net2 (NS 1) X) = true := by
  obtain ⟨es, hes, e, he, rfl⟩ := covOK_sound cov_parts.1 l hl
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hes
  have hw : walkSAt i = true := wk_all i (by rw [dfs_length] at hi; exact hi)
  have hw' : walkSFrom (NS 0) (NS 1) pk kp tc td (maskOf o0) (dfs.getD i []) = true := hw
  rw [List.getD_eq_getElem _ _ hi] at hw'
  have h0 : QF (saltOf (maskOf o0)) := ⟨1, Ly0.B0.one_mem, by
    rw [shiftRight_saltOf, one_smul]
    exact isMask_O0⟩
  exact walkSFrom_sound h0 (fun X hX => qf_step hc hd (by decide) hX)
    (fun X hX => qf_step hc hd (by decide) hX) hw' e he

omit hc hd in
theorem keyIs_unique {S : Set (Fin Ly0.deg)} {k k' : Nat} (h : KeyIs S k) (h' : KeyIs S k') :
    k = k' := by
  obtain ⟨M, hM, rfl⟩ := h
  obtain ⟨M', hM', rfl⟩ := h'
  rw [hM.eq hM']

omit hc hd in
theorem key_inj {l l' : Nat} (hl : l < nL) (hl' : l' < nL) (h : fldW 48 kp l = fldW 48 kp l') :
    l = l' := by
  have hs := incOK_sound cov_parts.2.1
  rcases lt_trichotomy l l' with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (hs l l' hlt hl'))
  · exact heq
  · exact absurd h (Nat.ne_of_gt (hs l' l hgt hl))

omit hc hd in
theorem keyIs_of_keyOf {M : Nat} {S : Set (Fin Ly0.deg)} (hM : IsMask M S) {k : Nat}
    (h : keyOf pk M = k) : KeyIs S k := ⟨M, hM, (hM.keyOf_eq pk).symm.trans h⟩

omit hc hd in
theorem keyIs_of_entry {X : Nat} {S : Set (Fin Ly0.deg)} (hm : IsMask (X >>> 131072) S)
    {k : Nat} (hk : keyS pk X = k) : KeyIs S k := ⟨_, hm, hk⟩

theorem line_ex {l : Nat} (hl : l < nL) : ∃ g ∈ Ly0.B0, KeyIs (g • O0) (fldW 48 kp l) := by
  obtain ⟨X, ⟨g, hg, hm⟩, h⟩ := entry hc hd hl
  exact ⟨g, hg, keyIs_of_entry hm (lineS_sound h).1⟩

theorem Lf_spec {l : Nat} (hl : l < nL) :
    (∃ g ∈ Ly0.B0, Lf l = g • O0) ∧ KeyIs (Lf l) (fldW 48 kp l) := by
  have h := line_ex hc hd hl
  classical
  have e : Lf l = h.choose • O0 := by
    unfold Lf
    rw [dif_pos h]
  rw [e]
  exact ⟨⟨_, h.choose_spec.1, rfl⟩, h.choose_spec.2⟩

theorem L_inj : Function.Injective L := by
  intro i j e
  have hi := (Lf_spec hc hd i.2).2
  have hj := (Lf_spec hc hd j.2).2
  change Lf i = Lf j at e
  rw [e] at hi
  exact Fin.ext (key_inj j.2 i.2 (keyIs_unique hj hi)).symm

omit hc hd in
theorem Y0_le : SG 0 ≤ Ly0.B0 := SG_le 0

theorem Y0_fix : ∀ y ∈ SG 0, y • O0 = O0 := by
  have hfix := fixOK_sound fix0_ok
  have hS : SG 0 ≤ stabilizer (Perm (Fin Ly0.deg)) O0 := by
    rw [SG, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    exact smul_eq_of_netsApply (by norm_num) (fun N hN => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hN
      exact valid_all j (sG_lt' 0 g hg j hj)) (compN_wZ hc hd (sG_lt' 0 g hg)) isMask_O0
      (hfix g hg)
  exact fun y hy => hS hy

theorem card_le (hbc : RB5Bound) : Nat.card Ly0.B0 ≤ nL * Nat.card (SG 0) := by
  have h1 := card_B0_le hc hd hbc
  have h2 := card_SG_ge hc hd (n := 0) (by decide)
  have e : ordS.getD 0 0 = 349920 := rfl
  have e' : nL = 15400 := rfl
  rw [e] at h2
  rw [e']
  omega

theorem lines (hbc : RB5Bound) :
    (∀ g ∈ Ly0.B0, ∃ i, g • O0 = L i) ∧ (∀ g ∈ Ly0.B0, g • O0 = O0 → g ∈ SG 0) :=
  lines_of_card Y0_le (Y0_fix hc hd) L (L_inj hc hd) (fun i => (Lf_spec hc hd i.2).1)
    (card_le hc hd hbc)

theorem line_of_key (hbc : RB5Bound) {g : Perm (Fin Ly0.deg)} (hg : g ∈ Ly0.B0) {l : Nat}
    (hl : l < nL) (hk : KeyIs (g • O0) (fldW 48 kp l)) : g • O0 = Lf l := by
  obtain ⟨i, hi⟩ := (lines hc hd hbc).1 g hg
  have hki := (Lf_spec hc hd i.2).2
  change g • O0 = Lf i at hi
  rw [← hi] at hki
  have e := key_inj i.2 hl (keyIs_unique hki hk)
  rw [hi, e]

theorem Lf_moves (hbc : RB5Bound) {l : Nat} (hl : l < nL) :
    (fldW 16 tc l < nL ∧ Lf (fldW 16 tc l) = Ly0.cG⁻¹ • Lf l) ∧
      (fldW 16 td l < nL ∧ Lf (fldW 16 td l) = Ly0.dG⁻¹ • Lf l) := by
  obtain ⟨X, hX, h⟩ := entry hc hd hl
  obtain ⟨k0, k1, k2, k3, k4⟩ := lineS_sound h
  obtain ⟨g, hg, hm, hmc⟩ := qf_net hc hd (j := 0) (by decide) hX
  obtain ⟨g', hg', hm', hmd⟩ := qf_net hc hd (j := 1) (by decide) hX
  have hL : g • O0 = Lf l := line_of_key hc hd hbc hg hl (keyIs_of_entry hm k0)
  have hL' : g' • O0 = Lf l := line_of_key hc hd hbc hg' hl (keyIs_of_entry hm' k0)
  refine ⟨⟨k1, ?_⟩, ⟨k2, ?_⟩⟩
  · rw [← line_of_key hc hd hbc (Ly0.B0.mul_mem (Ly0.B0.inv_mem (rho_mem 0)) hg) k1
      (keyIs_of_entry hmc k3), mul_smul, hL, rho0_eq]
  · rw [← line_of_key hc hd hbc (Ly0.B0.mul_mem (Ly0.B0.inv_mem (rho_mem 1)) hg') k2
      (keyIs_of_entry hmd k4), mul_smul, hL', rho1_eq]

omit hc hd in
theorem int_cases {z : ℤ} (hz : z ≠ 0 ∧ z.natAbs ≤ 2) : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by
  omega

omit hc hd in
theorem letterG_one : Ly0.letterG Ly0.gens0 1 = Ly0.cG := by
  rw [← rho0_eq, rho_eq]
  simp [jZ]

omit hc hd in
theorem letterG_two : Ly0.letterG Ly0.gens0 2 = Ly0.dG := by
  rw [← rho1_eq, rho_eq]
  simp [jZ]

theorem Lf_mvX (hbc : RB5Bound) {z : ℤ} (hz : z ≠ 0 ∧ z.natAbs ≤ 2) {l : Nat} (hl : l < nL) :
    mvX tc td (lcode z) l < nL ∧
      Lf (mvX tc td (lcode z) l) = Ly0.letterG Ly0.gens0 z • Lf l := by
  obtain ⟨⟨c1, c2⟩, ⟨d1, d2⟩⟩ := Lf_moves hc hd hbc hl
  have hcc : Ly0.cG⁻¹ = Ly0.cG := inv_eq_of_mul_eq_one_right (cG_mul_cG hc hd)
  rcases int_cases hz with rfl | rfl | rfl | rfl
  · have e : mvX tc td (lcode 1) l = fldW 16 tc l := rfl
    rw [e, letterG_one]
    refine ⟨c1, ?_⟩
    rw [c2, hcc]
  · have e : mvX tc td (lcode (-1)) l = fldW 16 tc l := rfl
    rw [e, Ly0.letterG_neg _ one_ne_zero, letterG_one]
    exact ⟨c1, c2⟩
  · have e : mvX tc td (lcode 2) l = fldW 16 td (fldW 16 td l) := strictN_eq _ _
    obtain ⟨⟨-, -⟩, ⟨d1', d2'⟩⟩ := Lf_moves hc hd hbc d1
    have hdd : Ly0.dG⁻¹ * Ly0.dG⁻¹ = Ly0.dG := by
      calc Ly0.dG⁻¹ * Ly0.dG⁻¹ = Ly0.dG⁻¹ * Ly0.dG⁻¹ * Ly0.dG ^ 3 := by
            rw [dG_pow_three hc hd, mul_one]
        _ = Ly0.dG := by group
    rw [e, letterG_two]
    refine ⟨d1', ?_⟩
    rw [d2', d2, ← mul_smul, hdd]
  · have e : mvX tc td (lcode (-2)) l = fldW 16 td l := rfl
    rw [e, Ly0.letterG_neg _ two_ne_zero, letterG_two]
    exact ⟨d1, d2⟩

theorem Lf_mvC (hbc : RB5Bound) (ws : List ℤ) (hws : ∀ z ∈ ws, z ≠ 0 ∧ z.natAbs ≤ 2) {l : Nat}
    (hl : l < nL) :
    mvC tc td (ws.map lcode) l < nL ∧
      Lf (mvC tc td (ws.map lcode) l) = Ly0.wG Ly0.gens0 ws • Lf l := by
  induction ws with
  | nil =>
    refine ⟨hl, ?_⟩
    change Lf l = Ly0.wG Ly0.gens0 [] • Lf l
    rw [Ly0.wG_nil, one_smul]
  | cons z ws ih =>
    have ih' := ih fun z' hz' => hws z' (List.mem_cons_of_mem _ hz')
    have e : mvC tc td ((z :: ws).map lcode) l =
        mvX tc td (lcode z) (mvC tc td (ws.map lcode) l) := strictN_eq _ _
    have hx := Lf_mvX hc hd hbc (hws z List.mem_cons_self) ih'.1
    rw [e, Ly0.wG_cons, mul_smul, ← ih'.2]
    exact hx

theorem Lf_mvL (hbc : RB5Bound) {j : Nat} (hj : j < 6) {l : Nat} (hl : l < nL) :
    mvL tabs j l < nL ∧ Lf (mvL tabs j l) = rho j • Lf l := by
  have ht := tabOK_sound cov_parts.2.2.1 l hl
  have e : mvL tabs j l = mvC tc td (jC j) l := by
    interval_cases j
    · have e0 : mvC tc td (jC 0) l = mvX tc td 0 l := strictN_eq _ _
      exact (rfl : mvL tabs 0 l = mvX tc td 0 l).trans e0.symm
    · have e1 : mvC tc td (jC 1) l = mvX tc td 2 l := strictN_eq _ _
      exact (rfl : mvL tabs 1 l = mvX tc td 2 l).trans e1.symm
    · have e2 : mvC tc td (jC 2) l = mvX tc td 3 l := strictN_eq _ _
      exact (rfl : mvL tabs 2 l = mvX tc td 3 l).trans e2.symm
    · exact ht.1
    · exact ht.2.1
    · exact ht.2.2
  rw [e, jC_eq, rho_eq]
  exact Lf_mvC hc hd hbc (jZ j) (jZ_mem j) hl

theorem Lf_mvJ (hbc : RB5Bound) (w : List Nat) (hw : ∀ j ∈ w, j < 6) {l : Nat} (hl : l < nL) :
    mvJ tabs w l < nL ∧ Lf (mvJ tabs w l) = wP w • Lf l := by
  induction w with
  | nil =>
    refine ⟨hl, ?_⟩
    change Lf l = wP [] • Lf l
    rw [wP_nil, one_smul]
  | cons j w ih =>
    have ih' := ih fun j' hj' => hw j' (List.mem_cons_of_mem _ hj')
    have e : mvJ tabs (j :: w) l = mvL tabs j (mvJ tabs w l) := strictN_eq _ _
    have hx := Lf_mvL hc hd hbc (hw j List.mem_cons_self) ih'.1
    rw [e, wP_cons, mul_smul, ← ih'.2]
    exact hx

theorem Lf_root (hbc : RB5Bound) : Lf root = O0 := by
  have hk : KeyIs O0 (fldW 48 kp root) := keyIs_of_keyOf isMask_O0 (Nat.eq_of_beq_eq_true root_key)
  have h := line_of_key hc hd hbc Ly0.B0.one_mem cov_parts.2.2.2 (by rw [one_smul]; exact hk)
  rw [one_smul] at h
  exact h.symm

theorem forest (hbc : RB5Bound) {n : Nat} (hn : n < 4) :
    ∀ l < nL, ∃ s ∈ SG n, ∃ r ∈ RS (n + 1), Lf l = (s * r) • O0 := by
  have hfr : frAt n = true := by
    interval_cases n
    exacts [fr0, fr1, fr2, fr3]
  have hrep : ∀ p, (nt.getD p (0, 0)).1 = n + 1 →
      (mvJ tabs (jwOf (rep.getD p [])) root < nL ∧
        ∃ s ∈ SG n, ∃ r ∈ RS (n + 1), Lf (mvJ tabs (jwOf (rep.getD p [])) root) = (s * r) • O0) := by
    intro p hp
    have hm := Lf_mvJ hc hd hbc (jwOf (rep.getD p [])) (rep_getD_lt p) cov_parts.2.2.2
    refine ⟨hm.1, 1, (SG n).one_mem, _, ⟨p, hp, rfl⟩, ?_⟩
    rw [hm.2, Lf_root hc hd hbc, one_mul]
  have hgen : ∀ s l, (l < nL ∧ ∃ s' ∈ SG n, ∃ r ∈ RS (n + 1), Lf l = (s' * r) • O0) →
      (mvJ tabs (jwOf ((sG.getD n []).getD s [])) l < nL ∧ ∃ s' ∈ SG n, ∃ r ∈ RS (n + 1),
        Lf (mvJ tabs (jwOf ((sG.getD n []).getD s [])) l) = (s' * r) • O0) := by
    rintro s l ⟨hl, s', hs', r, hr, e⟩
    have hm := Lf_mvJ hc hd hbc _ (sG_getD_lt n s) hl
    refine ⟨hm.1, wP (jwOf ((sG.getD n []).getD s [])) * s', (SG n).mul_mem (gen_mem_SG n s) hs',
      r, hr, ?_⟩
    rw [hm.2, e, ← mul_smul, mul_assoc]
  have h := frOK_sound (T := tabs) (nt := nt) (rep := rep) (G := sG.getD n []) (node := n + 1)
    (root := root) (es := frs.getD n [])
    (Q := fun l => l < nL ∧ ∃ s ∈ SG n, ∃ r ∈ RS (n + 1), Lf l = (s * r) • O0) hrep hgen hfr
  exact fun l hl => (h l hl).2

theorem cover_node (hbc : RB5Bound) {n : Nat} (hn : n < 4) :
    ∀ g ∈ Ly0.B0, ∃ s ∈ SG n, ∃ r ∈ RS (n + 1), ∃ y ∈ SG 0, g = s * r * y :=
  cover_of_lines (L := L) (lines hc hd hbc).1 (lines hc hd hbc).2 (SG_le n) (RS_sub (n + 1))
    fun i => forest hc hd hbc hn i i.2

end Letters

end CertificateChecks.KernelLyDce

end
