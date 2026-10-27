module

public import Certificates.Kernel.Om2K.EnumGlue
public import Certificates.Data.Holder1711.Om2Facts
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import Certificates.Kernel.Om2K.BJoin

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Raw.Orb CFSG.KC.BfsPin
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (reflTab)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711 (Om2Facts.E Om2Facts.G)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711 (OmGen.BadElt Om2Facts.Yg Om2Facts.t
  Om2Facts.tc Om2Facts.R Om2Facts.cP Om2Facts.Zt1 Om2Facts.Zt4 Om2Facts.D Om2Facts.TwinFail
  Om2Facts.S8)

abbrev PR (P : Nat) (g : Equiv.Perm (Fin 480)) : Prop := PRep 480 9 P g

theorem pr_ip {P : Nat} {g : Equiv.Perm (Fin 480)} (h : PR P g) (x : Fin 480) :
    ip P x = g x := h x

theorem pr_pc {P Q : Nat} {g h : Equiv.Perm (Fin 480)} (hP : PR P g) (hQ : PR Q h) :
    PR (pc P Q) (g * h) := prep_pcomp (by norm_num) hP hQ

theorem pr_pid : PR pid 1 := prep_pidn (by norm_num) (by norm_num)

theorem pr_eq {P : Nat} {g h : Equiv.Perm (Fin 480)} (hg : PR P g) (hh : PR P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem pr_ne {P Q : Nat} {g h : Equiv.Perm (Fin 480)} (hP : PR P g) (hQ : PR Q h)
    (hne : NeAt P Q) : g ≠ h := by
  rintro rfl
  unfold NeAt at hne
  obtain ⟨p, hp, e⟩ := hne
  exact e ((hP ⟨p, hp⟩).trans (hQ ⟨p, hp⟩).symm)

theorem ip_pc {P Q i : Nat} (hi : i < 480) : ip (pc P Q) i = ip P (ip Q i) :=
  PF.pg_pcomp (by norm_num) hi

theorem ip_lt {Q : Nat} (hQ : cnK Q = true) {i : Nat} (hi : i < 480) : ip Q i < 480 :=
  Nat.blt_eq.mp (allN_spec (range_of_canonK hQ) i hi)

theorem pr_inv {P Q : Nat} {g : Equiv.Perm (Fin 480)} (hP : PR P g) (hQ : cnK Q = true)
    (h : pc P Q = pid) : PR Q g⁻¹ := by
  intro x
  have hlt := ip_lt hQ x.2
  have e : ip (pc P Q) x = ip pid x := by rw [h]
  rw [ip_pc x.2, pr_ip pr_pid] at e
  have e2 : g ⟨ip Q x, hlt⟩ = x := Fin.ext ((pr_ip hP _).symm.trans e)
  have e3 : g⁻¹ x = ⟨ip Q x, hlt⟩ := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact e2.symm
  change ip Q x = ((g⁻¹ x : Fin 480) : Nat)
  rw [e3]

theorem pr_conj {A B C : Nat} {a b : Equiv.Perm (Fin 480)} (hA : PR A a) (hB : PR B b)
    (h : pc A B = pc C A) : PR C (a * b * a⁻¹) := by
  intro y
  have e : ip (pc A B) (a⁻¹ y) = ip (pc C A) (a⁻¹ y) := by rw [h]
  have hy : a (a⁻¹ y) = y := by simp
  rw [ip_pc (a⁻¹ y).2, ip_pc (a⁻¹ y).2, pr_ip hA (a⁻¹ y), hy, pr_ip hB, pr_ip hA] at e
  change ip C y = _
  rw [← e]
  simp [Equiv.Perm.mul_apply]

theorem okK_valid {P : Nat} (h : okK P = true) : validA 480 (unpack 480 9 P) = true :=
  validA_ok h

theorem pr_of_ok {P : Nat} (h : okK P = true) : PR P (permOfArr 480 (unpack 480 9 P)) :=
  prep_of_rep (rep_of_validA (okK_valid h))

theorem pr_of_valid {P : Nat} (h : validA 480 (unpack 480 9 P) = true) :
    PR P (permOfArr 480 (unpack 480 9 P)) :=
  prep_of_rep (rep_of_validA h)

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem fld_le (r o m : Nat) : fld(r, o, m) ≤ m := Nat.and_le_right

theorem pr_ipn {P : Nat} {g : Equiv.Perm (Fin 480)} (h : PR P g) {p : Nat} (hp : p < 480) :
    ip P p = (g ⟨p, hp⟩ : Nat) := h ⟨p, hp⟩

theorem pr_inv_eq {P Q : Nat} {g h : Equiv.Perm (Fin 480)} (hP : PR P g) (hQ : PR Q h)
    (e : pc P Q = pid) : h = g⁻¹ := by
  have h1 := pr_pc hP hQ
  rw [e] at h1
  exact eq_inv_of_mul_eq_one_right (pr_eq h1 pr_pid)

theorem pr_ne_comm {A B : Nat} {a b : Equiv.Perm (Fin 480)} (ha : PR A a) (hb : PR B b)
    {p : Nat} (hp : p < 480) (hne : ip A (ip B p) ≠ ip B (ip A p)) : a * b ≠ b * a := by
  intro e
  apply hne
  rw [pr_ipn hb hp, pr_ip ha, pr_ipn ha hp, pr_ip hb]
  exact congrArg (fun z : Equiv.Perm (Fin 480) => ((z ⟨p, hp⟩ : Fin 480) : Nat)) e

theorem pr_comm {A B : Nat} {a b : Equiv.Perm (Fin 480)} (ha : PR A a) (hb : PR B b)
    (e : pc A B = pc B A) : a * b = b * a := by
  have h := pr_pc ha hb
  rw [e] at h
  exact pr_eq h (pr_pc hb ha)

theorem getD_mem {ws : List (List Nat)} {k : Nat} (hk : k < ws.length) : ws.getD k [] ∈ ws := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem _

theorem E_mem_G {ws : List (List Nat)} {w : List Nat} (hw : w ∈ ws) :
    Om2Facts.E w ∈ Om2Facts.G ws := by
  unfold Om2Facts.G
  exact Subgroup.subset_closure ⟨w, hw, rfl⟩

theorem pr_E {w : List Nat} {P : Nat} (he : wY LY w = unpack 480 9 P) (hP : okK P = true) :
    PR P (Om2Facts.E w) := by
  unfold Om2Facts.E
  rw [he]
  exact pr_of_ok hP

theorem E_nil : Om2Facts.E [] = 1 := by
  unfold Om2Facts.E
  exact permOfArr_eq_of_rep rep_idA

theorem pr_EL {k : Nat} (hk : k < 7) : PR (EL.G k) (Om2Facts.E (elW.getD k [])) :=
  pr_E (el_eq hk) (el_ok hk)

theorem pr_t : PR (EL.G 0) Om2Facts.t := pr_EL (k := 0) (by norm_num)

theorem pr_i0 : PR (EL.G 1) (Om2Facts.E wI0) := pr_EL (k := 1) (by norm_num)

theorem pr_j0 : PR (EL.G 2) (Om2Facts.E wJ0) := pr_EL (k := 2) (by norm_num)

theorem pr_tc : PR (EL.G 3) Om2Facts.tc := pr_EL (k := 3) (by norm_num)

theorem pr_TG {k : Nat} (hk : k < 8) : PR (TG.G k) (Om2Facts.E (wT.getD k [])) :=
  pr_E (tg_eq hk) (tg_ok hk)

theorem pr_FU {k : Nat} (hk : k < 3) : PR (FU.G k) (Om2Facts.E (wFuse0.getD k [])) :=
  pr_E (fu_eq hk) (fu_ok hk)

theorem pr_CC {k : Nat} (hk : k < 5) : PR (CC.G k) (Om2Facts.E (wCc.getD k [])) :=
  pr_E (cc_eq hk) (allN_spec kOkC k hk)

theorem tg_mem : ∀ k < 8, ∃ g ∈ Om2Facts.G wT, PR (TG.G k) g := fun k hk =>
  ⟨_, E_mem_G (getD_mem (by rw [wT_len]; exact hk)), pr_TG hk⟩

theorem cc_mem : ∀ k < 5, ∃ g ∈ Om2Facts.G wCc, PR (CC.G k) g := fun k hk =>
  ⟨_, E_mem_G (getD_mem (by rw [wCc_len]; exact hk)), pr_CC hk⟩

theorem t_sq : Om2Facts.t * Om2Facts.t = 1 := by
  have h := pr_pc pr_t pr_t
  rw [Nat.eq_of_beq_eq_true kR2] at h
  exact pr_eq h pr_pid

theorem tc_sq : Om2Facts.tc * Om2Facts.tc = 1 := by
  have h := pr_pc pr_tc pr_tc
  rw [Nat.eq_of_beq_eq_true kR7] at h
  exact pr_eq h pr_pid

theorem pr_cA {k : Nat} (hk : k < 3) : PR (cAK k) (Om2Facts.cP k) := by
  unfold Om2Facts.cP
  rw [cA_eq hk]
  exact pr_of_ok (cA_ok hk)

theorem pr_ZT0 : PR (BD.ZT 0) Om2Facts.t := by
  rw [(zOK_sound (allN_spec kZT 0 (by norm_num))).1 rfl]
  exact pr_t

theorem pr_ZTk {k : Nat} (hk0 : k ≠ 0) (hk : k < 4) :
    PR (BD.ZT k) (Om2Facts.t * Om2Facts.cP (k - 1)) := by
  rw [(zOK_sound (allN_spec kZT k hk)).2 hk0]
  exact pr_pc pr_t (pr_cA (by omega))

theorem LY_valid {l : Nat} (hl : l < 16) : validA 480 LY[l]! = true := by
  rw [letters_get hl]
  exact okK_valid (L_ok hl)

theorem E_single {l : Nat} (hl : l < 16) : Om2Facts.E [l] = permOfArr 480 LY[l]! := by
  have h := rep_compA (rep_of_validA (LY_valid hl)) (rep_idA (n := 480))
  rw [mul_one] at h
  exact permOfArr_eq_of_rep h

theorem pr_L {l : Nat} (hl : l < 16) : PR (L.G l) (Om2Facts.E [l]) := by
  rw [E_single hl, letters_get hl]
  exact pr_of_ok (L_ok hl)

theorem E_single_inv {l : Nat} (hl : 8 ≤ l) (hl' : l < 16) :
    Om2Facts.E [l] = (Om2Facts.E [l - 8])⁻¹ := by
  have e := Nat.eq_of_beq_eq_true (allN_spec kInv (l - 8) (by omega))
  have e2 : Nat.add (l - 8) 8 = l := by
    change l - 8 + 8 = l
    omega
  rw [e2] at e
  have hr : Rep 480 (unpack 480 9 (L.G l)) (permOfArr 480 (unpack 480 9 (L.G (l - 8))))⁻¹ := by
    rw [e, ← invCand_pinv (L_ok (by omega))]
    exact rep_inv_of_validA (okK_valid (L_ok (by omega)))
  rw [E_single hl', E_single (by omega), letters_get hl', letters_get (by omega)]
  exact permOfArr_eq_of_rep hr

theorem E_single_mem {l : Nat} (hl : l < 16) : Om2Facts.E [l] ∈ Om2Facts.Yg := by
  have gen : ∀ i < 8, Om2Facts.E [i] ∈ Om2Facts.Yg := fun i hi => by
    unfold Om2Facts.Yg Om2Facts.G
    exact Subgroup.subset_closure ⟨[i], List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩, rfl⟩
  by_cases h : l < 8
  · exact gen l h
  · rw [E_single_inv (by omega) hl]
    exact inv_mem (gen _ (by omega))

theorem G_eq (ws : List (List Nat)) :
    Om2Facts.G ws = Subgroup.closure (permsA 480 (ws.map (wY LY)).toArray) := by
  unfold Om2Facts.G
  congr 1
  ext x
  simp only [permsA, Set.mem_image, Set.mem_setOf_eq, List.size_toArray, List.length_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    refine ⟨k, hk, ?_⟩
    rw [getElem!_pos _ k (by simpa using hk)]
    simp [Om2Facts.E]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨ws[k], List.getElem_mem hk, ?_⟩
    rw [getElem!_pos _ k (by simpa using hk)]
    simp [Om2Facts.E]

theorem enum_pr {ws : List (List Nat)} {ng N sz : Nat} {G T E S : Nat → Nat} {SK : List Nat}
    (hlt : ∀ w ∈ ws, ∀ l ∈ w, l < 16) (hlen : ws.length = ng)
    (hG : allN ng (genOK ws G) = true) (hk : bfsK 480 9 ng G N T E S = true)
    (hK : keysSK 480 9 keyPtsYA.toList N T SK = true) (hN : N = sz) :
    (∀ i < sz, PR (T i) (permOfArr 480 (unpack 480 9 (T i)))) ∧
      ∀ x ∈ Om2Facts.G ws, ∃ i < sz, PR (T i) x := by
  obtain ⟨h1, h2⟩ := enum_of hlt hlen hG hk hK hN
  subst hN
  have hps : ∀ p ∈ keyPtsY, p < 480 := by decide
  obtain ⟨hmem, -, hval⟩ := enumOK_spec hps h1
  have hsz : (enumOfY LY ws (N + 1)).pts.size = N := by rw [h2, Array.size_ofFn]
  have hget : ∀ i < N, (enumOfY LY ws (N + 1)).pts[i]! = unpack 480 9 (T i) := by
    intro i hi
    rw [getElem!_pos _ i (by rw [hsz]; exact hi)]
    simp only [h2, Array.getElem_ofFn]
  have hv : ∀ i < N, PR (T i) (permOfArr 480 (unpack 480 9 (T i))) := fun i hi => by
    have := hval i (by rw [hsz]; exact hi)
    rw [hget i hi] at this
    exact pr_of_valid this
  refine ⟨hv, fun x hx => ?_⟩
  rw [G_eq] at hx
  obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
  rw [hsz] at hi
  rw [hget i hi]
  exact ⟨i, hi, hv i hi⟩

theorem enum0 : (∀ i < 4096, PR (E0.T i) (permOfArr 480 (unpack 480 9 (E0.T i)))) ∧
    ∀ x ∈ Om2Facts.G wS0, ∃ i < 4096, PR (E0.T i) x :=
  enum_pr wS0_lt (by decide) kEG0 okE0 E0.keys rfl

theorem enum1 : (∀ i < 27, PR (E1.T i) (permOfArr 480 (unpack 480 9 (E1.T i)))) ∧
    ∀ x ∈ Om2Facts.G wP3, ∃ i < 27, PR (E1.T i) x :=
  enum_pr wP3_lt (by decide) kEG1 okE1 E1.keys rfl

theorem enum2 : (∀ i < 1024, PR (E2.T i) (permOfArr 480 (unpack 480 9 (E2.T i)))) ∧
    ∀ x ∈ Om2Facts.G wSc, ∃ i < 1024, PR (E2.T i) x :=
  enum_pr wSc_lt (by decide) kEG2 okE2 E2.keys rfl

theorem enum4 : (∀ i < 4608, PR (E4.T i) (permOfArr 480 (unpack 480 9 (E4.T i)))) ∧
    ∀ x ∈ Om2Facts.G wCR, ∃ i < 4608, PR (E4.T i) x :=
  enum_pr wCR_lt (by decide) kEG4 okE4 E4.keys rfl

theorem ncard_le_of_pr {s : Set (Equiv.Perm (Fin 480))} {L : List Nat} {T : Nat → Nat}
    (h : ∀ x ∈ s, ∃ i ∈ L, PR (T i) x) : s.ncard ≤ L.length := by
  have hsub : s ⊆ (fun i => permOfArr 480 (unpack 480 9 (T i))) '' (L.toFinset : Set Nat) := by
    intro x hx
    obtain ⟨i, hi, hp⟩ := h x hx
    refine ⟨i, by simpa using hi, ?_⟩
    exact permOfArr_eq_of_rep (fun y => (unpack_get y.2).trans (hp y))
  calc s.ncard
      ≤ ((fun i => permOfArr 480 (unpack 480 9 (T i))) '' (L.toFinset : Set Nat)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (L.toFinset : Set Nat).ncard := Set.ncard_image_le L.toFinset.finite_toSet
    _ = L.toFinset.card := Set.ncard_coe_finset _
    _ ≤ L.length := List.toFinset_card_le _

theorem ng_conj : ∀ j < 409, ∃ g ∈ Om2Facts.Yg, PR (BD.NG j) (g * Om2Facts.t * g⁻¹) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    obtain ⟨-, -, -, h0, h1⟩ := nodeOK_sound (allN_spec kNodes j hj)
    by_cases hj0 : j = 0
    · subst hj0
      refine ⟨1, Om2Facts.Yg.one_mem, ?_⟩
      rw [h0 rfl]
      simpa using pr_t
    · obtain ⟨par, hpar, l, hl, e⟩ := h1 hj0
      obtain ⟨g, hg, hp⟩ := ih par hpar (by omega)
      have := pr_conj (pr_L hl) hp e
      refine ⟨Om2Facts.E [l] * g, Om2Facts.Yg.mul_mem (E_single_mem hl) hg, ?_⟩
      convert this using 1
      group

theorem ng_D1 {j : Nat} (hj : j < 409) (hf : fld(BD.NF j, 0, 1) = 1) {d : Equiv.Perm (Fin 480)}
    (hd : PR (BD.NG j) d) : d ∈ Om2Facts.D Om2Facts.Zt1 := by
  obtain ⟨g, hg, hp⟩ := ng_conj j hj
  obtain ⟨-, hne, -⟩ := nodeOK_sound (allN_spec kNodes j hj)
  refine ⟨g, hg, pr_eq hd hp, ?_⟩
  have := pr_ne hd pr_ZT0 (hne hf)
  simpa [Om2Facts.Zt1] using this

theorem ng_D4 {j : Nat} (hj : j < 409) (hf : fld(BD.NF j, 0, 1) = 1)
    (hf4 : fld(BD.NF j, 10, 1) = 1) {d : Equiv.Perm (Fin 480)} (hd : PR (BD.NG j) d) :
    d ∈ Om2Facts.D Om2Facts.Zt4 := by
  obtain ⟨g, hg, hp⟩ := ng_conj j hj
  obtain ⟨-, hne, hne4, -⟩ := nodeOK_sound (allN_spec kNodes j hj)
  refine ⟨g, hg, pr_eq hd hp, ?_⟩
  have h0 := pr_ne hd pr_ZT0 (hne hf)
  have h1 := pr_ne hd (pr_ZTk (k := 1) (by norm_num) (by norm_num))
    (hne4 hf4 1 (by norm_num) (by norm_num))
  have h2 := pr_ne hd (pr_ZTk (k := 2) (by norm_num) (by norm_num))
    (hne4 hf4 2 (by norm_num) (by norm_num))
  have h3 := pr_ne hd (pr_ZTk (k := 3) (by norm_num) (by norm_num))
    (hne4 hf4 3 (by norm_num) (by norm_num))
  simp only [Om2Facts.Zt4, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨h0, h1, h2, h3⟩

abbrev Cl (x : Equiv.Perm (Fin 480)) : Subgroup (Equiv.Perm (Fin 480)) :=
  Subgroup.closure ((Om2Facts.R : Set (Equiv.Perm (Fin 480))) ∪
    {y | ∃ h ∈ Om2Facts.G wT, y = h * x * h⁻¹})

theorem pr_KG : ∀ k < 8, ∃ g ∈ Om2Facts.R, PR (BD.KG k) g := by
  intro k hk
  rw [kgOK_sound (allN_spec kKG k hk)]
  have ha : Om2Facts.E wI0 ∈ Om2Facts.R := by
    unfold Om2Facts.R
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : Om2Facts.E wJ0 ∈ Om2Facts.R := by
    unfold Om2Facts.R
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have p11 := pr_pc pr_i0 pr_i0
  have p111 := pr_pc p11 pr_i0
  have m11 := Om2Facts.R.mul_mem ha ha
  have m111 := Om2Facts.R.mul_mem m11 ha
  interval_cases k
  · exact ⟨1, Om2Facts.R.one_mem, pr_pid⟩
  · exact ⟨_, ha, pr_i0⟩
  · exact ⟨_, m11, p11⟩
  · exact ⟨_, m111, p111⟩
  · exact ⟨_, hb, pr_j0⟩
  · exact ⟨_, Om2Facts.R.mul_mem hb ha, pr_pc pr_j0 pr_i0⟩
  · exact ⟨_, Om2Facts.R.mul_mem hb m11, pr_pc pr_j0 p11⟩
  · exact ⟨_, Om2Facts.R.mul_mem hb m111, pr_pc pr_j0 p111⟩

theorem pr_gI {G : Nat → Nat} {ng k : Nat} {S : Subgroup (Equiv.Perm (Fin 480))}
    (hG : ∀ k < ng, ∃ g ∈ S, PR (G k) g) (hk : k ≤ ng) : ∃ g ∈ S, PR (gI G ng k) g := by
  unfold gI
  cases hb : Nat.beq k ng
  · have hne : k ≠ ng := Nat.ne_of_beq_eq_false hb
    obtain ⟨g, hg, hp⟩ := hG k (by omega)
    exact ⟨g, hg, hp⟩
  · exact ⟨1, S.one_mem, pr_pid⟩

theorem pr_Lh {G A AI R : Nat → Nat} {ng nL : Nat} {S : Subgroup (Equiv.Perm (Fin 480))}
    (hG : ∀ k < ng, ∃ g ∈ S, PR (G k) g) (hc : allN nL (lhOK G A AI R ng) = true) :
    ∀ h < nL, ∃ s ∈ S, PR (A h) s ∧ PR (AI h) s⁻¹ := by
  intro h hh
  obtain ⟨a, ha, b, hb, e1, e2, e3⟩ := lhOK_sound (allN_spec hc h hh)
  obtain ⟨g1, hg1, p1⟩ := pr_gI hG ha
  obtain ⟨g2, hg2, p2⟩ := pr_gI hG hb
  have hA : PR (A h) (g1 * g2) := by
    rw [e1]
    exact pr_pc p1 p2
  exact ⟨g1 * g2, S.mul_mem hg1 hg2, hA, pr_inv hA e3 e2⟩

theorem lhT : ∀ h < 73, ∃ s ∈ Om2Facts.G wT, PR (BD.LhG h) s ∧ PR (BD.LhI h) s⁻¹ :=
  pr_Lh tg_mem kLh

theorem lcC : ∀ h < 31, ∃ s ∈ Om2Facts.G wCc, PR (BD.LcG h) s ∧ PR (BD.LcI h) s⁻¹ :=
  pr_Lh cc_mem kLc

theorem wLet_mem {X XV l : Nat} {x : Equiv.Perm (Fin 480)} (hx : PR X x)
    (hxv : wInv l = true → PR XV x⁻¹) (hl : wLetOK l = true) :
    ∃ g ∈ Cl x, PR (wLet X XV l) g := by
  have hty : fld(l, 0, 3) ≤ 3 := fld_le _ _ _
  unfold wLetOK at hl
  unfold wInv at hxv
  unfold wLet
  simp only [strictB_eq] at hl
  simp only [strictN_eq]
  generalize fld(l, 2, 127) = k at hl ⊢
  generalize fld(l, 0, 3) = ty at hl hxv hty ⊢
  interval_cases ty
  · obtain ⟨g, hg, hp⟩ := pr_KG k (Nat.blt_eq.mp hl)
    exact ⟨g, Subgroup.subset_closure (Or.inl hg), hp⟩
  · obtain ⟨s, hs, hS, hSI⟩ := lhT k (Nat.blt_eq.mp hl)
    refine ⟨s * x * s⁻¹, Subgroup.subset_closure (Or.inr ⟨s, hs, rfl⟩), ?_⟩
    have := pr_pc hS (pr_pc hx hSI)
    rw [← mul_assoc] at this
    exact this
  · obtain ⟨s, hs, hS, hSI⟩ := lhT k (Nat.blt_eq.mp hl)
    refine ⟨(s * x * s⁻¹)⁻¹, inv_mem (Subgroup.subset_closure (Or.inr ⟨s, hs, rfl⟩)), ?_⟩
    have := pr_pc hS (pr_pc (hxv rfl) hSI)
    convert this using 1
    group
  · exact ⟨x, Subgroup.subset_closure (Or.inr ⟨1, one_mem _, by group⟩), hx⟩

theorem wProd_mem {X XV nl l1 l2 l3 : Nat} {x : Equiv.Perm (Fin 480)} (hx : PR X x)
    (hxv : (wInv l1 || wInv l2 || wInv l3) = true → PR XV x⁻¹)
    (h1 : wLetOK l1 = true) (h2 : wLetOK l2 = true) (h3 : wLetOK l3 = true)
    (hnl : nl < 4) (hnl0 : nl ≠ 0) : ∃ g ∈ Cl x, PR (wProd X XV nl l1 l2 l3) g := by
  obtain ⟨g1, m1, p1⟩ := wLet_mem hx (fun h => hxv (by simp [h])) h1
  obtain ⟨g2, m2, p2⟩ := wLet_mem hx (fun h => hxv (by simp [h])) h2
  obtain ⟨g3, m3, p3⟩ := wLet_mem hx (fun h => hxv (by simp [h])) h3
  have hnl1 : 1 ≤ nl := Nat.pos_of_ne_zero hnl0
  unfold wProd
  interval_cases nl
  · exact ⟨g1, m1, p1⟩
  · exact ⟨g1 * g2, mul_mem m1 m2, pr_pc p1 p2⟩
  · exact ⟨g1 * (g2 * g3), mul_mem m1 (mul_mem m2 m3), pr_pc p1 (pr_pc p2 p3)⟩

theorem bad_of_wit {En W : Nat → Nat} {nE f i : Nat} {x : Equiv.Perm (Fin 480)}
    {Dset : Set (Equiv.Perm (Fin 480))}
    (hEv : ∀ i < nE, PR (En i) (permOfArr 480 (unpack 480 9 (En i))))
    (hx : PR (En i) x) (hw : witOK En nE W i = true) (hn : noWit W f i = false)
    (hD : ∀ j < 409, fld(BD.NF j, 0, 1) = 1 → fld(BD.NF j, f, 1) = 1 →
      ∀ d, PR (BD.NG j) d → d ∈ Dset) :
    OmGen.BadElt (Om2Facts.G wT) Om2Facts.R Dset x := by
  obtain ⟨hne0, hfl⟩ := noWit_sound hn
  rcases witOK_sound hw with h0 | ⟨hnl, hxi, hj, hf0, hl1, hl2, hl3, hinv, hval⟩
  · exact absurd h0 hne0
  · have hxv : (wInv fld(W i, 2, 511) || wInv fld(W i, 11, 511) || wInv fld(W i, 20, 511)) =
        true → PR (En fld(W i, 29, 8191)) x⁻¹ := fun h => by
      have hv := hEv _ hxi
      rw [pr_inv_eq hx hv (hinv h)] at hv
      exact hv
    obtain ⟨g, hg, hp⟩ := wProd_mem hx hxv hl1 hl2 hl3 hnl hne0
    rw [hval] at hp
    exact ⟨g, hD _ hj hf0 hfl g hp, hg⟩

theorem bad_count {En W : Nat → Nat} {nE f bound : Nat} {ws : List (List Nat)}
    {Dset : Set (Equiv.Perm (Fin 480))}
    (hEv : ∀ i < nE, PR (En i) (permOfArr 480 (unpack 480 9 (En i))))
    (hEc : ∀ x ∈ Om2Facts.G ws, ∃ i < nE, PR (En i) x)
    (hw : ∀ i < nE, witOK En nE W i = true)
    (hD : ∀ j < 409, fld(BD.NF j, 0, 1) = 1 → fld(BD.NF j, f, 1) = 1 →
      ∀ d, PR (BD.NG j) d → d ∈ Dset)
    (hc : ((List.range nE).filter (noWit W f)).length ≤ bound) :
    {x | x ∈ Om2Facts.G ws ∧ ¬ OmGen.BadElt (Om2Facts.G wT) Om2Facts.R Dset x}.ncard ≤
      bound := by
  refine (ncard_le_of_pr (T := En) fun x hx => ?_).trans hc
  obtain ⟨i, hi, hp⟩ := hEc x hx.1
  refine ⟨i, List.mem_filter.2 ⟨List.mem_range.2 hi, ?_⟩, hp⟩
  cases hnw : noWit W f i
  · exact absurd (bad_of_wit hEv hp (hw i hi) hnw hD) hx.2
  · rfl

theorem bad_fact :
    {x | x ∈ Om2Facts.G wS0 ∧
      ¬ OmGen.BadElt (Om2Facts.G wT) Om2Facts.R (Om2Facts.D Om2Facts.Zt1) x}.ncard ≤ 8 ∧
    {x | x ∈ Om2Facts.G wP3 ∧
      ¬ OmGen.BadElt (Om2Facts.G wT) Om2Facts.R (Om2Facts.D Om2Facts.Zt1) x}.ncard ≤ 1 ∧
    {x | x ∈ Om2Facts.G wS0 ∧
      ¬ OmGen.BadElt (Om2Facts.G wT) Om2Facts.R (Om2Facts.D Om2Facts.Zt4) x}.ncard ≤ 1184 ∧
    {x | x ∈ Om2Facts.G wP3 ∧
      ¬ OmGen.BadElt (Om2Facts.G wT) Om2Facts.R (Om2Facts.D Om2Facts.Zt4) x}.ncard ≤ 19 := by
  have hD1 : ∀ j < 409, fld(BD.NF j, 0, 1) = 1 → fld(BD.NF j, 0, 1) = 1 →
      ∀ d, PR (BD.NG j) d → d ∈ Om2Facts.D Om2Facts.Zt1 :=
    fun j hj h0 _ d hd => ng_D1 hj h0 hd
  have hD4 : ∀ j < 409, fld(BD.NF j, 0, 1) = 1 → fld(BD.NF j, 10, 1) = 1 →
      ∀ d, PR (BD.NG j) d → d ∈ Om2Facts.D Om2Facts.Zt4 :=
    fun j hj h0 h4 d hd => ng_D4 hj h0 h4 hd
  have hw1 : ∀ i < 27, witOK E1.T 27 BD.W1 i = true := allN_spec kW1
  exact ⟨bad_count enum0.1 enum0.2 wit0_all hD1 cnt01, bad_count enum1.1 enum1.2 hw1 hD1 cnt11,
    bad_count enum0.1 enum0.2 wit0_all hD4 cnt04, bad_count enum1.1 enum1.2 hw1 hD4 cnt14⟩

theorem cjAt_eq {S SI G : Nat} {s g : Equiv.Perm (Fin 480)} (hs : PR S s) (hsi : PR SI s⁻¹)
    (hg : PR G g) (q : Fin 480) : cjAt S SI G q = ((s * g * s⁻¹) q : Nat) := by
  unfold cjAt
  rw [pr_ip hsi, pr_ip hg, pr_ip hs]
  rfl

theorem xpw_eq {X : Nat} {x : Equiv.Perm (Fin 480)} (hx : PR X x) {k : Nat} (hk : k < 4)
    (q : Fin 480) : xpw X k q = ((x ^ k) q : Nat) := by
  unfold xpw
  interval_cases k
  · change (q : Nat) = ((x ^ 0) q : Nat)
    simp
  · change ip X q = ((x ^ 1) q : Nat)
    rw [pow_one, pr_ip hx]
  · change ip X (ip X q) = ((x ^ 2) q : Nat)
    rw [pr_ip hx, pr_ip hx, pow_two]
    rfl
  · change ip X (ip X (ip X q)) = ((x ^ 3) q : Nat)
    rw [pr_ip hx, pr_ip hx, pr_ip hx, pow_three]
    rfl

theorem twinFail_of {X Y S SI : Nat} {x y s : Equiv.Perm (Fin 480)} (hx : PR X x) (hy : PR Y y)
    (hs : PR S s) (hsi : PR SI s⁻¹) (h : TwinFailK X Y S SI) : Om2Facts.TwinFail x y s := by
  obtain ⟨⟨g, hg, hk⟩, a, ha, b, hb, p, hp, hne⟩ := h
  have mem : ∀ {G : Nat}, G ∈ [X, Y] → ∃ g' ∈ ({x, y} : Set (Equiv.Perm (Fin 480))), PR G g' := by
    intro G hG
    rcases List.mem_cons.1 hG with rfl | hG'
    · exact ⟨x, Set.mem_insert _ _, hx⟩
    · rw [List.mem_singleton] at hG'
      subst hG'
      exact ⟨y, Set.mem_insert_of_mem _ rfl, hy⟩
  obtain ⟨g', hg', pg⟩ := mem hg
  obtain ⟨a', ha', pa⟩ := mem ha
  obtain ⟨b', hb', pb⟩ := mem hb
  refine ⟨⟨g', hg', fun k hk4 => ⟨fun e => ?_, fun e => ?_⟩⟩, a', ha', b', hb', fun e => ?_⟩
  · obtain ⟨q, hq, hne⟩ := (hk k hk4).1
    apply hne
    rw [cjAt_eq hs hsi pg ⟨q, hq⟩, e, ← xpw_eq hx hk4 ⟨q, hq⟩]
  · obtain ⟨q, hq, hne⟩ := (hk k hk4).2
    apply hne
    rw [cjAt_eq hs hsi pg ⟨q, hq⟩, e, Equiv.Perm.mul_apply, ← pr_ip hy,
      ← xpw_eq hx hk4 ⟨q, hq⟩]
  · apply hne
    have e1 : ip a (cjAt S SI b p) = ((a' * (s * b' * s⁻¹)) ⟨p, hp⟩ : Nat) := by
      rw [cjAt_eq hs hsi pb ⟨p, hp⟩, pr_ip pa]
      rfl
    have e2 : cjAt S SI b (ip a p) = (((s * b' * s⁻¹) * a') ⟨p, hp⟩ : Nat) := by
      rw [pr_ipn pa hp, cjAt_eq hs hsi pb]
      rfl
    rw [e1, e2, e]

theorem q8_core {En SQ RT PRw Lg LgI : Nat → Nat} {nE nR nL tt : Nat} {withR : Bool}
    {τ x y : Equiv.Perm (Fin 480)} {S : Subgroup (Equiv.Perm (Fin 480))} {i j : Nat}
    (hτ : PR tt τ) (hττ : τ * τ = 1)
    (hsq : allN nE (sqOK En SQ RT tt nR) = true) (hrt : allN nR (rootOK En RT nE) = true)
    (hrow : ∀ a < nR, q8Row En RT PRw Lg LgI nL nR withR a = true)
    (hL : ∀ h < nL, ∃ s ∈ S, PR (Lg h) s ∧ PR (LgI h) s⁻¹)
    (hi : i < nE) (hj : j < nE) (hx : PR (En i) x) (hy : PR (En j) y)
    (hxx : x * x = τ) (hyy : y * y = τ) (hyx : y * x * y⁻¹ = x⁻¹) :
    (withR = true ∧ x ∈ Om2Facts.R ∧ y ∈ Om2Facts.R) ∨ ∃ s ∈ S, Om2Facts.TwinFail x y s := by
  have root : ∀ {i : Nat} {z : Equiv.Perm (Fin 480)}, i < nE → PR (En i) z → z * z = τ →
      ∃ a < nR, fld(RT a, 0, 8191) = i := by
    intro i z hi hz hzz
    rcases sqOK_sound (allN_spec hsq i hi) with h | ⟨p, hp, hne⟩
    · exact h
    · refine absurd ?_ hne
      rw [pr_ipn hz hp, pr_ip hz, pr_ipn hτ hp, ← hzz]
      rfl
  have inR : ∀ {a i : Nat} {z : Equiv.Perm (Fin 480)}, a < nR → fld(RT a, 0, 8191) = i →
      PR (En i) z → fld(RT a, 13, 1) = 1 → z ∈ Om2Facts.R := by
    intro a i z ha hai hz h1
    have e := (rootOK_sound (allN_spec hrt a ha)).2 h1
    rw [hai] at e
    rw [e] at hz
    obtain ⟨g, hg, hp⟩ := pr_KG _ (Nat.lt_succ_of_le (fld_le _ _ _))
    rw [pr_eq hz hp]
    exact hg
  obtain ⟨a, ha, hai⟩ := root hi hx hxx
  obtain ⟨b, hb, hbj⟩ := root hj hy hyy
  have hpf := q8Row_sound (hrow a ha) b hb
  rw [hai, hbj] at hpf
  rcases hpf with ⟨p, hp, hne⟩ | ⟨hw, ha1, hb1⟩ | ⟨h, hh, htw⟩
  · exfalso
    have h4 : x * x * x * x = 1 := by
      calc x * x * x * x = (x * x) * (x * x) := by group
        _ = 1 := by rw [hxx, hττ]
    have e : y * x = x * x * x * y := by
      rw [eq_inv_of_mul_eq_one_left h4]
      exact mul_inv_eq_iff_eq_mul.1 hyx
    apply hne
    rw [pr_ipn hx hp, pr_ip hy, pr_ipn hy hp, pr_ip hx, pr_ip hx, pr_ip hx]
    exact congrArg (fun z : Equiv.Perm (Fin 480) => ((z ⟨p, hp⟩ : Fin 480) : Nat)) e
  · exact Or.inl ⟨hw, inR ha hai hx ha1, inR hb hbj hy hb1⟩
  · obtain ⟨s, hs, hS, hSI⟩ := hL h hh
    exact Or.inr ⟨s, hs, twinFail_of hx hy hS hSI htw⟩

theorem q8T_fact : ∀ x ∈ Om2Facts.G wS0, ∀ y ∈ Om2Facts.G wS0, x * x = Om2Facts.t →
    y * y = Om2Facts.t → y * x * y⁻¹ = x⁻¹ →
    (x ∈ Om2Facts.R ∧ y ∈ Om2Facts.R) ∨ ∃ s ∈ Om2Facts.G wT, Om2Facts.TwinFail x y s := by
  intro x hx y hy hxx hyy hyx
  obtain ⟨i, hi, px⟩ := enum0.2 x hx
  obtain ⟨j, hj, py⟩ := enum0.2 y hy
  rcases q8_core pr_t t_sq kSq0 kRt0 q80_all lhT hi hj px py hxx hyy hyx with ⟨-, h⟩ | h
  · exact Or.inl h
  · exact Or.inr h

theorem q8C_fact : ∀ x ∈ Om2Facts.G wSc, ∀ y ∈ Om2Facts.G wSc, x * x = Om2Facts.tc →
    y * y = Om2Facts.tc → y * x * y⁻¹ = x⁻¹ → ∃ s ∈ Om2Facts.G wCc, Om2Facts.TwinFail x y s := by
  intro x hx y hy hxx hyy hyx
  obtain ⟨i, hi, px⟩ := enum2.2 x hx
  obtain ⟨j, hj, py⟩ := enum2.2 y hy
  rcases q8_core pr_tc tc_sq kSq2 kRt2 q82_all lcC hi hj px py hxx hyy hyx with ⟨h, -⟩ | h
  · exact absurd h Bool.false_ne_true
  · exact h

theorem orb_tree : ∀ m < 24, ∃ s ∈ Om2Facts.G wT,
    PR (BD.OA m) (s * Om2Facts.E wI0 * s⁻¹) ∧ PR (BD.OB m) (s * Om2Facts.E wJ0 * s⁻¹) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    obtain ⟨-, -, h0, h1⟩ := oNodeOK_sound (allN_spec kOrb m hm)
    by_cases hm0 : m = 0
    · subst hm0
      obtain ⟨e1, e2⟩ := h0 rfl
      refine ⟨1, one_mem _, ?_, ?_⟩
      · rw [e1]
        simpa using pr_i0
      · rw [e2]
        simpa using pr_j0
    · obtain ⟨par, hpar, k, hk, ea, eb⟩ := h1 hm0
      obtain ⟨s, hs, pa, pb⟩ := ih par hpar (by omega)
      refine ⟨Om2Facts.E (wT.getD k []) * s,
        mul_mem (E_mem_G (getD_mem (by rw [wT_len]; exact hk))) hs, ?_, ?_⟩
      · convert pr_conj (pr_TG hk) pa ea using 1
        group
      · convert pr_conj (pr_TG hk) pb eb using 1
        group

theorem orb2_fact : 24 ≤ {p : Equiv.Perm (Fin 480) × Equiv.Perm (Fin 480) |
    ∃ s ∈ Om2Facts.G wT, p = (s * Om2Facts.E wI0 * s⁻¹, s * Om2Facts.E wJ0 * s⁻¹)}.ncard := by
  choose! f hf using orb_tree
  have hnd : ((List.range 24).map fun m =>
      (f m * Om2Facts.E wI0 * (f m)⁻¹, f m * Om2Facts.E wJ0 * (f m)⁻¹)).Nodup := by
    refine List.Nodup.map_on ?_ List.nodup_range
    intro m hm m' hm' he
    rw [List.mem_range] at hm hm'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · rcases oDistOK_sound (allN_spec kOD m hm) m' hm' h with d | d
      · exact pr_ne (hf m hm).2.1 (hf m' hm').2.1 d (congrArg Prod.fst he)
      · exact pr_ne (hf m hm).2.2 (hf m' hm').2.2 d (congrArg Prod.snd he)
    · rcases oDistOK_sound (allN_spec kOD m' hm') m hm h with d | d
      · exact pr_ne (hf m' hm').2.1 (hf m hm).2.1 d (congrArg Prod.fst he.symm)
      · exact pr_ne (hf m' hm').2.2 (hf m hm).2.2 d (congrArg Prod.snd he.symm)
  refine le_trans ?_ (hnd.length_le_ncard (Set.toFinite _) ?_)
  · simp
  · intro p hp
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hp
    exact ⟨f m, (hf m (List.mem_range.1 hm)).1, rfl⟩

theorem pr_SG : ∀ m < 8, ∃ u ∈ Om2Facts.S8, PR (BD.SG m) u := by
  intro m hm
  obtain ⟨-, h0, h1⟩ := sgOK_sound (allN_spec kSG m hm)
  have hvE : ∃ v ∈ [wI0, wJ0], PR (EL.G (1 + m % 2)) (Om2Facts.E v) := by
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · rw [h]
      exact ⟨wI0, List.mem_cons_self .., pr_i0⟩
    · rw [h]
      exact ⟨wJ0, by simp, pr_j0⟩
  obtain ⟨v, hv, pv⟩ := hvE
  by_cases hf : m / 2 = 0
  · rw [h0 hf]
    exact ⟨Om2Facts.E v, ⟨[], List.mem_cons_self .., v, hv, by rw [E_nil]; group⟩, pv⟩
  · obtain ⟨e, -, -⟩ := h1 hf
    have hk : m / 2 - 1 < 3 := by omega
    exact ⟨_, ⟨wFuse0.getD (m / 2 - 1) [],
      List.mem_cons_of_mem _ (getD_mem (by rw [wFuse0_len]; exact hk)), v, hv, rfl⟩,
      pr_conj (pr_FU hk) pv e⟩

theorem cen8_fact :
    Nat.card ↥(Om2Facts.G wCR ⊓ Subgroup.centralizer Om2Facts.S8) ≤ 8 := by
  have e : Nat.card ↥(Om2Facts.G wCR ⊓ Subgroup.centralizer Om2Facts.S8) =
      ((Om2Facts.G wCR ⊓ Subgroup.centralizer Om2Facts.S8 : Subgroup (Equiv.Perm (Fin 480))) :
        Set (Equiv.Perm (Fin 480))).ncard := Nat.card_coe_set_eq _
  rw [e]
  refine (ncard_le_of_pr (T := E4.T)
    (L := (List.range 4608).filter (fun i => Nat.beq fld(BD.CR i, 0, 1) 1))
    fun u hu => ?_).trans cntCen
  have hu' := Subgroup.mem_inf.1 hu
  obtain ⟨i, hi, hp⟩ := enum4.2 u hu'.1
  refine ⟨i, List.mem_filter.2 ⟨List.mem_range.2 hi, ?_⟩, hp⟩
  rcases (crOK_sound (allN_spec kCR i hi)).1 with h | ⟨p, hp', hne⟩
  · rw [h]
    rfl
  · exfalso
    obtain ⟨v, hvS, pv⟩ := pr_SG _ (Nat.lt_succ_of_le (fld_le _ _ _))
    exact pr_ne_comm hp pv hp' hne (Subgroup.mem_centralizer_iff.1 hu'.2 v hvS).symm

theorem pair_fact :
    (∀ u ∈ Om2Facts.G wCR, u * u = 1 → (∃ g ∈ Om2Facts.Yg, u = g * Om2Facts.t * g⁻¹) →
      u ∈ Om2Facts.Zt4) ∧
    ∀ w ∈ wFuse0, ∀ a ∈ [wI0, wJ0], ∀ b ∈ [wI0, wJ0],
      Commute (Om2Facts.E w * Om2Facts.E a * (Om2Facts.E w)⁻¹) (Om2Facts.E b) := by
  refine ⟨fun u hu huu ⟨g, hg, hug⟩ => ?_, fun w hw a ha b hb => ?_⟩
  · obtain ⟨i, hi, hp⟩ := enum4.2 u hu
    rcases (crOK_sound (allN_spec kCR i hi)).2 with ⟨q, hq, hne⟩ | ⟨k, hk, e⟩ | ⟨hne, hcomm⟩
    · exfalso
      apply hne
      rw [pr_ipn hp hq, pr_ip hp]
      exact congrArg (fun z : Equiv.Perm (Fin 480) => ((z ⟨q, hq⟩ : Fin 480) : Nat)) huu
    · rw [e] at hp
      unfold Om2Facts.Zt4
      interval_cases k
      · exact Or.inl (pr_eq hp pr_ZT0)
      · exact Or.inr (Or.inl (pr_eq hp (pr_ZTk (k := 1) (by norm_num) (by norm_num))))
      · exact Or.inr (Or.inr (Or.inl (pr_eq hp (pr_ZTk (k := 2) (by norm_num) (by norm_num)))))
      · exact Or.inr (Or.inr (Or.inr (pr_eq hp (pr_ZTk (k := 3) (by norm_num) (by norm_num)))))
    · exfalso
      have hc : ∀ l < 8, u * Om2Facts.E [l] = Om2Facts.E [l] * u := fun l hl =>
        pr_comm hp (pr_L (by omega)) (hcomm l hl)
      have hY : Om2Facts.Yg ≤ Subgroup.centralizer {u} := by
        unfold Om2Facts.Yg Om2Facts.G
        rw [Subgroup.closure_le]
        rintro _ ⟨w, hw, rfl⟩
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hw
        exact Subgroup.mem_centralizer_iff.2 fun h hh => by
          rw [Set.mem_singleton_iff.1 hh]
          exact hc l (List.mem_range.1 hl)
      have hcg : u * g = g * u := Subgroup.mem_centralizer_iff.1 (hY hg) u rfl
      have h1 : u * g = g * Om2Facts.t := by
        rw [hug]
        group
      exact pr_ne hp pr_t hne (mul_left_cancel (hcg.symm.trans h1))
  · obtain ⟨f, hf, rfl⟩ := mem_getD hw
    rw [wFuse0_len] at hf
    have key : ∀ v < 2, ∀ c ∈ [wI0, wJ0], Commute
        (Om2Facts.E (wFuse0.getD f []) * Om2Facts.E (elW.getD (1 + v) []) *
          (Om2Facts.E (wFuse0.getD f []))⁻¹) (Om2Facts.E c) := by
      intro v hv c hc
      have hm8 : 2 * (f + 1) + v < 8 := by omega
      obtain ⟨-, -, h1⟩ := sgOK_sound (allN_spec kSG _ hm8)
      have ed : (2 * (f + 1) + v) / 2 = f + 1 := by omega
      have em : (2 * (f + 1) + v) % 2 = v := by omega
      rw [ed, em, Nat.add_sub_cancel] at h1
      obtain ⟨e, c1, c2⟩ := h1 (by omega)
      have hS := pr_conj (pr_FU hf) (pr_EL (k := 1 + v) (by omega)) e
      rcases List.mem_cons.1 hc with rfl | hc'
      · exact pr_comm hS pr_i0 c1
      · rw [List.mem_singleton] at hc'
        subst hc'
        exact pr_comm hS pr_j0 c2
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact key 0 (by norm_num) b hb
    · rw [List.mem_singleton] at ha'
      subst ha'
      exact key 1 (by norm_num) b hb

open Certificates in
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data in
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check in
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Facts in
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711 (OmGen.BadElt) in
theorem certB :
    (∀ x ∈ G wS0, ∀ y ∈ G wS0, x * x = t → y * y = t → y * x * y⁻¹ = x⁻¹ →
      (x ∈ R ∧ y ∈ R) ∨ ∃ s ∈ G wT, TwinFail x y s) ∧
    (∀ x ∈ G wSc, ∀ y ∈ G wSc, x * x = tc → y * y = tc → y * x * y⁻¹ = x⁻¹ →
      ∃ s ∈ G wCc, TwinFail x y s) ∧
    24 ≤ {p : Equiv.Perm (Fin 480) × Equiv.Perm (Fin 480) |
      ∃ s ∈ G wT, p = (s * E wI0 * s⁻¹, s * E wJ0 * s⁻¹)}.ncard ∧
    Nat.card ↥(G wCR ⊓ Subgroup.centralizer S8) ≤ 8 ∧
    ({x | x ∈ G wS0 ∧ ¬ OmGen.BadElt (G wT) R (D Zt1) x}.ncard ≤ 8 ∧
      {x | x ∈ G wP3 ∧ ¬ OmGen.BadElt (G wT) R (D Zt1) x}.ncard ≤ 1 ∧
      {x | x ∈ G wS0 ∧ ¬ OmGen.BadElt (G wT) R (D Zt4) x}.ncard ≤ 1184 ∧
      {x | x ∈ G wP3 ∧ ¬ OmGen.BadElt (G wT) R (D Zt4) x}.ncard ≤ 19) ∧
    (∀ u ∈ G wCR, u * u = 1 → (∃ g ∈ Yg, u = g * t * g⁻¹) → u ∈ Zt4) ∧
      ∀ w ∈ wFuse0, ∀ a ∈ [wI0, wJ0], ∀ b ∈ [wI0, wJ0], Commute (E w * E a * (E w)⁻¹) (E b) :=
  ⟨q8T_fact, q8C_fact, orb2_fact, cen8_fact, bad_fact, pair_fact⟩

end CertificateChecks.KernelOm2

end
