module

public import Certificates.Kernel.Sp6Cover.Small
public import Certificates.Kernel.Sp6Cover.Class
public import Certificates.Kernel.Sp6Cover.Group
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverSpec
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.Kernel.Spor.RawCard
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import CFSG.Certificates.Kernel.Spor.BaseMaskGlue
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.Spor.PEnumSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables
public import CFSG.Sporadic.Schreier.ClassSpec
public import CFSG.Sporadic.Schreier.ClassSum
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.Certificates.Kernel.Spor.BaseMaskSound
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSp6Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.MulH CFSG.Monster.B.Co2
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverData
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6Cover

open CFSG.KS.Raw.Orb (PRep prep_pcomp prep_pidn prep_of_rep rep_unpack prep_PS isInvA_unpack)

theorem kb_and (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem kb_if (c t e : Bool) : bIf(c, t, e) = if c = true then t else e := by cases c <;> rfl

theorem kn_if (c : Bool) (a b : Nat) : nIf(c, a, b) = if c = true then a else b := by
  cases c <;> rfl

theorem kn_strict (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem h32 : (240 : ℕ) < 2 ^ 32 := by norm_num

theorem h24 : (240 : ℕ) < 16777216 := by norm_num

theorem hw8 : (240 : ℕ) + 1 < 2 ^ 8 := by norm_num

theorem prep_eq {P : ℕ} {g h : Equiv.Perm (Fin 240)} (hg : PRep 240 8 P g) (hh : PRep 240 8 P h) :
    g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem prep_idP : PRep 240 8 idP 1 := prep_pidn h24 hw8

theorem prep_pc {P Q : ℕ} {g h : Equiv.Perm (Fin 240)} (hP : PRep 240 8 P g)
    (hQ : PRep 240 8 Q h) : PRep 240 8 (pc P Q) (g * h) :=
  prep_pcomp h32 hP hQ

theorem cn_pc {P Q : ℕ} (hP : cnK P = true) (hQ : cnK Q = true) : cnK (pc P Q) = true :=
  CFSG.KC.BfsPin.canonK_pcomp hP hQ

theorem ne_of_prep {P Q : ℕ} {g h : Equiv.Perm (Fin 240)} (hP : cnK P = true)
    (hQ : cnK Q = true) (hg : PRep 240 8 P g) (hh : PRep 240 8 Q h) (hne : P ≠ Q) : g ≠ h := by
  intro e
  apply hne
  refine CFSG.KS.MulH.unpack_injH hP hQ ?_
  unfold CFSG.KS.Raw.unpack
  congr 1
  funext i
  rw [hg i, hh i, e]

theorem ne_of_neK {p q : ℕ} (h : neK p q = true) : p ≠ q := by
  intro e
  subst e
  unfold neK at h
  rw [kb_if, Nat.beq_refl] at h
  simp at h

theorem comm_of {P Q : ℕ} {g h : Equiv.Perm (Fin 240)} (hP : PRep 240 8 P g)
    (hQ : PRep 240 8 Q h) (hc : commK P Q = true) : g * h = h * g := by
  have e : pc P Q = pc Q P := Nat.eq_of_beq_eq_true hc
  exact prep_eq (prep_pc hP hQ) (by rw [e]; exact prep_pc hQ hP)

theorem not_comm_of {P Q : ℕ} {g h : Equiv.Perm (Fin 240)} (hPc : cnK P = true)
    (hQc : cnK Q = true) (hP : PRep 240 8 P g) (hQ : PRep 240 8 Q h)
    (hc : bIf(commK P Q, false, true) = true) : g * h ≠ h * g := by
  have hne : pc P Q ≠ pc Q P := by
    intro e
    rw [kb_if] at hc
    unfold commK at hc
    rw [e, Nat.beq_refl] at hc
    simp at hc
  exact ne_of_prep (cn_pc hPc hQc) (cn_pc hQc hPc) (prep_pc hP hQ) (prep_pc hQ hP) hne

theorem wfoldK_cons (S : ℕ → ℕ) (l : ℕ) (wd : List ℕ) (acc : ℕ) :
    wfoldK 240 8 (mask 8) S (l :: wd) acc = wfoldK 240 8 (mask 8) S wd (pc acc (S l)) := by
  unfold wfoldK
  exact kn_strict _ _

theorem prep_wfoldK {S : ℕ → ℕ} {f : ℕ → Equiv.Perm (Fin 240)} :
    ∀ (wd : List ℕ) {acc : ℕ} {g : Equiv.Perm (Fin 240)},
      (∀ l ∈ wd, PRep 240 8 (S l) (f l)) → PRep 240 8 acc g →
      PRep 240 8 (wfoldK 240 8 (mask 8) S wd acc) (g * (wd.map f).prod)
  | [], acc, g, _, h => by
    have e : wfoldK 240 8 (mask 8) S [] acc = acc := rfl
    rw [e, List.map_nil, List.prod_nil, mul_one]
    exact h
  | l :: wd, acc, g, hS, h => by
    rw [wfoldK_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    exact prep_wfoldK wd (fun l' hl' => hS l' (List.mem_cons_of_mem _ hl'))
      (prep_pc h (hS l (by simp)))

@[expose] def Inj (P : ℕ) : Prop :=
  ∀ i < 240, ∀ j < 240, pg 8 (mask 8) P i = pg 8 (mask 8) P j → i = j

theorem pg_pc {P Q i : ℕ} (hi : i < 240) :
    pg 8 (mask 8) (pc P Q) i = pg 8 (mask 8) P (pg 8 (mask 8) Q i) :=
  CFSG.KS.PF.pg_pcomp h32 hi

theorem pg_idP {i : ℕ} (hi : i < 240) : pg 8 (mask 8) idP i = i := CFSG.KS.PF.pg_pidn h24 hw8 hi

theorem inj_idP : Inj idP := fun i hi j hj e => by
  rwa [pg_idP hi, pg_idP hj] at e

theorem inj_of_sq {P Q : ℕ} (h : pc P P = Q) (hQ : Inj Q) : Inj P := fun i hi j hj e =>
  hQ i hi j hj (by rw [← h, pg_pc hi, pg_pc hj, e])

theorem prep_inj {P : ℕ} (hc : cnK P = true) (hinj : Inj P) :
    PRep 240 8 P (permOfArr 240 (unpack 240 8 P)) := by
  have hr := range_of_canonK hc
  have hcond : (∀ i < 240, (unpack 240 8 P)[i]! < 240) ∧
      ∀ i < 240, ∀ j < 240, (unpack 240 8 P)[i]! = (unpack 240 8 P)[j]! → i = j := by
    refine ⟨fun i hi => ?_, fun i hi j hj e => ?_⟩
    · rw [CFSG.KS.Raw.Orb.unpack_get hi]
      exact Nat.le_of_ble_eq_true (CFSG.KS.allN_spec hr i hi)
    · rw [CFSG.KS.Raw.Orb.unpack_get hi, CFSG.KS.Raw.Orb.unpack_get hj] at e
      exact hinj i hi j hj e
  intro x
  rw [← CFSG.KS.Raw.Orb.unpack_get x.2, permOfArr, dif_pos hcond]
  rfl

theorem ybinds : Binds 240 8 YC.S 12 4 YC.BP yS yBaseA := by
  obtain ⟨h1, h2, h3, h4⟩ := ybind
  exact ⟨by norm_num, by norm_num, by norm_num, h1, h2, h3, h4⟩

theorem yW_eq : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 12 yWD = yW := by decide +kernel

theorem y_chain : CFSG.Certificates.Native.rawChainOK 240 (yS.extract 0 3) yS
    (yBase.map Fin.val).toArray yW 1 = true := by
  rw [← yW_eq]
  exact rawChainK_sound (NS := 4) (CH := 60) (chunks := 1) ybinds YC.head YC.hl (by norm_num) YC.hs

theorem card_Y : Nat.card ySub = 2903040 := by
  have hs : CFSG.Certificates.Native.rawOrbitSizes 240 yS (yBase.map Fin.val).toArray =
      [240, 126, 12, 8] :=
    (rawOrbitSizesK_sound ybinds yperm YC.hl).trans ysizes
  rw [ySub, CFSG.ComponentClassification.J2Cover.ofArrays_card (by norm_num) y_chain, hs]
  rfl

theorem mem_Y {P : ℕ} {g : Equiv.Perm (Fin 240)} (hc : cnK P = true) (hg : PRep 240 8 P g)
    (h : siftY P = true) : g ∈ ySub :=
  (CFSG.ComponentClassification.J2Cover.ofArrays_mem_iff (by norm_num) y_chain
    (rep_unpack hg)).1 (siftK_sound ybinds yperm YC.hl rfl (range_of_canonK hc) h)

theorem dP_mem' {k : ℕ} (hk : k < 3) : dP k ∈ ySub := by
  rw [ySub, CFSG.ComponentClassification.J2Cover.ofArrays_originalSubgroup]
  exact Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem prep_yS {j : ℕ} (hj : j < 12) : PRep 240 8 (YC.S j) (permOfArr 240 yS[j]!) ∧
    PRep 240 8 (YC.SI j) (permOfArr 240 yS[j]!)⁻¹ :=
  prep_PS ybinds yperm hj

theorem rep_d {k : ℕ} (hk : k < 3) : Rep 240 yS[k]! (dP k) := by
  have := rep_unpack (prep_yS (j := k) (by omega)).1
  rwa [← ybind.2.1 k (by omega)] at this

theorem cbinds : Binds 240 8 CC.S 6 3 CC.BP cS cBase := by
  obtain ⟨h1, h2, h3, h4⟩ := cbind
  exact ⟨by norm_num, by norm_num, by norm_num, h1, h2, h3, h4⟩

noncomputable abbrev cP (j : ℕ) : Equiv.Perm (Fin 240) := permOfArr 240 cS[j]!

theorem prep_cS {j : ℕ} (hj : j < 6) : PRep 240 8 (CC.S j) (cP j) ∧
    PRep 240 8 (CC.SI j) (cP j)⁻¹ :=
  prep_PS cbinds cperm hj

theorem cA_size' : cA.size = 3 := rfl

theorem cS_get {j : ℕ} (hj : j < 3) : cS[j]! = cA[j]! := by
  unfold cS
  rw [getElem!_pos (cA ++ cX) j (by rw [Array.size_append, cA_size']; omega),
    getElem!_pos cA j (by rw [cA_size']; exact hj), Array.getElem_append_left]

theorem canon_parts : (∀ k < 32, cnK (E k) = true) ∧ cnK idP = true ∧
    ∀ k < 3, cnK (CC.S k) = true ∧ cnK (CC.SI k) = true ∧ cnK (YC.S k) = true ∧
      cnK (YC.SI k) = true := by
  have h := canon
  simp only [kb_and, Bool.and_eq_true] at h
  obtain ⟨h1, h2, -, -, h5⟩ := h
  refine ⟨CFSG.KS.allN_spec h1, h2, fun k hk => ?_⟩
  have := CFSG.KS.allN_spec h5 k hk
  simp only [Bool.and_eq_true] at this
  exact this

theorem cnE {k : ℕ} (hk : k < 32) : cnK (E k) = true := canon_parts.1 k hk

theorem rRel_parts : pc (E 0) (E 0) = idP ∧ E 0 ≠ idP ∧ pc (E 1) (E 1) = E 0 ∧
    pc (E 2) (E 2) = E 0 ∧ pc (pc (E 2) (E 1)) (pc (E 0) (E 2)) = pc (E 0) (E 1) := by
  have h := rRel
  simp only [kb_and, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h1, ne_of_neK h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5⟩

theorem inj_E0 : Inj (E 0) := inj_of_sq rRel_parts.1 inj_idP

theorem prep_t : PRep 240 8 (E 0) tP := by
  have := prep_inj (cnE (k := 0) (by norm_num)) inj_E0
  rwa [← ebind.1] at this

theorem prep_i : PRep 240 8 (E 1) iP := by
  have := prep_inj (cnE (k := 1) (by norm_num)) (inj_of_sq rRel_parts.2.2.1 inj_E0)
  rwa [← ebind.2.1] at this

theorem prep_j : PRep 240 8 (E 2) jP := by
  have := prep_inj (cnE (k := 2) (by norm_num)) (inj_of_sq rRel_parts.2.2.2.1 inj_E0)
  rwa [← ebind.2.2.1] at this

theorem invs_parts : (∀ k < 3, CFSG.KS.Prim.invEqK 240 8 (mask 8) (240 * 8) (E (3 + k))
    (E (6 + k)) = true) ∧ CFSG.KS.Prim.invEqK 240 8 (mask 8) (240 * 8) (E 11) (E 12) = true := by
  have h := invs
  simp only [kb_and, Bool.and_eq_true] at h
  exact ⟨CFSG.KS.allN_spec h.1, h.2⟩

theorem prep_g {k : ℕ} (hk : k < 3) : PRep 240 8 (E (3 + k)) (gP k) ∧
    PRep 240 8 (E (6 + k)) (gP k)⁻¹ := by
  have hr := rep_permOfArr (isInvA_unpack (n := 240) (w := 8) (invs_parts.1 k hk))
  have e : gP k = permOfArr 240 (unpack 240 8 (E (3 + k))) :=
    congrArg (permOfArr 240) (ebind.2.2.2.2 k hk)
  rw [e]
  exact ⟨prep_of_rep hr.1, prep_of_rep hr.2⟩

theorem sifts_parts : (∀ k < 6, siftY (E k) = true) ∧ ∀ k < 3, siftY (CC.S k) = true := by
  have h := sifts
  simp only [kb_and, Bool.and_eq_true] at h
  exact ⟨CFSG.KS.allN_spec h.1, CFSG.KS.allN_spec h.2⟩

theorem t_mem : tP ∈ ySub := mem_Y (cnE (k := 0) (by norm_num)) prep_t (sifts_parts.1 0 (by norm_num))

theorem i_mem : iP ∈ ySub := mem_Y (cnE (k := 1) (by norm_num)) prep_i (sifts_parts.1 1 (by norm_num))

theorem j_mem : jP ∈ ySub := mem_Y (cnE (k := 2) (by norm_num)) prep_j (sifts_parts.1 2 (by norm_num))

theorem g_mem {k : ℕ} (hk : k < 3) : gP k ∈ ySub :=
  mem_Y (cnE (k := 3 + k) (by omega)) (prep_g hk).1 (sifts_parts.1 (3 + k) (by omega))

theorem d_inv {k : ℕ} (hk : k < 3) : (dP k)⁻¹ = tP * (gP k * tP * (gP k)⁻¹) := by
  have h := Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec dRel k hk)
  exact prep_eq (prep_yS (j := k) (by omega)).2
    (by rw [h]; exact prep_pc prep_t (prep_pc (prep_pc (prep_g hk).1 prep_t) (prep_g hk).2))

theorem t_mul_t : tP * tP = 1 :=
  prep_eq (prep_pc prep_t prep_t) (by rw [rRel_parts.1]; exact prep_idP)

theorem t_ne_one : tP ≠ 1 :=
  ne_of_prep (cnE (k := 0) (by norm_num)) canon_parts.2.1 prep_t prep_idP rRel_parts.2.1

theorem i_mul_i : iP * iP = tP :=
  prep_eq (prep_pc prep_i prep_i) (by rw [rRel_parts.2.2.1]; exact prep_t)

theorem j_mul_j : jP * jP = tP :=
  prep_eq (prep_pc prep_j prep_j) (by rw [rRel_parts.2.2.2.1]; exact prep_t)

theorem j_i_j : jP * iP * jP⁻¹ = iP⁻¹ := by
  have h1 : tP * jP = jP⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_assoc, j_mul_j, t_mul_t])
  have h2 : tP * iP = iP⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_assoc, i_mul_i, t_mul_t])
  have h3 : jP * iP * (tP * jP) = tP * iP :=
    prep_eq (prep_pc (prep_pc prep_j prep_i) (prep_pc prep_t prep_j))
      (by rw [rRel_parts.2.2.2.2]; exact prep_pc prep_t prep_i)
  rwa [h1, h2] at h3

theorem rep_tA : Rep 240 tA tP := by
  have := rep_unpack prep_t
  rwa [← ebind.1] at this

section Class

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem threp_of_prep {P : ℕ} {g : Equiv.Perm (Fin 240)} (hc : cnK P = true)
    (h : PRep 240 8 P g) : CFSG.Sporadic.Th.Rep 240 (tabT (unpack 240 8 P)) g := by
  intro i hi
  rw [CFSG.KS.MulH.ap_tabT _ (CFSG.KS.MulH.unpack_lt hc), CFSG.KS.Raw.Orb.unpack_get hi,
    h ⟨i, hi⟩, CFSG.Sporadic.Th.idx_of_lt _ hi]
  rfl

theorem le_ncard_conjClass_of_closureOK {H : Subgroup (Equiv.Perm (Fin 240))}
    {GT GI : Array Table} {gg : ℕ → Equiv.Perm (Fin 240)}
    (hg : ∀ l < GT.size, CFSG.Sporadic.Th.Rep 240 GT[l]! (gg l) ∧
      CFSG.Sporadic.Th.Rep 240 GI[l]! (gg l)⁻¹ ∧ gg l ∈ H)
    {T : Table} {b : Equiv.Perm (Fin 240)} (hT : CFSG.Sporadic.Th.Rep 240 T b) {m : ℕ}
    {c : Array Table × Array ℕ × Array ℕ}
    (h : (conjTreeOK 240 GT GI T c.1 c.2.1 c.2.2 && hkeysDistinct 240 c.1.toList &&
      decide (m ≤ c.1.size)) = true) :
    m ≤ (CFSG.Sporadic.Schreier.conjClass H b).ncard := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨htree, hdist⟩, hsize⟩ := h
  have hent := CFSG.Sporadic.Schreier.conjTreeOK_spec H hg hT htree
  have hrepL : ∀ U ∈ c.1.toList, ∃ d ∈ H, CFSG.Sporadic.Th.Rep 240 U (d * b * d⁻¹) := by
    intro U hU
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hU
    rw [Array.length_toList] at hk
    obtain ⟨d, hd, hrep⟩ := hent k hk
    refine ⟨d, hd, ?_⟩
    rw [Array.getElem_toList]
    rwa [getElem!_pos c.1 k hk] at hrep
  set E := c.1.toList.map (CFSG.Sporadic.Schreier.tablePerm 240)
  have hF : List.Forall₂ (CFSG.Sporadic.Th.Rep 240) c.1.toList E := by
    rw [List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun U hU => ?_
    obtain ⟨d, -, hrep⟩ := hrepL U hU
    rw [CFSG.Sporadic.Schreier.tablePerm_eq hrep]
    exact hrep
  have hnodup : E.Nodup := CFSG.Sporadic.SmallOddCore.nodup_of_hkeysDistinct hF hdist
  have hEcls : ∀ y ∈ E, y ∈ CFSG.Sporadic.Schreier.conjClass H b := by
    intro y hy
    obtain ⟨U, hU, rfl⟩ := List.mem_map.1 hy
    obtain ⟨d, hd, hrep⟩ := hrepL U hU
    exact ⟨d, hd, CFSG.Sporadic.Schreier.tablePerm_eq hrep⟩
  have hlen : E.length = c.1.size := by simp [E]
  have hfin : Finite H := Subtype.finite
  calc m ≤ c.1.size := hsize
    _ = E.toFinset.card := by rw [List.toFinset_card_of_nodup hnodup, hlen]
    _ = (E.toFinset : Set (Equiv.Perm (Fin 240))).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (CFSG.Sporadic.Schreier.conjClass H b).ncard :=
      Set.ncard_le_ncard (fun y hy => hEcls y (List.mem_toFinset.1 hy))
        (CFSG.Sporadic.Schreier.conjClass_finite H b)

noncomputable abbrev tcG : Array Table :=
  Array.ofFn (n := 3) fun j => tabT (unpack 240 8 (TC.G j.val))

noncomputable abbrev tcGI : Array Table :=
  Array.ofFn (n := 3) fun j => tabT (unpack 240 8 (TC.GI j.val))

theorem tcGens_parts : (∀ j < 3, TC.G j = YC.S j ∧ TC.GI j = YC.SI j) ∧
    (∀ j < 3, cnK (TC.G j) = true ∧ cnK (TC.GI j) = true) ∧ cnK TC.R = true ∧
    szOK 240 8 = true := by
  have h := tcGens
  simp only [kb_and, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun j hj => ?_, fun j hj => ?_, h3, h4⟩
  · have := CFSG.KS.allN_spec h1 j hj
    simp only [Bool.and_eq_true] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩
  · have := CFSG.KS.allN_spec h2 j hj
    simp only [Bool.and_eq_true] at this
    exact this

theorem tcG_get {j : ℕ} (hj : j < 3) : tcG[j]! = tabT (unpack 240 8 (TC.G j)) := by
  rw [getElem!_pos tcG j (by simpa using hj)]
  simp [tcG]

theorem tcGI_get {j : ℕ} (hj : j < 3) : tcGI[j]! = tabT (unpack 240 8 (TC.GI j)) := by
  rw [getElem!_pos tcGI j (by simpa using hj)]
  simp [tcGI]

theorem tabs_G : TabsOK 240 8 3 TC.G tcG :=
  ⟨by simp [tcG], fun j hj => ⟨tcG_get hj, (tcGens_parts.2.1 j hj).1⟩⟩

theorem tabs_GI : TabsOK 240 8 3 TC.GI tcGI :=
  ⟨by simp [tcGI], fun j hj => ⟨tcGI_get hj, (tcGens_parts.2.1 j hj).2⟩⟩

theorem tc_cnt : TC.cnt = 630 := Nat.eq_of_beq_eq_true tcCnt

theorem tc_rec : conjTreeOK 240 tcG tcGI (tabT (unpack 240 8 TC.R))
      (hRec 240 8 TC.cnt TC.T TC.PL).1 (hRec 240 8 TC.cnt TC.T TC.PL).2.1
      (hRec 240 8 TC.cnt TC.T TC.PL).2.2 = true ∧
    hkeysDistinct 240 (hRec 240 8 TC.cnt TC.T TC.PL).1.toList = true := by
  have hcnt := tc_cnt
  have hp : ∀ i < TC.cnt, CFSG.KS.PEnum.penumPtK 240 8 (mask 8) (240 * 8) true TC.G TC.GI 3 TC.cnt TC.T TC.PL
      TC.POS TC.SRT TC.SRI i = true := by
    intro i hi
    rcases Nat.lt_or_ge i 210 with h1 | h1
    · exact CFSG.KS.BaseMask.penumSl_spec tcE0 (Nat.zero_le _) (by omega) hi
    · rcases Nat.lt_or_ge i 420 with h2 | h2
      · exact CFSG.KS.BaseMask.penumSl_spec tcE1 h1 (by omega) hi
      · exact CFSG.KS.BaseMask.penumSl_spec tcE2 h2 (by omega) hi
  have hs : ∀ i < TC.cnt, hsortPtK 240 8 (mask 8) TC.cnt TC.T TC.HS TC.HSI i = true :=
    fun i hi => slK_spec tcH i (Nat.zero_le _) (by omega) hi
  obtain ⟨-, h2, h3⟩ := conjH_sound tcGens_parts.2.2.2 tabs_G tabs_GI rfl tcHd hp hs
  exact ⟨h2, h3⟩

theorem class_le : 630 ≤ (CFSG.Sporadic.Schreier.conjClass ySub tP).ncard := by
  have hR : PRep 240 8 TC.R tP := by
    have := rep_tA
    rw [tcRoot] at this
    exact prep_of_rep this
  refine le_ncard_conjClass_of_closureOK (H := ySub) (GT := tcG) (GI := tcGI) (gg := dP)
    (fun l hl => ?_) (threp_of_prep tcGens_parts.2.2.1 hR)
    (c := hRec 240 8 TC.cnt TC.T TC.PL) ?_
  · have hl' : l < 3 := by simpa using hl
    obtain ⟨e1, e2⟩ := tcGens_parts.1 l hl'
    refine ⟨?_, ?_, dP_mem' hl'⟩
    · rw [tcG_get hl']
      exact threp_of_prep (tcGens_parts.2.1 l hl').1 (by rw [e1]; exact (prep_yS (by omega)).1)
    · rw [tcGI_get hl']
      exact threp_of_prep (tcGens_parts.2.1 l hl').2 (by rw [e2]; exact (prep_yS (by omega)).2)
  · obtain ⟨h1, h2⟩ := tc_rec
    rw [h1, h2]
    simp [hRec, tc_cnt]

end Class

theorem card_CSub_le : Nat.card CSub ≤ 4608 := by
  have hos := CFSG.Sporadic.Schreier.ncard_conjClass_mul_card ySub tP
  rw [card_Y] at hos
  have h630 := class_le
  by_contra hlt
  rw [not_le] at hlt
  have : 630 * 4609 ≤ (CFSG.Sporadic.Schreier.conjClass ySub tP).ncard *
      Nat.card (CFSG.Sporadic.Schreier.centralizerIn ySub tP) := Nat.mul_le_mul h630 hlt
  omega

theorem cP_mem_C {j : ℕ} (hj : j < 3) : cP j ∈ CSub := by
  have hp := (prep_cS (j := j) (by omega)).1
  refine Subgroup.mem_inf.2 ⟨mem_Y (canon_parts.2.2 j hj).1 hp (sifts_parts.2 j hj), ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact comm_of hp prep_t (CFSG.KS.allN_spec cCent j hj)

noncomputable abbrev C0 : Subgroup (Equiv.Perm (Fin 240)) :=
  Subgroup.closure (Set.range fun j : Fin 3 => permOfArr 240 cS[j.val]!)

theorem C0_le : C0 ≤ CSub := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact cP_mem_C j.2

theorem cBaseL_eq : (([0, 1, 4] : List (Fin 240)).map Fin.val).toArray = cBase := by
  decide +kernel

theorem card_C0 : Nat.card C0 = 4608 := by
  have hsz : CFSG.Certificates.Native.rawOrbitSizes 240 cS cBase = [192, 12, 2] :=
    (rawOrbitSizesK_sound cbinds cperm CC.hl).trans csizes
  have hcard : Nat.card (Subgroup.closure (Set.range fun j : Fin 3 => permOfArr 240 cS[j.val]!)) ≤
      (CFSG.Certificates.Native.rawOrbitSizes 240 cS cBase).prod := by
    rw [hsz]
    exact (Subgroup.card_le_of_le C0_le).trans card_CSub_le
  have hch := rawChainK_of_card 1 cbinds CC.head CC.hl hcard
  rw [← cBaseL_eq] at hch
  have hc := CFSG.ComponentClassification.J2Cover.ofArrays_card (hn := (by norm_num : 1 ≤ 240))
    (hk := (by rw [cbind.1]; norm_num : 3 ≤ cS.size))
    (hb := (by decide : ([0, 1, 4] : List (Fin 240)).Nodup)) (by norm_num) hch
  rw [CFSG.ComponentClassification.J2Cover.ofArrays_originalSubgroup, cBaseL_eq, hsz] at hc
  have hset : {g | ∃ i < 3, permOfArr 240 cS[i]! = g} =
      Set.range fun j : Fin 3 => permOfArr 240 cS[j.val]! := by
    ext g
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j.val, j.2, rfl⟩
  rw [hset] at hc
  rw [hc]
  rfl

theorem C0_eq : C0 = CSub :=
  Subgroup.eq_of_le_of_card_ge C0_le (by rw [card_C0]; exact card_CSub_le)

theorem card_C : Nat.card CSub = 4608 := by rw [← C0_eq, card_C0]

noncomputable def cw (wd : List ℕ) : Equiv.Perm (Fin 240) := (wd.map fun l => cP (l - 1)).prod

theorem letters_of {k : ℕ} (hk : k < 13) : ∀ l ∈ ew.getD k [], 1 ≤ l ∧ l ≤ 3 := by
  have h := letters
  have hk' : k < ew.length := by rw [h.2]; exact hk
  have hmem : ew.getD k [] ∈ ew := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
    exact List.getElem_mem hk'
  intro l hl
  have h1 := List.all_eq_true.1 h.1 _ hmem
  have h2 := List.all_eq_true.1 h1 l hl
  simpa using h2

theorem prep_cw {k : ℕ} (hk : k < 13) {P : ℕ}
    (h : Nat.beq P (wfoldK 240 8 (mask 8) cL (ew.getD k []) idP) = true) :
    PRep 240 8 P (cw (ew.getD k [])) := by
  rw [Nat.eq_of_beq_eq_true h]
  have := prep_wfoldK (S := cL) (f := fun l => cP (l - 1)) (ew.getD k [])
    (fun l hl => (prep_cS (j := l - 1) (by have := letters_of hk l hl; omega)).1) prep_idP
  rwa [one_mul] at this

theorem cw_mem {k : ℕ} (hk : k < 13) : cw (ew.getD k []) ∈ CSub := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  exact cP_mem_C (by have := letters_of hk l hl; omega)

theorem words_parts :
    (∀ k < 3, Nat.beq (E (9 + k)) (wfoldK 240 8 (mask 8) cL (ew.getD k []) idP) = true) ∧
    Nat.beq (E 13) (wfoldK 240 8 (mask 8) cL (ew.getD 3 []) idP) = true ∧
    ∀ k < 9, Nat.beq (E (14 + k)) (wfoldK 240 8 (mask 8) cL (ew.getD (4 + k) []) idP) = true := by
  have h := words
  simp only [kb_and, Bool.and_eq_true] at h
  exact ⟨CFSG.KS.allN_spec h.1, h.2.1, CFSG.KS.allN_spec h.2.2⟩

noncomputable abbrev p1 : Equiv.Perm (Fin 240) := cw (ew.getD 0 [])

noncomputable abbrev p2 : Equiv.Perm (Fin 240) := cw (ew.getD 1 [])

noncomputable abbrev cc : Equiv.Perm (Fin 240) := cw (ew.getD 2 [])

noncomputable abbrev x3 : Equiv.Perm (Fin 240) := cw (ew.getD 3 [])

theorem prep_p1 : PRep 240 8 (E 9) p1 := prep_cw (by norm_num) (words_parts.1 0 (by norm_num))

theorem prep_p2 : PRep 240 8 (E 10) p2 := prep_cw (by norm_num) (words_parts.1 1 (by norm_num))

theorem prep_c : PRep 240 8 (E 11) cc := prep_cw (by norm_num) (words_parts.1 2 (by norm_num))

theorem prep_x3 : PRep 240 8 (E 13) x3 := prep_cw (by norm_num) words_parts.2.1

theorem prep_cinv : PRep 240 8 (E 12) cc⁻¹ :=
  prep_of_rep (rep_inv_of_isInvA (rep_unpack prep_c) (isInvA_unpack invs_parts.2))

theorem prep_rL (l : ℕ) : PRep 240 8 (rL l) (if l = 1 then iP else jP) := by
  unfold rL
  rw [kn_if]
  by_cases h : l = 1
  · subst h
    rw [if_pos (Nat.beq_refl 1), if_pos rfl]
    exact prep_i
  · rw [if_neg (fun hb => h (Nat.eq_of_beq_eq_true hb)), if_neg h]
    exact prep_j

theorem rword_mem (wd : List ℕ) : (wd.map fun l => if l = 1 then iP else jP).prod ∈ RSub := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
  split_ifs
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem conj_R : ∀ c ∈ CSub, ∀ r ∈ RSub, c * r * c⁻¹ ∈ RSub := by
  rw [← C0_eq]
  refine conj_mem_of_closure fun g hg => ?_
  obtain ⟨j, rfl⟩ := hg
  refine conj_mem_closure fun r hr => ?_
  have hn := CFSG.KS.allN_spec CertificateChecks.KernelSp6Cover.norm j.val j.2
  simp only [kb_and, Bool.and_eq_true] at hn
  obtain ⟨hn1, hn2⟩ := hn
  have hc := prep_cS (j := j.val) (by omega)
  rcases hr with rfl | rfl
  · have e := prep_eq (prep_pc (prep_pc hc.1 prep_i) hc.2)
      (by rw [Nat.eq_of_beq_eq_true hn1]; exact prep_wfoldK _ (fun l _ => prep_rL l) prep_idP)
    rw [e, one_mul]
    exact rword_mem _
  · have e := prep_eq (prep_pc (prep_pc hc.1 prep_j) hc.2)
      (by rw [Nat.eq_of_beq_eq_true hn2]; exact prep_wfoldK _ (fun l _ => prep_rL l) prep_idP)
    rw [e, one_mul]
    exact rword_mem _

theorem prep_pL (l : ℕ) : PRep 240 8 (pL l) (if l = 1 then p1 else p2) := by
  unfold pL
  rw [kn_if]
  by_cases h : l = 1
  · subst h
    rw [if_pos (Nat.beq_refl 1), if_pos rfl]
    exact prep_p1
  · rw [if_neg (fun hb => h (Nat.eq_of_beq_eq_true hb)), if_neg h]
    exact prep_p2

noncomputable def pe (k : ℕ) : Equiv.Perm (Fin 240) := p1 ^ (k / 3) * p2 ^ (k % 3)

theorem prep_pe {k : ℕ} (hk : k < 9) : PRep 240 8 (E (23 + k)) (pe k) := by
  rw [Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec pels k hk)]
  have := prep_wfoldK (S := pL) (f := fun l => if l = 1 then p1 else p2) (pWord k)
    (fun l _ => prep_pL l) prep_idP
  convert this using 1
  simp [pe, pWord, List.map_append, List.map_replicate, List.prod_append, List.prod_replicate]

theorem pRel_parts : wfoldK 240 8 (mask 8) pL [1, 1, 1] idP = idP ∧
    wfoldK 240 8 (mask 8) pL [2, 2, 2] idP = idP ∧ commK (E 9) (E 10) = true ∧
    ∀ k < 8, neK (E (24 + k)) idP = true := by
  have h := pRel
  simp only [kb_and, Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1, h.2.2.1,
    CFSG.KS.allN_spec h.2.2.2⟩

theorem p1_cube : p1 ^ 3 = 1 := by
  have := prep_wfoldK (S := pL) (f := fun l => if l = 1 then p1 else p2) [1, 1, 1]
    (fun l _ => prep_pL l) prep_idP
  rw [pRel_parts.1] at this
  have e := prep_eq this prep_idP
  have e2 : p1 * (p1 * p1) = 1 := by simpa using e
  rw [pow_three]
  exact e2

theorem p2_cube : p2 ^ 3 = 1 := by
  have := prep_wfoldK (S := pL) (f := fun l => if l = 1 then p1 else p2) [2, 2, 2]
    (fun l _ => prep_pL l) prep_idP
  rw [pRel_parts.2.1] at this
  have e := prep_eq this prep_idP
  have e2 : p2 * (p2 * p2) = 1 := by simpa using e
  rw [pow_three]
  exact e2

theorem p_comm : p1 * p2 = p2 * p1 := comm_of prep_p1 prep_p2 pRel_parts.2.2.1

theorem prep_pe1 {k : ℕ} (hk : k < 8) : PRep 240 8 (E (24 + k)) (pe (k + 1)) := by
  have := prep_pe (k := k + 1) (by omega)
  have e : 23 + (k + 1) = 24 + k := by omega
  rwa [e] at this

theorem pe_ne {k : ℕ} (hk : k < 8) : pe (k + 1) ≠ 1 :=
  ne_of_prep (cnE (by omega)) canon_parts.2.1 (prep_pe1 hk) prep_idP
    (ne_of_neK (pRel_parts.2.2.2 k hk))

theorem kb_strictB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem pe_conj_ne {a b : ℕ} (ha : a < 8) (hb : b < 8) : cc * pe (a + 1) * cc⁻¹ ≠ pe (b + 1) := by
  have h := disj
  unfold disjK at h
  have h1 := CFSG.KS.allN_spec h a ha
  rw [kb_strictB] at h1
  have hne := ne_of_neK (CFSG.KS.allN_spec h1 b hb)
  exact ne_of_prep (cn_pc (cn_pc (cnE (by norm_num)) (cnE (by omega))) (cnE (by norm_num)))
    (cnE (by omega)) (prep_pc (prep_pc prep_c (prep_pe1 ha)) prep_cinv) (prep_pe1 hb) hne

theorem p1_mem : p1 ∈ CSub := cw_mem (by norm_num)

theorem p2_mem : p2 ∈ CSub := cw_mem (by norm_num)

theorem cc_mem : cc ∈ CSub := cw_mem (by norm_num)

noncomputable abbrev aT : CSub := ⟨p1, p1_mem⟩

noncomputable abbrev bT : CSub := ⟨p2, p2_mem⟩

noncomputable abbrev cT : CSub := ⟨cc, cc_mem⟩

noncomputable abbrev PT : Subgroup CSub := Subgroup.closure {aT, bT}

theorem aT_cube : aT ^ 3 = 1 := Subtype.ext (by simpa using p1_cube)

theorem bT_cube : bT ^ 3 = 1 := Subtype.ext (by simpa using p2_cube)

theorem aT_bT : aT * bT = bT * aT := Subtype.ext (by simpa using p_comm)

theorem div_mod_three {i j : ℕ} (hj : j < 3) : (3 * i + j) / 3 = i ∧ (3 * i + j) % 3 = j := by
  omega

theorem PT_ne : ∀ i < 3, ∀ j < 3, aT ^ i * bT ^ j = 1 → i = 0 ∧ j = 0 := by
  intro i hi j hj h
  have h' : p1 ^ i * p2 ^ j = 1 := by simpa using congrArg Subtype.val h
  by_contra hne
  have hk : 3 * i + j - 1 < 8 := by omega
  apply pe_ne hk
  have e1 : 3 * i + j - 1 + 1 = 3 * i + j := by omega
  rw [e1, pe, (div_mod_three hj).1, (div_mod_three hj).2]
  exact h'

theorem card_PT : Nat.card PT = 9 := card_closure_pair aT_cube bT_cube aT_bT PT_ne

theorem PT_form : ∀ x ∈ PT, ∃ k < 9, (x : Equiv.Perm (Fin 240)) = pe k := by
  intro x hx
  obtain ⟨i, hi, j, hj, rfl⟩ := closure_pair_form aT_cube bT_cube aT_bT x hx
  refine ⟨3 * i + j, by omega, ?_⟩
  rw [pe, (div_mod_three hj).1, (div_mod_three hj).2]
  simp

theorem pe_zero : pe 0 = 1 := by simp [pe]

theorem PT_disj : ∀ x ∈ PT, cT * x * cT⁻¹ ∈ PT → x = 1 := by
  intro x hx hcx
  obtain ⟨k, hk, ek⟩ := PT_form x hx
  obtain ⟨k', hk', ek'⟩ := PT_form _ hcx
  by_contra hne
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (Subtype.ext (by rw [ek, pe_zero]; rfl))
  rcases Nat.eq_zero_or_pos k' with rfl | hk'0
  · apply hne
    have h1 : cT * x * cT⁻¹ = 1 := Subtype.ext (by rw [ek', pe_zero]; rfl)
    calc x = cT⁻¹ * (cT * x * cT⁻¹) * cT := by group
      _ = 1 := by rw [h1]; group
  · apply pe_conj_ne (a := k - 1) (b := k' - 1) (by omega) (by omega)
    rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega), ← ek, ← ek']
    simp

theorem odd_fact : ∀ M : Subgroup (Equiv.Perm (Fin 240)), M ≤ CSub →
    (∀ c ∈ CSub, ∀ m ∈ M, c * m * c⁻¹ ∈ M) → Odd (Nat.card M) → M = ⊥ := by
  intro M hle hn hodd
  have hcard : Nat.card (M.subgroupOf CSub) = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hbot := odd_normal_eq_bot_of_disj card_C card_PT PT_disj (M.subgroupOf CSub)
    (fun g m hm => by
      rw [Subgroup.mem_subgroupOf] at hm ⊢
      simpa using hn g g.2 m hm)
    (by rw [hcard]; exact hodd)
  rw [Subgroup.eq_bot_iff_forall]
  intro m hm
  have h1 : (⟨m, hle hm⟩ : CSub) ∈ M.subgroupOf CSub := Subgroup.mem_subgroupOf.2 hm
  rw [hbot] at h1
  exact congrArg Subtype.val ((Subgroup.mem_bot).1 h1)

theorem acts3_fact : ∃ x ∈ CSub, x ^ 3 = 1 ∧ x * iP ≠ iP * x := by
  have h := acts3
  simp only [kb_and, Bool.and_eq_true] at h
  refine ⟨x3, cw_mem (by norm_num), ?_, not_comm_of (cnE (by norm_num)) (cnE (by norm_num))
    prep_x3 prep_i h.2⟩
  rw [pow_three']
  exact prep_eq (prep_pc (prep_pc prep_x3 prep_x3) prep_x3)
    (by rw [Nat.eq_of_beq_eq_true h.1]; exact prep_idP)

theorem cent_of {y : Equiv.Perm (Fin 240)} (hi : y * iP = iP * y) (hj : y * jP = jP * y) :
    ∀ r ∈ RSub, y * r = r * y := by
  intro r hr
  have hle : RSub ≤ Subgroup.centralizer {y} := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 hi.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 hj.symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hr)).symm

theorem good_parts {k : ℕ} (hk : k < 9) :
    (commK (E (23 + k)) (E 1) = true ∧ commK (E (23 + k)) (E 2) = true) ∨
    (commK (E (14 + k)) (E 1) = true ∧ commK (E (14 + k)) (E 2) = true ∧
      bIf(commK (E (23 + k)) (E (14 + k)), false, true) = true) := by
  have h := CFSG.KS.allN_spec good k hk
  rw [kb_if] at h
  by_cases hc : bAnd(commK (E (23 + k)) (E 1), commK (E (23 + k)) (E 2)) = true
  · left
    rw [kb_and, Bool.and_eq_true] at hc
    exact hc
  · right
    rw [if_neg hc, kb_and, kb_and, Bool.and_eq_true, Bool.and_eq_true] at h
    exact h

theorem i_mem_C : iP ∈ CSub :=
  Subgroup.mem_inf.2 ⟨i_mem, Subgroup.mem_centralizer_singleton_iff.2 (by rw [← i_mul_i, mul_assoc])⟩

theorem j_mem_C : jP ∈ CSub :=
  Subgroup.mem_inf.2 ⟨j_mem, Subgroup.mem_centralizer_singleton_iff.2 (by rw [← j_mul_j, mul_assoc])⟩

theorem good_fact : ∀ x ∈ CSub, x ^ 9 = 1 → (x * iP = iP * x ∧ x * jP = jP * x) ∨
    ∃ y ∈ CSub, y * iP = iP * y ∧ y * jP = jP * y ∧ x * y ≠ y * x := by
  intro x hx hx9
  have hR : ∀ g : CSub, ∀ r ∈ RSub.subgroupOf CSub, g * r * g⁻¹ ∈ RSub.subgroupOf CSub :=
    fun g r hr => by
      rw [Subgroup.mem_subgroupOf] at hr ⊢
      simpa using conj_R g g.2 r hr
  have hgood : ∀ p ∈ PT, (∀ r ∈ RSub.subgroupOf CSub, p * r = r * p) ∨
      ∃ y : CSub, (∀ r ∈ RSub.subgroupOf CSub, y * r = r * y) ∧ p * y ≠ y * p := by
    intro p hp
    obtain ⟨k, hk, ek⟩ := PT_form p hp
    rcases good_parts hk with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · left
      have hc := cent_of (comm_of (prep_pe hk) prep_i h1) (comm_of (prep_pe hk) prep_j h2)
      intro r hr
      exact Subtype.ext (by simpa [ek] using hc r (Subgroup.mem_subgroupOf.1 hr))
    · right
      have hyk := prep_cw (k := 4 + k) (by omega) (words_parts.2.2 k hk)
      have hc := cent_of (comm_of hyk prep_i h1) (comm_of hyk prep_j h2)
      refine ⟨⟨_, cw_mem (k := 4 + k) (by omega)⟩, fun r hr =>
        Subtype.ext (by simpa using hc r (Subgroup.mem_subgroupOf.1 hr)), fun he => ?_⟩
      exact not_comm_of (cnE (by omega)) (cnE (by omega)) (prep_pe hk) hyk h3
        (by simpa [ek] using congrArg Subtype.val he)
  have hiR : (⟨iP, i_mem_C⟩ : CSub) ∈ RSub.subgroupOf CSub :=
    Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure (by simp))
  have hjR : (⟨jP, j_mem_C⟩ : CSub) ∈ RSub.subgroupOf CSub :=
    Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure (by simp))
  rcases centralizes_or_of_sylow (x := (⟨x, hx⟩ : CSub)) card_C card_PT (RSub.subgroupOf CSub) hR
    hgood (Subtype.ext (by simpa using hx9)) with hc | ⟨y, hy, hne⟩
  · left
    exact ⟨by simpa using congrArg Subtype.val (hc _ hiR),
      by simpa using congrArg Subtype.val (hc _ hjR)⟩
  · right
    refine ⟨y, y.2, by simpa using congrArg Subtype.val (hy _ hiR),
      by simpa using congrArg Subtype.val (hy _ hjR), fun he => hne (Subtype.ext ?_)⟩
    simpa using he

theorem rep_cA {k : ℕ} (hk : k < 3) : Rep 240 cA[k]! (permOfArr 240 cA[k]!) := by
  have := rep_unpack (prep_cS (j := k) (by omega)).1
  have e : cP k = permOfArr 240 cA[k]! := congrArg (permOfArr 240) (cS_get hk)
  rw [← cbind.2.1 k (by omega), cS_get hk, e] at this
  exact this

theorem forall_cA {p : Array ℕ → Prop} (h : ∀ k < 3, p cA[k]!) : ∀ a ∈ cA.toList, p a := by
  intro a ha
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  have hk' : k < 3 := by
    rw [Array.length_toList] at hk
    exact hk
  rw [Array.getElem_toList, ← getElem!_pos cA k (by rw [cA_size']; exact hk')]
  exact h k hk'

theorem rep_data : ∀ a ∈ [tA, iA, jA] ++ cA.toList, Rep 240 a (permOfArr 240 a) := by
  intro a ha
  rw [List.mem_append] at ha
  rcases ha with ha | ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact rep_tA
    · have := rep_unpack prep_i
      rwa [← ebind.2.1] at this
    · have := rep_unpack prep_j
      rwa [← ebind.2.2.1] at this
  · exact forall_cA (p := fun a => Rep 240 a (permOfArr 240 a)) (fun k hk => rep_cA hk) a ha

theorem cA_mem_C : ∀ a ∈ cA.toList, permOfArr 240 a ∈ CSub :=
  forall_cA (p := fun a => permOfArr 240 a ∈ CSub) fun k hk => by
    have e : cP k = permOfArr 240 cA[k]! := congrArg (permOfArr 240) (cS_get hk)
    rw [← e]
    exact cP_mem_C hk

theorem facts118002 :
    Nat.card ySub = 2903040 ∧
    (∀ k < 3, Rep 240 yS[k]! (dP k)) ∧
    (∀ a ∈ [tA, iA, jA] ++ cA.toList, Rep 240 a (permOfArr 240 a)) ∧
    tP ∈ ySub ∧ iP ∈ ySub ∧ jP ∈ ySub ∧ (∀ k < 3, gP k ∈ ySub) ∧
    (∀ a ∈ cA.toList, permOfArr 240 a ∈ CSub) ∧
    (∀ k < 3, (dP k)⁻¹ = tP * (gP k * tP * (gP k)⁻¹)) ∧
    tP * tP = 1 ∧ tP ≠ 1 ∧ iP * iP = tP ∧ jP * jP = tP ∧ jP * iP * jP⁻¹ = iP⁻¹ ∧
    Nat.card CSub = 4608 ∧
    (∀ c ∈ CSub, ∀ r ∈ RSub, c * r * c⁻¹ ∈ RSub) ∧
    (∀ M : Subgroup (Equiv.Perm (Fin 240)), M ≤ CSub →
      (∀ c ∈ CSub, ∀ m ∈ M, c * m * c⁻¹ ∈ M) → Odd (Nat.card M) → M = ⊥) ∧
    (∃ x ∈ CSub, x ^ 3 = 1 ∧ x * iP ≠ iP * x) ∧
    (∀ x ∈ CSub, x ^ 9 = 1 → (x * iP = iP * x ∧ x * jP = jP * x) ∨
      ∃ y ∈ CSub, y * iP = iP * y ∧ y * jP = jP * y ∧ x * y ≠ y * x) :=
  ⟨card_Y, fun _ hk => rep_d hk, rep_data, t_mem, i_mem, j_mem, fun _ hk => g_mem hk, cA_mem_C,
    fun _ hk => d_inv hk, t_mul_t, t_ne_one, i_mul_i, j_mul_j, j_i_j, card_C, conj_R, odd_fact,
    acts3_fact, good_fact⟩

end CertificateChecks.KernelSp6Cover
