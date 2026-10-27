module

public import Certificates.Kernel.HN1408.Y442202Inst
public import Certificates.Kernel.HN1408.SylSGlue
public import CFSG.Certificates.Kernel.Misc.PermClosOrbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5YFactsK
import Certificates.Kernel.HN1408.Y442202Sl0
import Certificates.Kernel.HN1408.Y442202Sl1
import Certificates.Kernel.HN1408.Y442202Sl2
import Certificates.Kernel.HN1408.Y442202Sl3
import Certificates.Kernel.HN1408.Y442202Wd
import Certificates.Kernel.HN1408.Y442202Flt
import Certificates.Kernel.HN1408.Y442202Bad
import Certificates.Kernel.HN1408.Y442202Good
import Certificates.Kernel.HN1408.Y442202Cent
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Basic

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Y442202

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
  CFSG.KS.RecGroup CFSG.KD.HN1408 CFSG.KD.HN1408.SylSG CFSG.KC.Misc.Clos
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Simple2S5
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.KS.Raw.Orb (strictB_eq bAnd_eq bIf_eq nIf_eq)

abbrev RC (X : ℕ) (g : Equiv.Perm (Fin 1408)) : Prop :=
  Cn X ∧ Rep 1408 (tabT (unpack 1408 11 X)) g

theorem rc_pc {X Y : ℕ} {g h : Equiv.Perm (Fin 1408)} (hX : RC X g) (hY : RC Y h) :
    RC (pc X Y) (g * h) := by
  refine ⟨CFSG.KC.BfsPin.canonK_pcomp hX.1 hY.1, ?_⟩
  have e : pc X Y = pcomp 1408 11 (mask 11) X Y := rfl
  rw [e, ← compT_unpack hX.1 hY.1]
  exact Rep.compT hX.2 hY.2

theorem rc_word {w : List ℕ} (hw : lettersOK w = true) : RC (WK w) (elemW w) :=
  ⟨(rep_word hw).2, (rep_word hw).1⟩

theorem rc_id : RC idK 1 := ⟨cId, by rw [← idT_eq]; exact Rep.idT (by norm_num)⟩

theorem perm_eq {X : ℕ} {g h : Equiv.Perm (Fin 1408)} (hg : RC X g) (hh : RC X h) : g = h :=
  CFSG.Sporadic.Schreier.rep_unique hg.2 hh.2

theorem nat_eq {X Y : ℕ} {g : Equiv.Perm (Fin 1408)} (hX : RC X g) (hY : RC Y g) : X = Y := by
  obtain ⟨-, hw, h1, -⟩ := CFSG.KS.PF.canon_facts hX.1
  obtain ⟨-, -, h2, -⟩ := CFSG.KS.PF.canon_facts hY.1
  exact CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) h1 h2 fun i hi => by
    rw [pt_rep hX.1 hX.2 hi, pt_rep hY.1 hY.2 hi]

theorem rc_pt {X p : ℕ} {g : Equiv.Perm (Fin 1408)} (hX : RC X g) (hp : p < 1408) :
    pt X p = (g ⟨p, hp⟩).val := by
  unfold pt
  rw [pt_rep hX.1 hX.2 hp, idx_of_lt g hp, Equiv.Perm.smul_def]

theorem comm_of {X Y : ℕ} {g h : Equiv.Perm (Fin 1408)} (hX : RC X g) (hY : RC Y h)
    (hc : commP X Y = true) : g * h = h * g := by
  unfold commP at hc
  have e : pc X Y = pc Y X := Nat.eq_of_beq_eq_true hc
  exact perm_eq (rc_pc hX hY) (by rw [e]; exact rc_pc hY hX)

theorem conj_of {X Y Z : ℕ} {g h k : Equiv.Perm (Fin 1408)} (hX : RC X g) (hY : RC Y h)
    (hZ : RC Z k) (hc : conjInK X Y Z = true) : g * h * g⁻¹ = k := by
  unfold conjInK at hc
  have e : pc X Y = pc Z X := Nat.eq_of_beq_eq_true hc
  exact mul_inv_eq_iff_eq_mul.2 (perm_eq (rc_pc hX hY) (by rw [e]; exact rc_pc hZ hX))

theorem ne_of_bIf {a b : ℕ}
    (h : Bool.rec (motive := fun _ => Bool) true false (Nat.beq a b) = true) : a ≠ b := by
  intro e
  subst e
  rw [Nat.beq_refl] at h
  exact Bool.false_ne_true h

theorem oneOr_of {t q : ℕ} (h : q = idK ∨ q = t) : oneOr t q = true := by
  unfold oneOr
  rw [bIf_eq]
  rcases h with rfl | rfl
  · rw [if_pos (Nat.beq_refl _)]
  · split
    · rfl
    · exact Nat.beq_refl _

theorem mem_C {X tK : ℕ} {w : List ℕ} {t : Equiv.Perm (Fin 1408)} (hX : RC X (elemW w))
    (ht : RC tK t) (hh : halvesK X = true) (hc : commP X tK = true) :
    elemW w ∈ pPrime ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 1408))) := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨elemW_mem w, ?_⟩, ?_⟩
  · exact mem_blocks1408_of_preservesHalves hX.2 (halves_eq hX.1 hh)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact comm_of hX ht hc

structure Rec (T : ℕ → ℕ) (cnt : ℕ) (O : Subgroup (Equiv.Perm (Fin 1408)))
    (x : ℕ → Equiv.Perm (Fin 1408)) : Prop where
  one : x 0 = 1
  rc : ∀ i < cnt, RC (T i) (x i)
  inj : ∀ a < cnt, ∀ b < cnt, x a = x b → a = b
  mem : ∀ y, y ∈ O ↔ ∃ i < cnt, x i = y
  card : Nat.card ↥O = cnt

theorem Rec.mem_of {T : ℕ → ℕ} {cnt : ℕ} {O : Subgroup (Equiv.Perm (Fin 1408))}
    {x : ℕ → Equiv.Perm (Fin 1408)} (R : Rec T cnt O x) {k : ℕ} (hk : k < cnt)
    {g : Equiv.Perm (Fin 1408)} (hg : RC (T k) g) : g ∈ O :=
  (R.mem g).2 ⟨k, hk, perm_eq (R.rc k hk) hg⟩

theorem rec_facts {G GI T PL POS SRT SRI : ℕ → ℕ} {k cnt : ℕ} {ws : List (List ℕ)}
    (hr : recOK G GI k cnt T PL POS SRT SRI = true) (hk : ws.length = k)
    (hG : allN k (fun j => Nat.beq (G j) (WK (ws.getD j []))) = true)
    (hw : ∀ j < k, lettersOK (ws.getD j []) = true) :
    ∃ x, Rec T cnt (wSub ws) x := by
  unfold recOK at hr
  rw [bAnd_eq, Bool.and_eq_true] at hr
  have hp : ∀ i < cnt, penumPtK 1408 11 (mask 11) (1408 * 11) false G GI k cnt T PL POS SRT SRI i =
      true := fun i hi =>
    CFSG.KS.BaseMask.penumSl_spec hr.2 (Nat.zero_le i) (Nat.lt_of_lt_of_le hi (Nat.le_add_left _ _)) hi
  have hg : ∀ j < k, canonK 1408 11 (mask 11) (1408 * 11) (G j) = true ∧
      Rep 1408 (tabT (unpack 1408 11 (G j))) (elemW (ws.getD j [])) := fun j hj => by
    rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 hG j hj)]
    exact ⟨(rep_word (hw j hj)).2, (rep_word (hw j hj)).1⟩
  obtain ⟨x, h0, hrep, hinj, hmem, hcard⟩ := penumLeft_closure (n := 1408) (w := 11) (k := k)
    (cnt := cnt) (cap := 4096) (g := fun j => elemW (ws.getD j [])) hn (by norm_num) hg hr.1 hp
  have hcl : closure ((fun j => elemW (ws.getD j [])) '' {j | j < k}) = wSub ws := by
    rw [← hk, image_getD]
    rfl
  refine ⟨x, ⟨h0, fun i hi => ⟨(penumPt_specH (hp i hi)).1, hrep i hi⟩, hinj, fun y => ?_, ?_⟩⟩
  · rw [← hcl]
    exact hmem y
  · rw [← hcl]
    exact hcard

theorem gens_parts : allN 6 (fun j => Nat.beq (OZ.G j) (WK (oGensZ.getD j []))) = true ∧
    allN 6 (fun j => Nat.beq (OAZ.G j) (WK (oGensAZ.getD j []))) = true ∧
    allN 2 (fun j => Nat.beq (Y0.G j) (WK ((ykWords.getD 0 []).getD j []))) = true ∧
    allN 2 (fun j => Nat.beq (Y1.G j) (WK ((ykWords.getD 1 []).getD j []))) = true := by
  have h := ch442202_gens
  unfold gensOK gensK at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  exact h

theorem lettZ : ∀ j < 6, lettersOK (oGensZ.getD j []) = true := by decide

theorem lettAZ : ∀ j < 6, lettersOK (oGensAZ.getD j []) = true := by decide

theorem rZ : ∃ x, Rec OZ.T 128 (wSub oGensZ) x :=
  rec_facts ch442202_recOZ (by decide) gens_parts.1 lettZ

theorem rAZ : ∃ x, Rec OAZ.T 128 (wSub oGensAZ) x :=
  rec_facts ch442202_recOAZ (by decide) gens_parts.2.1 lettAZ

theorem rY0 : ∃ x, Rec Y0.T 240 (yK 0) x :=
  rec_facts ch442202_recY0 (by decide) gens_parts.2.2.1 (by decide)

theorem rY1 : ∃ x, Rec Y1.T 240 (yK 1) x :=
  rec_facts ch442202_recY1 (by decide) gens_parts.2.2.2 (by decide)

theorem wList_letters : ∀ j < 72, lettersOK (wList.getD j []) = true := by decide

theorem W_rc {j : ℕ} (hj : j < 72) : RC (W j) (elemW (wList.getD j [])) := by
  have e : W j = WK (wList.getD j []) := by
    rcases Nat.lt_or_ge j 8 with h8 | h8
    · have h := Orb.allN_iff.1 ch442202_w0 j h8
      rw [strictB_eq] at h
      have e0 : Nat.add 0 j = j := Nat.zero_add j
      rw [e0] at h
      exact Nat.eq_of_beq_eq_true h
    · have h := Orb.allN_iff.1 ch442202_w8 (j - 8) (by change j - 8 < 64; omega)
      rw [strictB_eq] at h
      have e8 : Nat.add 8 (j - 8) = j := by
        change 8 + (j - 8) = j
        omega
      rw [e8] at h
      exact Nat.eq_of_beq_eq_true h
  rw [e]
  exact rc_word (wList_letters j hj)

theorem W_rc_eq {j : ℕ} (hj : j < 72) {w : List ℕ} (e : wList.getD j [] = w) : RC (W j) (elemW w) := by
  rw [← e]
  exact W_rc hj

theorem rc_s₁ : RC (W 0) (elemW sOne) := W_rc_eq (by norm_num) (by decide)

theorem rc_s₂ : RC (W 1) (elemW sTwo) := W_rc_eq (by norm_num) (by decide)

theorem rc_z : RC (W 2) elemZ := W_rc_eq (w := wordZ) (by norm_num) (by decide)

theorem rc_az : RC (W 3) (elemA * elemZ) := by
  have h := W_rc_eq (w := wordA ++ wordZ) (j := 3) (by norm_num) (by decide)
  have e : elemW (wordA ++ wordZ) = elemA * elemZ := by
    simp only [elemW, elemA, elemZ, CFSG.EvenSporadicStandard.TwoHS.wordVal, List.map_append,
      List.prod_append]
  rw [e] at h
  exact h

theorem cz_eq : ∀ c < 2, wList.getD (4 + c) [] = classz.centGens.getD c [] := by decide

theorem caz_eq : ∀ c < 2, wList.getD (6 + c) [] = classaz.centGens.getD c [] := by decide

theorem centK_parts {G T CI C : ℕ → ℕ} {t s₁ s₂ nC cSwap : ℕ}
    (h : centK G T CI t s₁ s₂ C nC 6 128 cSwap = true) :
    (∀ j < 6, halvesK (G j) = true ∧ commP (G j) t = true) ∧ CI 0 < 128 ∧ T (CI 0) = t ∧
      halvesK s₁ = true ∧ commP s₁ t = true ∧ halvesK s₂ = true ∧ commP s₂ t = true ∧
      CI 1 < 128 ∧ pc s₁ s₁ = T (CI 1) ∧ CI 2 < 128 ∧
      pc (pc (pc s₂ s₂) (pc s₂ s₂)) s₂ = T (CI 2) ∧
      (∀ c < nC, ∀ j < 6, CI (3 + (c * 6 + j)) < 128 ∧
        conjInK (C c) (G j) (T (CI (3 + (c * 6 + j))))  = true) ∧
      704 ≤ pt cSwap 0 := by
  unfold centK at h
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, Orb.allN_iff, Nat.blt_eq, Nat.ble_eq,
    Nat.beq_eq, Nat.add_eq, Nat.mul_eq] at h
  obtain ⟨hG, h0, hT0, hh1, hc1, hh2, hc2, h1, hs1, h2, hs2, hcj, hsw⟩ := h
  exact ⟨hG, h0, hT0, hh1, hc1, hh2, hc2, h1, hs1, h2, hs2, fun c hc j hj => hcj c hc j hj, hsw⟩

theorem centFactsK_of {G T CI C : ℕ → ℕ} {tK s₁K s₂K nC cSwap i : ℕ} {ws cg : List (List ℕ)}
    {w₁ w₂ : List ℕ} {t : Equiv.Perm (Fin 1408)} {x : ℕ → Equiv.Perm (Fin 1408)}
    (R : Rec T 128 (wSub ws) x) (hws : ws.length = 6)
    (hG : ∀ j < 6, RC (G j) (elemW (ws.getD j []))) (ht : RC tK t) (h1 : RC s₁K (elemW w₁))
    (h2 : RC s₂K (elemW w₂)) (hcg : cg.length = nC)
    (hC : ∀ c < nC, RC (C c) (elemW (cg.getD c []))) (hsw : RC cSwap (elemW (cg.getD i [])))
    (h : centK G T CI tK s₁K s₂K C nC 6 128 cSwap = true) :
    CentFactsK t (wSub ws) (elemW w₁) (elemW w₂) cg i := by
  obtain ⟨hGc, h0, hT0, hh1, hc1, hh2, hc2, hi1, hs1, hi2, hs2, hcj, hswap⟩ := centK_parts h
  refine
    { card_O := R.card
      O_le := ?_
      mem_O := R.mem_of h0 (by rw [hT0]; exact ht)
      norm_gens := ?_
      swap := ?_
      s₁_mem := mem_C h1 ht hh1 hc1
      s₂_mem := mem_C h2 ht hh2 hc2
      s₁_sq := R.mem_of hi1 (by rw [← hs1]; exact rc_pc h1 h1)
      s₂_pow := ?_ }
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
    have hj6 : j < 6 := by rw [← hws]; exact hj
    have hg := hG j hj6
    rw [List.getD_eq_getElem _ _ hj] at hg
    exact mem_C hg ht (hGc j hj6).1 (hGc j hj6).2
  · intro w hw o ho
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hw
    have hcn : c < nC := by rw [← hcg]; exact hc
    have hκ := hC c hcn
    rw [List.getD_eq_getElem _ _ hc] at hκ
    have hle : wSub ws ≤ (wSub ws).comap (MulAut.conj (elemW cg[c])).toMonoidHom := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
      have hj6 : j < 6 := by rw [← hws]; exact hj
      have hg := hG j hj6
      rw [List.getD_eq_getElem _ _ hj] at hg
      obtain ⟨hk, hcj'⟩ := hcj c hcn j hj6
      simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [conj_of hκ hg (R.rc _ hk) hcj']
      exact (R.mem _).2 ⟨_, hk, rfl⟩
    have := hle ho
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    exact this
  · exact not_mem_blocks1408_of_swapsZero hsw.2 (by rw [swapsZero_eq hsw.1]; exact decide_eq_true hswap)
  · have e : elemW w₂ ^ 5 = elemW w₂ * elemW w₂ * (elemW w₂ * elemW w₂) * elemW w₂ := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e]
    exact R.mem_of hi2 (by rw [← hs2]; exact rc_pc (rc_pc (rc_pc h2 h2) (rc_pc h2 h2)) h2)

theorem flt_at {T : ℕ → ℕ} {cnt s₁K s₂K tK nA nB : ℕ} {YA YB FA FB : ℕ → ℕ}
    (hf : fltK T cnt s₁K s₂K tK nA nB YA YB FA FB = true) {i : ℕ} (hi : i < cnt) :
    (oneOr tK (pc (pc s₁K (T i)) (pc s₁K (T i))) = true →
        FA i < nA ∧ YA (FA i) = pc s₁K (T i)) ∧
      (oneOr tK (pc (pc (pc (pc s₂K (T i)) (pc s₂K (T i))) (pc (pc s₂K (T i)) (pc s₂K (T i))))
          (pc s₂K (T i))) = true → FB i < nB ∧ YB (FB i) = pc s₂K (T i)) := by
  unfold fltK at hf
  have h := Orb.allN_iff.1 hf i hi
  unfold fltSq fltQu at h
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hA, hB⟩ := h
  rw [bIf_eq] at hA hB
  refine ⟨fun ho => ?_, fun ho => ?_⟩
  · rw [if_pos ho, Bool.and_eq_true, Nat.blt_eq] at hA
    exact ⟨hA.1, Nat.eq_of_beq_eq_true hA.2⟩
  · rw [if_pos ho, Bool.and_eq_true, Nat.blt_eq] at hB
    exact ⟨hB.1, Nat.eq_of_beq_eq_true hB.2⟩

theorem pow5 (y : Equiv.Perm (Fin 1408)) : y * y * (y * y) * y = y ^ 5 := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem pairs_of {T : ℕ → ℕ} {O : Subgroup (Equiv.Perm (Fin 1408))}
    {x : ℕ → Equiv.Perm (Fin 1408)} (R : Rec T 128 O x) {tK s₁K s₂K : ℕ}
    {t s₁ s₂ : Equiv.Perm (Fin 1408)} (ht : RC tK t) (h1 : RC s₁K s₁) (h2 : RC s₂K s₂)
    {YA YB FA FB : ℕ → ℕ} (hf : fltK T 128 s₁K s₂K tK 16 32 YA YB FA FB = true)
    {P : Equiv.Perm (Fin 1408) → Equiv.Perm (Fin 1408) → Prop}
    (hab : ∀ a < 16, ∀ b < 32, ∀ y₁ y₂, RC (YA a) y₁ → RC (YB b) y₂ → P y₁ y₂) :
    ∀ o₁ ∈ O, ∀ o₂ ∈ O, ((s₁ * o₁) * (s₁ * o₁) = 1 ∨ (s₁ * o₁) * (s₁ * o₁) = t) →
      ((s₂ * o₂) ^ 5 = 1 ∨ (s₂ * o₂) ^ 5 = t) → P (s₁ * o₁) (s₂ * o₂) := by
  intro o₁ ho₁ o₂ ho₂ hq₁ hq₂
  obtain ⟨i, hi, rfl⟩ := (R.mem o₁).1 ho₁
  obtain ⟨j, hj, rfl⟩ := (R.mem o₂).1 ho₂
  have hy₁ := rc_pc h1 (R.rc i hi)
  have hy₂ := rc_pc h2 (R.rc j hj)
  have ha := (flt_at hf hi).1 (oneOr_of (by
    have r := rc_pc hy₁ hy₁
    rcases hq₁ with e | e
    · rw [e] at r
      exact Or.inl (nat_eq r rc_id)
    · rw [e] at r
      exact Or.inr (nat_eq r ht)))
  have hb := (flt_at hf hj).2 (oneOr_of (by
    have r := rc_pc (rc_pc (rc_pc hy₂ hy₂) (rc_pc hy₂ hy₂)) hy₂
    rw [pow5] at r
    rcases hq₂ with e | e
    · rw [e] at r
      exact Or.inl (nat_eq r rc_id)
    · rw [e] at r
      exact Or.inr (nat_eq r ht)))
  refine hab _ ha.1 _ hb.1 _ _ ?_ ?_
  · rw [ha.2]
    exact hy₁
  · rw [hb.2]
    exact hy₂

theorem mem_pair {y₁ y₂ : Equiv.Perm (Fin 1408)} :
    y₁ ∈ closure ({y₁, y₂} : Set (Equiv.Perm (Fin 1408))) ∧
      y₂ ∈ closure ({y₁, y₂} : Set (Equiv.Perm (Fin 1408))) :=
  ⟨subset_closure (Set.mem_insert _ _), subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

theorem bad_of {T : ℕ → ℕ} {O : Subgroup (Equiv.Perm (Fin 1408))}
    {x : ℕ → Equiv.Perm (Fin 1408)} (R : Rec T 128 O x) {kt tK : ℕ} {t : Equiv.Perm (Fin 1408)}
    (hkt : kt < 128) (hT : T kt = tK) (ht : RC tK t) {y₁K y₂K k : ℕ}
    {y₁ y₂ : Equiv.Perm (Fin 1408)} (h1 : RC y₁K y₁) (h2 : RC y₂K y₂)
    (h : badK T 128 kt y₁K y₂K k = true) : PairBad O t y₁ y₂ := by
  unfold PairBad
  unfold badK at h
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hk, h0, hkt', he⟩ := h
  have hw : RC (T k) (y₁ * y₂ * (y₁ * y₂) * (y₁ * y₂ * (y₁ * y₂))) := by
    rw [← he]
    have hu := rc_pc h1 h2
    exact rc_pc (rc_pc hu hu) (rc_pc hu hu)
  have hxt : x kt = t := perm_eq (R.rc kt hkt) (by rw [hT]; exact ht)
  refine ⟨x k, ?_, (R.mem _).2 ⟨k, hk, rfl⟩, fun e => ?_, fun e => ?_⟩
  · rw [perm_eq (R.rc k hk) hw]
    obtain ⟨m1, m2⟩ := mem_pair (y₁ := y₁) (y₂ := y₂)
    have hu := mul_mem m1 m2
    exact mul_mem (mul_mem hu hu) (mul_mem hu hu)
  · exact ne_of_bIf h0 (R.inj k hk 0 (by norm_num) (e.trans R.one.symm))
  · exact ne_of_bIf hkt' (R.inj k hk kt hkt (e.trans hxt.symm))

theorem badAll_at {T : ℕ → ℕ} {cnt kt nA nB : ℕ} {YA YB C : ℕ → ℕ}
    (h : badAllK T cnt kt nA nB YA YB C = true) {a b : ℕ} (ha : a < nA) (hb : b < nB) :
    badK T cnt kt (YA a) (YB b) (C (a * nB + b)) = true := by
  unfold badAllK at h
  have h1 := Orb.allN_iff.1 h a ha
  simp only [strictB_eq] at h1
  exact Orb.allN_iff.1 h1 b hb

theorem badSome_at {T : ℕ → ℕ} {cnt kt nA nB : ℕ} {YA YB C : ℕ → ℕ}
    (h : badSomeK T cnt kt nA nB YA YB C = true) {a b : ℕ} (ha : a < nA) (hb : b < nB)
    (hk : C (a * nB + b) < 1000) : badK T cnt kt (YA a) (YB b) (C (a * nB + b)) = true := by
  unfold badSomeK at h
  have h1 := Orb.allN_iff.1 h a ha
  simp only [strictB_eq] at h1
  have h2 := Orb.allN_iff.1 h1 b hb
  simp only [strictB_eq, bIf_eq] at h2
  have hb' : Nat.blt (C (Nat.add (Nat.mul a nB) b)) (nat_lit 1000) = true := by
    rw [Nat.blt_eq]
    exact hk
  rw [if_pos hb'] at h2
  exact h2

theorem good_at {a b : ℕ} (ha : a < 16) (hb : b < 32) (hk : ¬ r32 Caz (a * 32 + b) < 1000) :
    goodRow (r32 Caz (a * 32 + b) - 1000) (YAaz a) (YBaz b) = true := by
  have h := ch442202_goodAZ
  unfold goodAZ at h
  have h1 := Orb.allN_iff.1 h a ha
  simp only [strictB_eq] at h1
  have h2 := Orb.allN_iff.1 h1 b hb
  simp only [strictB_eq, bIf_eq] at h2
  have hb' : ¬ Nat.blt (r32 Caz (Nat.add (Nat.mul a (nat_lit 32)) b)) (nat_lit 1000) = true := by
    rw [Nat.blt_eq]
    exact hk
  rw [if_neg hb'] at h2
  exact h2

@[expose] def encP (p : Fin 1408 × Fin 1408) : ℕ := p.1.val * 1408 + p.2.val

theorem pairAct_eq (e g : ℕ) : pairAct e g = pt g (e / 1408) * 1408 + pt g (e % 1408) := rfl

theorem orb_card {y₁K y₂K : ℕ} {y₁ y₂ : Equiv.Perm (Fin 1408)} (h1 : RC y₁K y₁)
    (h2 : RC y₂K y₂) {E PA SG CT : ℕ → ℕ} (h : orbK y₁K y₂K 240 E PA SG CT = true) :
    240 ≤ Nat.card ↥(closure ({y₁, y₂} : Set (Equiv.Perm (Fin 1408)))) := by
  unfold orbK at h
  simp only [bAnd_eq, Bool.and_eq_true, Orb.allN_iff, Nat.blt_eq] at h
  obtain ⟨hE0, hall⟩ := h
  have hE0' : E 0 < 1982464 := hE0
  have hinj : Function.Injective encP := by
    rintro ⟨a, b⟩ ⟨c, d⟩ e
    have e' : a.val * 1408 + b.val = c.val * 1408 + d.val := e
    have := a.isLt
    have := b.isLt
    have := c.isLt
    have := d.isLt
    simp only [Prod.mk.injEq, Fin.ext_iff]
    constructor <;> omega
  have hM : ∀ j < [y₁, y₂].length, ∀ p, encP ([y₁, y₂].getD j 1 • p) =
      pairAct (encP p) (gen2 y₁K y₂K j) := by
    intro j hj p
    have hj2 : j < 2 := hj
    obtain ⟨σ, X, hX, e1, e2⟩ : ∃ σ X, RC X σ ∧ [y₁, y₂].getD j 1 = σ ∧ gen2 y₁K y₂K j = X := by
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · exact ⟨y₁, y₁K, h1, rfl, rfl⟩
      · exact ⟨y₂, y₂K, h2, rfl, rfl⟩
    rw [e1, e2, pairAct_eq]
    obtain ⟨a, b⟩ := p
    have := a.isLt
    have := b.isLt
    have hd : (a.val * 1408 + b.val) / 1408 = a.val := by omega
    have hm : (a.val * 1408 + b.val) % 1408 = b.val := by omega
    simp only [encP, Prod.smul_mk, Equiv.Perm.smul_def]
    rw [hd, hm, rc_pt hX a.isLt, rc_pt hX b.isLt]
  obtain ⟨x₀, hx0⟩ : ∃ x₀ : Fin 1408 × Fin 1408, encP x₀ = E 0 :=
    ⟨(⟨E 0 / 1408, by omega⟩, ⟨E 0 % 1408, by omega⟩), by simp only [encP, Fin.val_mk]; omega⟩
  have ht : ∀ k < 240, treeAt pairAct (encP x₀) (gen2 y₁K y₂K) [y₁, y₂].length E PA k = true :=
    fun k hk => by
      rw [hx0]
      exact (hall k hk).1
  obtain ⟨-, -, hcard⟩ := orbit_card_proved (H := Equiv.Perm (Fin 1408)) hinj [y₁, y₂] hM x₀
    (N := 240) (by norm_num) ht (fun k hk => (hall k hk).2.1) (fun k hk => (hall k hk).2.2)
  have hset : {g | g ∈ [y₁, y₂]} = ({y₁, y₂} : Set (Equiv.Perm (Fin 1408))) := by
    ext g
    simp
  rw [hset] at hcard
  rw [← hcard]
  exact Nat.card_le_card_of_surjective
    (fun g : ↥(closure ({y₁, y₂} : Set (Equiv.Perm (Fin 1408)))) =>
      (⟨g.1 • x₀, g.1, g.2, rfl⟩ :
        {y // ∃ g ∈ closure ({y₁, y₂} : Set (Equiv.Perm (Fin 1408))), g • x₀ = y}))
    (by
      rintro ⟨y, g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩)

theorem yt_rc {xY0 xY1 : ℕ → Equiv.Perm (Fin 1408)} (R0 : Rec Y0.T 240 (yK 0) xY0)
    (R1 : Rec Y1.T 240 (yK 1) xY1) {k j : ℕ} (hk : k < 2) (hj : j < 240) :
    ∃ e ∈ yK k, RC (YT k j) e := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact ⟨xY0 j, (R0.mem _).2 ⟨j, hj, rfl⟩, R0.rc j hj⟩
  · exact ⟨xY1 j, (R1.mem _).2 ⟨j, hj, rfl⟩, R1.rc j hj⟩

theorem good_of {xY0 xY1 : ℕ → Equiv.Perm (Fin 1408)} (R0 : Rec Y0.T 240 (yK 0) xY0)
    (R1 : Rec Y1.T 240 (yK 1) xY1) {y₁K y₂K g : ℕ} {y₁ y₂ : Equiv.Perm (Fin 1408)}
    (h1 : RC y₁K y₁) (h2 : RC y₂K y₂) (h : goodRow g y₁K y₂K = true) :
    PairGood (elemA * elemZ) y₁ y₂ := by
  unfold PairGood
  unfold goodRow at h
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hc, hk, hgood, horb⟩ := h
  unfold goodK at hgood
  simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at hgood
  obtain ⟨hj1, hj2, hc1, hc2⟩ := hgood
  have hκ : RC (W (8 + r32 GC g)) (elemW (wList.getD (8 + r32 GC g) [])) := W_rc (by omega)
  have hcomm := Orb.allN_iff.1 ch442202_cand _ hc
  obtain ⟨e₁, he₁, hr₁⟩ := yt_rc R0 R1 hk hj1
  obtain ⟨e₂, he₂, hr₂⟩ := yt_rc R0 R1 hk hj2
  refine ⟨_, hk, elemW (wList.getD (8 + r32 GC g) []), Subgroup.mem_inf.2 ⟨elemW_mem _, ?_⟩,
    ?_, ?_, orb_card h1 h2 horb⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact comm_of hκ rc_az hcomm
  · rw [conj_of hκ h1 hr₁ hc1]
    exact he₁
  · rw [conj_of hκ h2 hr₂ hc2]
    exact he₂

theorem badZ_all : badAllK OZ.T 128 (r32 CIz 0) 16 32 YAz YBz (r32 Cz) = true := by
  have h := ch442202_badZ
  unfold badZ at h
  rwa [strictB_eq] at h

theorem badAZ_some : badSomeK OAZ.T 128 (r32 CIaz 0) 16 32 YAaz YBaz (r32 Caz) = true := by
  have h := ch442202_badAZ
  unfold badAZ at h
  rwa [strictB_eq] at h

theorem yFactsK : YFactsK := by
  obtain ⟨xz, Rz⟩ := rZ
  obtain ⟨xaz, Raz⟩ := rAZ
  obtain ⟨xy0, R0⟩ := rY0
  obtain ⟨xy1, R1⟩ := rY1
  have hGz : ∀ j < 6, RC (OZ.G j) (elemW (oGensZ.getD j [])) := fun j hj => by
    rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 gens_parts.1 j hj)]
    exact rc_word (lettZ j hj)
  have hGaz : ∀ j < 6, RC (OAZ.G j) (elemW (oGensAZ.getD j [])) := fun j hj => by
    rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 gens_parts.2.1 j hj)]
    exact rc_word (lettAZ j hj)
  have pz := centK_parts ch442202_centZ
  have paz := centK_parts ch442202_centAZ
  refine
    { z := centFactsK_of Rz (by decide) hGz rc_z rc_s₁ rc_s₂ (by decide)
        (fun c hc => W_rc_eq (by omega) (cz_eq c hc)) (W_rc_eq (by norm_num) (cz_eq 1 (by norm_num)))
        ch442202_centZ
      az := centFactsK_of Raz (by decide) hGaz rc_az rc_s₁ rc_s₂ (by decide)
        (fun c hc => W_rc_eq (by omega) (caz_eq c hc))
        (W_rc_eq (by norm_num) (caz_eq 0 (by norm_num))) ch442202_centAZ
      card_y₀ := R0.card
      card_y₁ := R1.card
      pairs_z := ?_
      pairs_az := ?_ }
  · exact pairs_of (P := PairBad (wSub oGensZ) elemZ) Rz rc_z rc_s₁ rc_s₂ ch442202_fltZ
      fun a ha b hb y₁ y₂ r1 r2 => bad_of Rz pz.2.1 pz.2.2.1 rc_z r1 r2 (badAll_at badZ_all ha hb)
  · refine pairs_of (P := fun y₁ y₂ => PairBad (wSub oGensAZ) (elemA * elemZ) y₁ y₂ ∨
      PairGood (elemA * elemZ) y₁ y₂) Raz rc_az rc_s₁ rc_s₂ ch442202_fltAZ
      fun a ha b hb y₁ y₂ r1 r2 => ?_
    by_cases hk : r32 Caz (a * 32 + b) < 1000
    · exact Or.inl (bad_of Raz paz.2.1 paz.2.2.1 rc_az r1 r2 (badSome_at badAZ_some ha hb hk))
    · exact Or.inr (good_of R0 R1 r1 r2 (good_at ha hb hk))

end CFSG.KD.HN1408.Y442202

end
