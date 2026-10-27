module

public import Certificates.Kernel.TwoHS.F27020Q
public import Certificates.Kernel.TwoHS.HarGlue
public import CFSG.Certificates.Kernel.Spor.PackFld

public section

set_option maxRecDepth 400000

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KD.LQT.C4126
open CFSG.KS.MulH CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.TwoHS
open CFSG.Sporadic.Recognition.HSMultiplier

theorem sel2_eq (f : Fin 2 → Nat) : sel2 (f 0) (f 1) = f := by
  funext j
  fin_cases j <;> rfl

theorem sel6_eq (f : Fin 6 → Nat) : sel6 (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) = f := by
  funext j
  fin_cases j <;> rfl

theorem sel4_eq (f : Fin 4 → Nat) : sel4 (f 0) (f 1) (f 2) (f 3) = f := by
  funext j
  fin_cases j <;> rfl

theorem sel16_eq (f : Fin 16 → Nat) : sel16 (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8)
    (f 9) (f 10) (f 11) (f 12) (f 13) (f 14) (f 15) = f := by
  funext m
  fin_cases m <;> rfl

theorem bind2_eq (f : Fin 2 → Nat) (k : (Fin 2 → Nat) → Bool) : bind2 f k = k f := by
  unfold bind2
  simp only [CFSG.KS.PEnum.strictB_app']
  rw [sel2_eq]

theorem bind6_eq (f : Fin 6 → Nat) (k : (Fin 6 → Nat) → Bool) : bind6 f k = k f := by
  unfold bind6
  simp only [CFSG.KS.PEnum.strictB_app']
  rw [sel6_eq]

theorem bind4_eq (f : Fin 4 → Nat) (k : (Fin 4 → Nat) → Bool) : bind4 f k = k f := by
  unfold bind4
  simp only [CFSG.KS.PEnum.strictB_app']
  rw [sel4_eq]

theorem bind16_eq (f : Fin 16 → Nat) (k : (Fin 16 → Nat) → Bool) : bind16 f k = k f := by
  unfold bind16
  simp only [CFSG.KS.PEnum.strictB_app']
  rw [sel16_eq]

theorem ofFn_get {α : Type} [Inhabited α] {n : Nat} (f : Fin n → α) (j : Fin n) :
    (Array.ofFn f)[j.val]! = f j := by
  rw [getElem!_pos (Array.ofFn f) j.val (by simp)]
  simp

theorem prod_foldG {n w : Nat} {E : Fin 4 → Nat} {Et : Fin 4 → Table}
    (hE : ∀ l, Et l = tabT (unpack n w (E l)) ∧ canonK n w (mask w) (n * w) (E l) = true)
    (m : Nat) : ∀ (L : List (Fin 4)) (a : Nat), canonK n w (mask w) (n * w) a = true →
      L.foldl (fun acc l => if m.testBit l.val then compT n acc (Et l) else acc)
          (tabT (unpack n w a)) =
        tabT (unpack n w (L.foldl (fun acc l =>
          cond (m.testBit l.val) (pcomp n w (mask w) acc (E l)) acc) a)) ∧
      canonK n w (mask w) (n * w) (L.foldl (fun acc l =>
          cond (m.testBit l.val) (pcomp n w (mask w) acc (E l)) acc) a) = true
  | [], _, ha => ⟨rfl, ha⟩
  | l :: L, a, ha => by
    rw [List.foldl_cons, List.foldl_cons]
    cases hb : m.testBit l.val
    · rw [if_neg Bool.false_ne_true, cond_false]
      exact prod_foldG hE m L a ha
    · rw [if_pos rfl, cond_true, (hE l).1, compT_unpack ha (hE l).2]
      exact prod_foldG hE m L _ (CFSG.KC.BfsPin.canonK_pcomp ha (hE l).2)

theorem prod_eq {E : Fin 4 → Nat} {Et : Fin 4 → Table}
    (hE : ∀ l, Et l = tabT (unpack 11200 14 (E l)) ∧ Cn (E l)) (m : Nat) :
    hfxProd Et m = tabT (unpack 11200 14 (prodK E m)) ∧ Cn (prodK E m) := by
  unfold hfxProd prodK
  rw [idT_eq]
  exact prod_foldG hE m _ idK cId

theorem rho_lt (i : Fin 4) : [5, 12, 21, 34].getD i.val 0 < 43 := by
  fin_cases i <;> decide

theorem rho_parts (i : Fin 4) : hfxRho i = tabT (unpack 3850 12 (fxR i)) ∧ C3 (fxR i) :=
  ⟨CFSG.KD.HS3850.cent_tab (rho_lt i), CFSG.KD.HS3850.cent_cn (rho_lt i)⟩

@[expose] noncomputable def Tk (i : Fin 4) (j : Fin 6) : Nat := EVK HYF HYF (hfxW i j)

@[expose] noncomputable def Ak (i : Fin 4) (k : Fin 6) : Nat := EVK (Tk i) (Tk i) (hsCommWord k)

@[expose] noncomputable def Ek (i l : Fin 4) : Nat := EVK HYF HYF (hfxE i l)

@[expose] noncomputable def Fk (i l : Fin 4) : Nat := EVK (Ak i) (Ak i) (hfxE i l)

theorem ck_eq (i : Fin 4) :
    ck27020Q i = ckBodyQ idK (Tk i) (Ak i) (Ek i) (Fk i) (fun m => prodK (Ek i) m.val) := by
  unfold ck27020Q
  rw [CFSG.KS.PEnum.strictB_app', bind6_eq, bind6_eq, bind4_eq, bind4_eq, bind16_eq]
  rfl

theorem inv_of_sq {p : Nat} (hp : Cn p) (h : Nat.beq (pc p p) idK = true) :
    invEqK 11200 14 (mask 14) (11200 * 14) p p = true := by
  obtain ⟨hn, hw, h0, hlt⟩ := CFSG.KS.PF.canon_facts hp
  unfold invEqK CFSG.KC.Enum.permOK
  simp only [bAnd_iff]
  refine ⟨by simpa using h0, by simpa using h0, CFSG.KS.PackFld.allN_of_forall fun i hi => ?_⟩
  rw [CFSG.KS.PEnum.strictB_app']
  simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq]
  refine ⟨hlt i hi, ?_⟩
  unfold pc idK at h
  rw [← CFSG.KS.PF.pg_pcomp (by norm_num) hi, Nat.eq_of_beq_eq_true h]
  exact CFSG.KS.PF.pg_pidn hn hw hi

theorem ckR_of (h : ck27020R = true) :
    (∀ j, inv3 (XK j) (XK j) = true) ∧ ∀ i, ck3Body i XK (fxR i) = true := by
  unfold ck27020R at h
  rw [bind2_eq, bind2_eq, bind6_eq] at h
  simp only [CFSG.KS.PEnum.strictB_app', bAnd_iff, List.all_eq_true] at h
  exact ⟨fun j => h.1 j (List.mem_finRange j), fun i => h.2 i (List.mem_finRange i)⟩

theorem comm_of {E : Fin 4 → Nat}
    (h : ∀ l ∈ List.finRange 4, ∀ l' ∈ List.finRange 4,
      (Nat.ble l'.val l.val || Nat.beq (pc (E l) (E l')) (pc (E l') (E l))) = true)
    (l l' : Fin 4) : Nat.beq (pc (E l) (E l')) (pc (E l') (E l)) = true := by
  rcases lt_trichotomy l.val l'.val with hl | hl | hl
  · have h1 := h l (List.mem_finRange l) l' (List.mem_finRange l')
    simp only [Bool.or_eq_true, Nat.ble_eq] at h1
    rcases h1 with h1 | h1
    · omega
    · exact h1
  · rw [Fin.ext hl]
    exact Nat.beq_refl _
  · have h1 := h l' (List.mem_finRange l') l (List.mem_finRange l)
    simp only [Bool.or_eq_true, Nat.ble_eq] at h1
    rcases h1 with h1 | h1
    · omega
    · rw [Nat.eq_of_beq_eq_true h1]
      exact Nat.beq_refl _

theorem checkWith_of {i : Fin 4} {T TI A AI : Fin 6 → Table} {Et Ea : Fin 4 → Table}
    {P : Fin 16 → Table} (hX : ∀ j, inv3 (XK j) (XK j) = true)
    (hR : ck3Body i XK (fxR i) = true) (h : ck27020Q i = true)
    (hT : ∀ j, T j = evalW 11200 harY harYI (hfxW i j)) (hTI : ∀ j, TI j = invT 11200 (T j))
    (hA : ∀ k, A k = evalW 11200 T TI (hsCommWord k)) (hAI : ∀ k, AI k = invT 11200 (A k))
    (hEt : ∀ l, Et l = evalW 11200 harY harYI (hfxE i l))
    (hEa : ∀ l, Ea l = evalW 11200 A AI (hfxE i l)) (hP : ∀ m : Fin 16, P m = hfxProd Et m.val) :
    hfxCheckWith i T TI A AI Et Ea P = true := by
  rw [ck_eq] at h
  unfold ckBodyQ dist16 at h
  simp only [bAnd_iff, List.all_eq_true] at h
  obtain ⟨s4, s5, r6, r7, r8, r9⟩ := h
  unfold ck3Body at hR
  simp only [bAnd_iff, List.all_eq_true] at hR
  obtain ⟨r2, r3⟩ := hR
  have hTt : ∀ j, T j = tabT (unpack 11200 14 (Tk i j)) ∧ Cn (Tk i j) := fun j => by
    rw [hT]
    exact evalW_eq harY_parts harYI_parts _
  have r4 : ∀ j, invEqK 11200 14 (mask 14) (11200 * 14) (Tk i j) (Tk i j) = true := fun j =>
    inv_of_sq (hTt j).2 (s4 j (List.mem_finRange j))
  have hTIt : ∀ j, TI j = tabT (unpack 11200 14 (Tk i j)) ∧ Cn (Tk i j) := fun j => by
    rw [hTI, (hTt j).1]
    exact ⟨invT_eq (r4 j), (hTt j).2⟩
  have hAt : ∀ k, A k = tabT (unpack 11200 14 (Ak i k)) ∧ Cn (Ak i k) := fun k => by
    rw [hA]
    exact evalW_eq hTt hTIt _
  have r5 : ∀ k, invEqK 11200 14 (mask 14) (11200 * 14) (Ak i k) (Ak i k) = true := fun k =>
    inv_of_sq (hAt k).2 (s5 k (List.mem_finRange k))
  have hAIt : ∀ k, AI k = tabT (unpack 11200 14 (Ak i k)) ∧ Cn (Ak i k) := fun k => by
    rw [hAI, (hAt k).1]
    exact ⟨invT_eq (r5 k), (hAt k).2⟩
  have hEtt : ∀ l, Et l = tabT (unpack 11200 14 (Ek i l)) ∧ Cn (Ek i l) := fun l => by
    rw [hEt]
    exact evalW_eq harY_parts harYI_parts _
  have hEat : ∀ l, Ea l = tabT (unpack 11200 14 (Fk i l)) ∧ Cn (Fk i l) := fun l => by
    rw [hEa]
    exact evalW_eq hAt hAIt _
  have hPt : ∀ m : Fin 16, P m = tabT (unpack 11200 14 (prodK (Ek i) m.val)) ∧
      Cn (prodK (Ek i) m.val) := fun m => by
    rw [hP]
    exact prod_eq hEtt m.val
  obtain ⟨eR, cR⟩ := rho_parts i
  have iR : invT 3850 (hfxRho i) = tabT (unpack 3850 12 (fxR i)) := by
    rw [eR]
    exact invT_unpack (by norm_num) r2
  have hXI : ∀ j, harXI j = tabT (unpack 3850 12 (XK j)) ∧ C3 (XK j) := fun j => by
    refine ⟨?_, (harX_parts j).2⟩
    unfold harXI
    rw [(harX_parts j).1]
    exact invT_unpack (by norm_num) (hX j)
  unfold hfxCheckWith
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [eR]
    exact permOK_unpack cR r2
  · rw [iR, eR]
    exact invOK_unpack cR cR r2
  · intro j _
    obtain ⟨e, c⟩ := evalW3_eq harX_parts hXI (hfxW i j)
    obtain ⟨eX, cX⟩ := harX_parts j
    have c1 := CFSG.KC.BfsPin.canonK_pcomp cR cX
    rw [e, iR, eR, eX, compT_unpack cR cX, compT_unpack c1 cR,
      tblEq_unpack c (CFSG.KC.BfsPin.canonK_pcomp c1 cR)]
    exact r3 j (List.mem_finRange j)
  · intro j _
    rw [(hTIt j).1, (hTt j).1]
    exact invOK_unpack (hTt j).2 (hTt j).2 (r4 j)
  · intro k _
    rw [(hAIt k).1, (hAt k).1]
    exact invOK_unpack (hAt k).2 (hAt k).2 (r5 k)
  · intro l _
    rw [(hEtt l).1, (hEat l).1, tblEq_eq (hEtt l).2 (hEat l).2]
    exact r6 l (List.mem_finRange l)
  · intro l _
    rw [(hEtt l).1, comp_eq (hEtt l).2 (hEtt l).2, idT_eq,
      tblEq_eq (cPc (hEtt l).2 (hEtt l).2) cId]
    exact r7 l (List.mem_finRange l)
  · intro l _ l' _
    rw [(hEtt l).1, (hEtt l').1, comp_eq (hEtt l).2 (hEtt l').2, comp_eq (hEtt l').2 (hEtt l).2,
      tblEq_eq (cPc (hEtt l).2 (hEtt l').2) (cPc (hEtt l').2 (hEtt l).2)]
    exact comm_of r8 l l'
  · intro a _ b _
    obtain ⟨ea, ca⟩ := hPt a
    obtain ⟨eb, cb⟩ := hPt b
    rw [ea, eb, tblEq_eq ca cb]
    exact r9 a (List.mem_finRange a) b (List.mem_finRange b)

theorem hfxCheck_of (hR : ck27020R = true) {i : Fin 4} (h : ck27020Q i = true) :
    hfxCheck i = true := by
  obtain ⟨hX, hRi⟩ := ckR_of hR
  unfold hfxCheck
  refine checkWith_of hX (hRi i) h ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intro x <;> simp only [ofFn_get] <;> rfl

theorem hfxOK_of (hR : ck27020R = true) (h : ∀ i, ck27020Q i = true) : hfxOK = true := by
  unfold hfxOK
  rw [List.all_eq_true]
  intro i _
  exact hfxCheck_of hR (h i)

end CFSG.KD.TwoHS

end
