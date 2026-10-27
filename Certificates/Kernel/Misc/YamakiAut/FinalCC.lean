module

public import Certificates.Kernel.Misc.YamakiAut.FinalC
public import Certificates.Kernel.Misc.YamakiAut.ChecksC
public import CFSG.Certificates.Kernel.Misc.YamakiAmalgamFoldSound

public section

namespace CFSG.KD.YamakiAutM

open CFSG.KC.YamakiAutM CFSG.KC.YamakiAut CFSG.KD.YamakiAut CFSG.KD.YamakiRepF CFSG.KD.YamakiRep
  CFSG.KC.YamakiS0 CFSG.KC.YamakiA0 CFSG.KD.YamakiA0 CFSG.KD.BfsK CFSG.KC.BfsEnum
  CFSG.KC.YamakiRep CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.KD.YamakiAutC
  CFSG.KC.YamakiAmalgamFold
open CFSG.KD.Sp62 (MULF ONE)
open CFSG.KC.Misc.Spec (pkMat)

theorem compA_assoc {p q s : Array ℕ} (hs : ∀ i < 64, s[i]! < 64) :
    compA (compA p q) s = compA p (compA q s) :=
  ext64 (size_compA _ _) (size_compA _ _) fun i hi => by
    rw [compA_get _ _ hi, compA_get _ _ (hs i hi), compA_get _ _ hi, compA_get _ _ hi]

theorem idA_compA {t : Array ℕ} (ht : t.size = 64) (hb : ∀ i < 64, t[i]! < 64) :
    compA (idA ()) t = t :=
  ext64 (size_compA _ _) ht fun i hi => by rw [compA_get _ _ hi, idA_get (hb i hi)]

theorem arrN_inj_of {X Z : ℕ} (h : MULF Z X = ONE) :
    ∀ i < 64, ∀ j < 64, (arrN X)[i]! = (arrN X)[j]! → i = j := by
  have e : compA (arrN Z) (arrN X) = idA () := by rw [arrN_mul, h, arrN_one]
  intro i hi j hj hij
  have h1 : (compA (arrN Z) (arrN X))[i]! = (compA (arrN Z) (arrN X))[j]! := by
    rw [compA_get _ _ hi, compA_get _ _ hj, hij]
  rwa [e, idA_get hi, idA_get hj] at h1

theorem conj_of {X Z t u : ℕ} (h : MULF Z X = ONE) (e : MULF X u = MULF t X) :
    compA (compA (invA (arrN X)) (arrN t)) (arrN X) = arrN u := by
  have hb := fun i (hi : i < 64) => arrN_lt X hi
  have hi := arrN_inj_of h
  rw [compA_assoc hb, arrN_mul t X, ← e, ← arrN_mul X u, ← compA_assoc (fun i hi => arrN_lt u hi),
    invA_comp hb hi, idA_compA (arrN_size _) fun i hi => arrN_lt u hi]

theorem conj_to {X Z t : ℕ} {y : Array ℕ} (h : MULF Z X = ONE)
    (e : compA (compA (invA (arrN X)) (arrN t)) (arrN X) = y) :
    compA (arrN X) y = compA (arrN t) (arrN X) := by
  have hb := fun i (hi : i < 64) => arrN_lt X hi
  have hi := arrN_inj_of h
  rw [← e, ← compA_assoc hb, ← compA_assoc (fun i hi => arrN_lt t hi), comp_invA hb hi,
    idA_compA (arrN_size _) fun i hi => arrN_lt t hi]

theorem ya550712_ginv : MULF 22811959953 (RX 12) = ONE ∧ MULF 4701717328 (RX 13) = ONE := by
  decide +kernel

theorem invX : ∀ t < 1536, ∃ Z, MULF Z (recX RX 14 t) = ONE := by
  obtain ⟨-, -, h0, hB, -⟩ := enumX_repF
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    cases t with
    | zero =>
      refine ⟨ONE, ?_⟩
      rw [h0]
      exact CFSG.KC.Sp62.pkMat_inj (CFSG.KC.Sp62.MULF_lt _ _) ONE_lt (by
        rw [CFSG.KC.Sp62.pkMat_MULF, pkMat_ONE, mul_one])
    | succ i =>
      obtain ⟨b1, b2, b3⟩ := hB i (by omega)
      obtain ⟨Z, hZ⟩ := ih (recF RX 14 0 i) (by omega) (by omega)
      have hg : ∃ G, MULF G (RX (12 + recF RX 14 1 i)) = ONE := by
        rcases (by omega : recF RX 14 1 i = 0 ∨ recF RX 14 1 i = 1) with e | e
        · exact ⟨_, by rw [e]; exact ya550712_ginv.1⟩
        · exact ⟨_, by rw [e]; exact ya550712_ginv.2⟩
      obtain ⟨G, hG⟩ := hg
      refine ⟨MULF G Z, ?_⟩
      rw [b3]
      apply CFSG.KC.Sp62.pkMat_inj (CFSG.KC.Sp62.MULF_lt _ _) ONE_lt
      have e1 := congrArg (pkMat 6) hZ
      have e2 := congrArg (pkMat 6) hG
      rw [CFSG.KC.Sp62.pkMat_MULF, pkMat_ONE] at e1 e2
      rw [CFSG.KC.Sp62.pkMat_MULF, CFSG.KC.Sp62.pkMat_MULF, CFSG.KC.Sp62.pkMat_MULF, pkMat_ONE,
        mul_assoc, ← mul_assoc (pkMat 6 Z), e1, one_mul, e2]

theorem enumX_elem {i : ℕ} (hi : i < 1536) : (enumX ()).elems[i]! = arrN (recX RX 14 i) :=
  enumX_repF.1.2.2.2.1 i hi

theorem enumX_size : (enumX ()).elems.size = 1536 := enumX_repF.1.1

theorem ya550712_r1 : wordN (fun i => RX (12 + i)) [0] = cr0 ∧
    wordN (fun i => RX (12 + i)) [1, 1, 1, 0, 1, 1, 0, 1, 0, 1] = cr1 := by
  decide +kernel

theorem r1A_eq : r1A () = #[arrN cr0, arrN cr1] := by
  have e : r1A () = #[wordA (gX ()) [0], wordA (gX ()) [1, 1, 1, 0, 1, 1, 0, 1, 0, 1]] := rfl
  rw [e, wordA_gX _ (by decide), wordA_gX _ (by decide), ya550712_r1.1, ya550712_r1.2]

theorem ya550712_pc : ∀ k < 16, pc1.getD k 0 = (repC k).1 ∧ pc2.getD k 0 = (repC k).2 := by
  unfold repC
  decide +kernel

theorem ya550712_ex1 :
    tests1.map (fun w => decide (wordA #[(gX ())[0]!] w = idA ())) = [true, false] := by
  have h : ∀ w ∈ tests1, wordA #[(gX ())[0]!] w = arrN (wordN (fun _ => RX 12) w) := by
    intro w hw
    refine wordA_of _ _ w fun i hi => ?_
    have : i = 0 := by simp [tests1] at hw; rcases hw with rfl | rfl <;> simpa using hi
    subst this
    exact gX_get0
  have e : ∀ w ∈ tests1, decide (wordA #[(gX ())[0]!] w = idA ()) =
      Nat.beq (wordN (fun _ => RX 12) w) ONE := by
    intro w hw
    rw [h w hw, ← arrN_one, decide_arrN (wordN_lt _) ONE_lt]
  rw [List.map_congr_left e]
  decide +kernel

theorem ya550712_ex2 : tests2.map (fun w => decide (wordA (gX ()) w = idA ())) =
    [true, true, true, true] := by
  have e : ∀ w ∈ tests2, decide (wordA (gX ()) w = idA ()) =
      Nat.beq (wordN (fun i => RX (12 + i)) w) ONE := by
    intro w hw
    rw [wordA_gX _ (by simp [tests2] at hw; rcases hw with rfl | rfl | rfl | rfl <;> decide),
      ← arrN_one, decide_arrN (wordN_lt _) ONE_lt]
  rw [List.map_congr_left e]
  decide +kernel

theorem patt1_eq (Y : ℕ) : pattOK #[arrN Y] tests1 [true, false] = patt1 Y := by
  have h : ∀ w : List ℕ, (∀ i ∈ w, i = 0) →
      decide (wordA #[arrN Y] w = idA ()) = Nat.beq (wordN (fun _ => Y) w) ONE := by
    intro w hw
    rw [wordA_of _ (fun _ => Y) w (fun i hi => by rw [hw i hi]; rfl), ← arrN_one,
      decide_arrN (wordN_lt _) ONE_lt]
  unfold pattOK patt1
  simp only [tests1, List.zip_cons_cons, List.zip_nil_right, List.all_cons, List.all_nil]
  rw [h _ (by decide), h _ (by decide)]

theorem patt2_eq (c Y : ℕ) : pattOK #[arrN c, arrN Y] tests2 [true, true, true, true] =
    patt2 c Y ts2 := by
  have h : ∀ w : List ℕ, (∀ i ∈ w, i < 2) →
      decide (wordA #[arrN c, arrN Y] w = idA ()) =
        Nat.beq (wordN (CFSG.KD.YamakiAutC.cyOf c Y) w) ONE := by
    intro w hw
    rw [wordA_of _ (CFSG.KD.YamakiAutC.cyOf c Y) w (fun i hi => by
      rcases (by have := hw i hi; omega : i = 0 ∨ i = 1) with rfl | rfl
      · rfl
      · rfl), ← arrN_one, decide_arrN (wordN_lt _) ONE_lt]
  unfold pattOK
  simp only [tests2, ts2, patt2, List.zip_cons_cons, List.zip_nil_right, List.all_cons,
    List.all_nil, Bool.and_true]
  rw [h _ (by decide), h _ (by decide), h _ (by decide), h _ (by decide)]

theorem c1At_all : ∀ i < 1536, c1At RX HC1 1536 cr0 cr1 i = true := by
  intro i hi
  have e := CFSG.KC.Misc.Clos.forall_of_chunks 512 3
    (fun i => cond (Nat.blt i 1536) (c1At RX HC1 1536 cr0 cr1 i) true) (fun q hq => by
      have e := ch550712c1K.all q hq
      unfold ch550712c1 c1Chunk at e
      exact e) i (by omega)
  rw [Nat.blt_eq.mpr hi, cond_true] at e
  exact e

theorem c2At_all : ∀ i < 1536, c2At RX (fun k => pc1.getD k 0) (fun k => pc2.getD k 0) ts2 1536
    cr0 (HC2 i) i = true ∧ c2At RX (fun k => pc1.getD k 0) (fun k => pc2.getD k 0) ts2 1536 cr1
    (HC2 (Nat.add 1536 i)) i = true := by
  intro i hi
  have e := CFSG.KC.Misc.Clos.forall_of_chunks 512 3
    (fun i => cond (Nat.blt i 1536)
      (c2At RX (fun k => pc1.getD k 0) (fun k => pc2.getD k 0) ts2 1536 cr0 (HC2 i) i &&
        c2At RX (fun k => pc1.getD k 0) (fun k => pc2.getD k 0) ts2 1536 cr1
          (HC2 (Nat.add 1536 i)) i) true) (fun q hq => by
      have e := ch550712c2K.all q hq
      unfold ch550712c2 c2Chunk at e
      exact e) i (by omega)
  rw [Nat.blt_eq.mpr hi, cond_true, Bool.and_eq_true] at e
  exact e

theorem c1Check_holds : c1Check () = true := by
  unfold c1Check
  dsimp only
  rw [ya550712_ex1, r1A_eq, allLt_iff, enumX_size]
  intro i hi
  have h := c1At_all i hi
  unfold c1At at h
  simp only [CFSG.KC.YamakiRepF.strictY_eq] at h
  rw [enumX_elem hi, patt1_eq]
  generalize hh : HC1 i = h0 at h
  cases hp : patt1 (recX RX 14 i)
  · rfl
  rw [Bool.not_true, Bool.false_or]
  rcases Nat.eq_zero_or_pos h0 with rfl | hpos
  · rw [Nat.beq_refl, cond_true, hp] at h
    exact absurd h (by decide)
  have hb0 : Nat.beq h0 0 = false :=
    Bool.eq_false_iff.mpr fun e => by have := Nat.eq_of_beq_eq_true e; omega
  rw [hb0, cond_false, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hj, hc⟩ := h
  obtain ⟨Z, hZ⟩ := invX _ hj
  have hr2 : Nat.mod (Nat.pred h0) 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hr : (#[arrN cr0, arrN cr1] : Array (Array ℕ))[Nat.mod (Nat.pred h0) 2]! =
      arrN (cond (Nat.beq (Nat.mod (Nat.pred h0) 2) 0) cr0 cr1) := by
    have e2 : Nat.mod (Nat.pred h0) 2 = 0 ∨ Nat.mod (Nat.pred h0) 2 = 1 :=
      Nat.mod_two_eq_zero_or_one _
    rcases e2 with e | e <;> rw [e] <;> rfl
  have hkey : ((conjIndex1 (enumX ()) #[arrN cr0, arrN cr1])[arrN (recX RX 14 i)]?).isSome := by
    rw [conjIndex1_isSome]
    refine ⟨Nat.mod (Nat.pred h0) 2, by simpa using hr2, Nat.div (Nat.pred h0) 2,
      by rw [enumX_size]; exact hj, ?_⟩
    rw [enumX_elem hj, hr]
    exact conj_of hZ hc
  obtain ⟨⟨r, j'⟩, hv⟩ := Option.isSome_iff_exists.1 hkey
  obtain ⟨hr, hj', he⟩ := conjIndex1_get hv
  rw [enumX_size] at hj'
  simp only [hv, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hr, hj'⟩, ?_⟩
  rw [enumX_elem hj'] at he ⊢
  obtain ⟨Z', hZ'⟩ := invX j' hj'
  have hR : ∀ r < 2, ∃ c, (#[arrN cr0, arrN cr1] : Array (Array ℕ))[r]! = arrN c := by
    intro r hr
    rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  obtain ⟨c, hc'⟩ := hR r (by simpa using hr)
  rw [hc'] at he ⊢
  exact conj_to hZ' he

theorem c2Check_holds : c2Check () = true := by
  unfold c2Check
  dsimp only
  rw [ya550712_ex2, r1A_eq, allLt_iff]
  intro r hr
  rw [allLt_iff, enumX_size]
  intro i hi
  have hR : ∃ C H0, (#[arrN cr0, arrN cr1] : Array (Array ℕ))[r]! = arrN C ∧
      c2At RX (fun k => pc1.getD k 0) (fun k => pc2.getD k 0) ts2 1536 C H0 i = true := by
    have hr2 : r < 2 := by simpa using hr
    rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
    · exact ⟨_, _, rfl, (c2At_all i hi).1⟩
    · exact ⟨_, _, rfl, (c2At_all i hi).2⟩
  obtain ⟨C, h0, hRr, h⟩ := hR
  rw [hRr, enumX_elem hi, patt2_eq]
  unfold c2At at h
  simp only [CFSG.KC.YamakiRepF.strictY_eq] at h
  cases hp : patt2 C (recX RX 14 i) ts2
  · rfl
  rw [Bool.not_true, Bool.false_or]
  rcases Nat.eq_zero_or_pos h0 with rfl | hpos
  · rw [Nat.beq_refl, cond_true, hp] at h
    exact absurd h (by decide)
  have hb0 : Nat.beq h0 0 = false :=
    Bool.eq_false_iff.mpr fun e => by have := Nat.eq_of_beq_eq_true e; omega
  rw [hb0, cond_false, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq,
    Nat.beq_eq] at h
  obtain ⟨hj, hc1, hc2⟩ := h
  beta_reduce at hc1 hc2
  have hk : Nat.mod (Nat.pred h0) 16 < 16 := Nat.mod_lt _ (by norm_num)
  obtain ⟨Z, hZ⟩ := invX _ hj
  obtain ⟨p1, p2⟩ := ya550712_pc _ hk
  rw [p1] at hc1
  rw [p2] at hc2
  have hsz : (repsA ()).size = 16 := by simp [repsA, repWords]
  have hkey : ((conjIndex2 (enumX ()) (repsA ()))[(arrN C, arrN (recX RX 14 i))]?).isSome := by
    rw [conjIndex2_isSome]
    refine ⟨Nat.mod (Nat.pred h0) 16, by rw [hsz]; exact hk, Nat.div (Nat.pred h0) 16,
      by rw [enumX_size]; exact hj, ?_⟩
    rw [enumX_elem hj, repsA_get hk]
    dsimp only
    rw [conj_of hZ hc1, conj_of hZ hc2]
  obtain ⟨⟨k', j'⟩, hv⟩ := Option.isSome_iff_exists.1 hkey
  obtain ⟨hk', hj', he⟩ := conjIndex2_get hv
  rw [enumX_size] at hj'
  simp only [hv, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hk', hj'⟩, ?_⟩, ?_⟩
  all_goals rw [hsz] at hk'
  · rw [enumX_elem hj'] at he ⊢
    rw [repsA_get hk'] at he ⊢
    obtain ⟨Z', hZ'⟩ := invX j' hj'
    exact conj_to hZ' (Prod.mk.inj he).1
  · rw [enumX_elem hj'] at he ⊢
    rw [repsA_get hk'] at he ⊢
    obtain ⟨Z', hZ'⟩ := invX j' hj'
    exact conj_to hZ' (Prod.mk.inj he).2

end CFSG.KD.YamakiAutM

end
