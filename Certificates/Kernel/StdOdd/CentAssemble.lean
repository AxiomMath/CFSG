module

public import Certificates.Kernel.StdOdd.CentChecks
public import Certificates.Kernel.StdOdd.CentForm

set_option maxRecDepth 20000

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KS.StdOdd.Orbit CFSG.KS.StdOdd.Chain
  CFSG.KD.StdOdd.Orbit CFSG.KC.Misc.E6Std CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.Existence.StdOdd.Cert Matrix CFSG.KC.LQT.P

structure CentData where
  p : ℕ
  xw : List (ℕ × Bool)
  d0 : List (ℕ × Bool)
  eL : List ℕ
  K1 : List (ℕ × ℕ)
  Kall : List (ℕ × ℕ)
  prog : List (List ℕ)
  V : List ℕ
  bv : ℕ
  βs : List ℕ
  FP : ℕ → ℕ
  WN : ℕ → ℕ
  nf : ℕ → ℕ
  Df : ℕ → ℕ
  RI : ℕ → List ℕ
  LI : List ℕ
  HI : List (List ℕ)
  CP : ℕ
  HW : ℕ
  s : ℕ
  hD : ℕ
  m₀ : ℕ
  reps : List ℕ
  st : List ℕ
  R0 : ℕ
  r0D : ℕ
  cnts : List ℕ

namespace CentData

variable (D : CentData)

@[expose] noncomputable def xB (A B : ℕ) : ℕ := wordB A B D.xw

@[expose] noncomputable def FL (j : ℕ) : List ℕ :=
  splitPl (D.FP j) (Nat.div (Nat.add (D.nf j) 7) 8) (D.nf j) 156

@[expose] noncomputable def levOK (j : ℕ) : Bool :=
  andB (allL (D.RI j) fun r => andB (Nat.blt r (lenN D.V)) (fixesOK (nthV D.V r) D.βs j))
    (forestOK (D.FP j) (D.WN j) (Nat.div (Nat.add (D.nf j) 7) 8) (D.nf j) (D.Df j)
      ((D.RI j).map (nthV D.V)) (nthN D.βs j))

@[expose] noncomputable def chunkF (PL : List ℕ) (A B q : ℕ) : Bool :=
  chunkOK PL 3968055 (D.xB A B) (D.K1.map Prod.fst) (D.K1.map Prod.snd) Form.fmPk Form.brPk D.cnts q

@[expose] noncomputable def baseOK (A B : ℕ) : Bool :=
  andB (andB (andB (andB (Nat.beq (neqV (mapRows (wordB A B D.d0) (vecsPl [2 ^ 14])) D.bv 1) 0)
    (allN D.p fun j => Nat.beq (neqV (mapRows (powB (D.xB A B) (nthN D.eL j)) (vecsPl [D.bv]))
      (nthN D.βs j) 1) 0))
    (Nat.beq (lenN D.βs) D.p))
    (Nat.beq (profAll (D.xB A B) (D.K1.map Prod.fst) (D.K1.map Prod.snd) (vecsPl [D.bv]) 1
      Form.fmPk Form.brPk) (full 1)))
    (Nat.beq (profAll (D.xB A B) (D.Kall.map Prod.fst) (D.Kall.map Prod.snd) (vecsPl [D.bv]) 1
      Form.fmPk Form.brPk) (full 1))

@[expose] noncomputable def LOK (A B : ℕ) : Bool :=
  allL D.LI fun r => andB (Nat.blt r (lenN D.V)) (andB
    (Nat.beq (mulB (nthV D.V r) (D.xB A B)) (mulB (D.xB A B) (nthV D.V r)))
    (fixesOK (nthV D.V r) D.βs D.p))

@[expose] noncomputable def HOK (A B : ℕ) : Bool :=
  CFSG.KC.Misc.allLL D.HI fun line => andB (allL line fun r => Nat.blt r (lenN D.V))
    (Nat.beq (mulB (lineB D.V line) (D.xB A B)) (mulB (D.xB A B) (lineB D.V line)))

@[expose] noncomputable def hLet (A B : ℕ) : List ℕ :=
  powB (D.xB A B) (Nat.sub D.p 1) :: D.HI.map (lineB D.V)

@[expose] noncomputable def candF (A B : ℕ) : Bool :=
  candOK D.CP D.HW (Nat.div (Nat.add D.s 7) 8) D.s (D.xB A B) D.hD D.bv D.m₀ Form.fmPk
    (D.K1.map Prod.fst) (D.K1.map Prod.snd) (D.Kall.map Prod.fst) (D.Kall.map Prod.snd) Form.brPk
    (D.hLet A B) D.reps D.st

@[expose] noncomputable def startF (A B : ℕ) : Bool :=
  startOK D.R0 (Nat.div (Nat.add (lenN D.reps) 7) 8) D.r0D A B D.bv D.reps

@[expose] noncomputable def ckP (ck k : ℕ) : List ℕ :=
  Nat.casesOn (motive := fun _ => List ℕ) k (vecsPl D.reps) fun j =>
    splitPl (Nat.shiftRight ck (Nat.mul (Nat.mul 1248 (Nat.div (Nat.add (lenN D.reps) 7) 8)) j))
      (Nat.div (Nat.add (lenN D.reps) 7) 8) (lenN D.reps) 156

@[expose] noncomputable def segF (A B ck m k : ℕ) : Bool :=
  walkK [A, B] (stepsPl (Nat.shiftRight D.R0 (Nat.mul (Nat.mul 320
      (Nat.div (Nat.add (lenN D.reps) 7) 8)) k)) (Nat.div (Nat.add (lenN D.reps) 7) 8)
      (lenN D.reps) (Nat.min 20 (Nat.sub D.r0D (Nat.mul 20 k))) 2) (D.ckP ck k) fun V =>
    Bool.rec (motive := fun _ => Bool) (Nat.beq (neqMask V (D.ckP ck (Nat.succ k))) 0)
      (Nat.beq (neqV V D.bv (lenN D.reps)) 0) (Nat.beq (Nat.succ k) m)

@[expose] noncomputable def CL : List ℕ := splitPl D.CP (Nat.div (Nat.add D.s 7) 8) D.s 156

@[expose] noncomputable def candIni (A B : ℕ) : Bool :=
  andB (sortOK D.CL D.s) (Nat.beq (profAll (D.xB A B) (D.K1.map Prod.fst) (D.K1.map Prod.snd) D.CL
    D.s Form.fmPk Form.brPk) (full D.s))

@[expose] noncomputable def candEnd (A B : ℕ) (V : List ℕ) : Bool :=
  forceB (profAll (D.xB A B) (D.Kall.map Prod.fst) (D.Kall.map Prod.snd) D.CL D.s Form.fmPk
    Form.brPk) fun A' =>
  andB (andB (allIn V D.reps D.s) (popK (eqMaskV V D.bv D.s) D.m₀))
    (Nat.beq (Nat.land A' (andNot (andNot (full D.s) (eqMaskV V D.bv D.s)) (refMask V D.reps D.st D.s)))
      0)

@[expose] noncomputable def ccP (cc k : ℕ) : List ℕ :=
  Nat.casesOn (motive := fun _ => List ℕ) k D.CL fun j =>
    splitPl (Nat.shiftRight cc (Nat.mul (Nat.mul 1248 (Nat.div (Nat.add D.s 7) 8)) j))
      (Nat.div (Nat.add D.s 7) 8) D.s 156

@[expose] noncomputable def csegF (A B cc g m k : ℕ) : Bool :=
  walkK (D.hLet A B) (stepsPl (Nat.shiftRight D.HW (Nat.mul (Nat.mul (Nat.mul 8
      (Nat.div (Nat.add D.s 7) 8)) (lenN (D.hLet A B))) (Nat.mul g k)))
      (Nat.div (Nat.add D.s 7) 8) D.s (Nat.min g (Nat.sub D.hD (Nat.mul g k)))
      (lenN (D.hLet A B))) (D.ccP cc k) fun V =>
    Bool.rec (motive := fun _ => Bool) (Nat.beq (neqMask V (D.ccP cc (Nat.succ k))) 0)
      (D.candEnd A B V) (Nat.beq (Nat.succ k) m)

@[expose] def e (i : ℕ) : ℕ := D.eL.getD i 0

@[expose] def bK : Fin 78 → K := wM D.d0 *ᵥ Pi.single 7 1

@[expose] def βK (i : ℕ) : Fin 78 → K := wM D.xw ^ D.e i *ᵥ D.bK

@[expose] def regK (i : ℕ) : List M78 := (D.RI i).map (vM D.prog)

@[expose] noncomputable def BlK (i : ℕ) : Finset (Fin 78 → K) :=
  (Finset.range (D.nf i)).image (ptK (D.FL i))

@[expose] def RefFact (v : Fin 78 → K) : Prop :=
  ∃ g ∈ monAB, g *ᵥ v = D.bK ∧ SiftFails D.p D.βK D.regK D.BlK (fun i => g *ᵥ (wM D.xw ^ D.e i *ᵥ v))

end CentData

theorem prof_K {X : ℕ} {M : M78} (hX : Rep X M) {U : List ℕ} (hl : lenN U = 156) (w : ℕ)
    (K : List (ℕ × ℕ)) (hts : ∀ q ∈ K, q.2 = 0 ∨ q.2 = 3 ∨ q.2 = 4 ∨ q.2 = 5) (i : ℕ) :
    (profAll X (K.map Prod.fst) (K.map Prod.snd) U w Form.fmPk Form.brPk).testBit i = true ↔
      i < w ∧ ∀ q ∈ K, rhoC (ptK U i) (M ^ q.1 *ᵥ ptK U i) = q.2 := by
  rw [profAll_sound X hl w _ _ i _ _ (lenN_map_fst_snd K) (fun t ht => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ht
    exact hts q hq)]
  refine and_congr_right fun _ => ?_
  rw [← forall_zip_iff (P := fun a b => rhoC (ptK U i) (M ^ a *ᵥ ptK U i) = b) K]
  refine forall₂_congr fun l _ => ?_
  rw [rhoB_eq hl (lenN_mapRows _ _), ptK_mapRows hl (rep_powB hX _)]

theorem testBit_lt_of {x w : ℕ} (h : ∀ i, x.testBit i = true → i < w) : x < 2 ^ w :=
  Nat.lt_pow_two_of_testBit x fun i hi => by
    cases e : x.testBit i
    · rfl
    · exact absurd (h i e) (by omega)

theorem ptK_eq_iff_vecB {U : List ℕ} {i v : ℕ} : ptB U i = vecB v ↔ ptK U i = vecK v :=
  ⟨ptK_eq_vecK, fun h => by rw [← flat_ptK, h, flat_vecK]⟩

theorem allLL_true {L : List (List ℕ)} {f : List ℕ → Bool} (h : CFSG.KC.Misc.allLL L f = true) :
    ∀ x ∈ L, f x = true := by
  induction L with
  | nil => intro x hx; cases hx
  | cons y L ih =>
    change andB (f y) (CFSG.KC.Misc.allLL L f) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact ih h.2 x hx


theorem ptK_of_mat {U V : List ℕ} {i : ℕ} {W : Matrix (Fin 156) (Fin 156) (ZMod 2)} {g : M78}
    (hV : ptB V i = W *ᵥ ptB U i) (hg : blowM g = W) : ptK V i = g *ᵥ ptK U i :=
  flat_inj (by rw [flat_ptK, hV, flat_mulVec, hg, flat_ptK])

theorem lenN_pickL (O : List ℕ) : ∀ e : List ℕ, (pickL O e).length = e.length
  | [] => rfl
  | _ :: e => congrArg Nat.succ (lenN_pickL O e)

theorem nthN_pickL (O : List ℕ) : ∀ (e : List ℕ) (i : ℕ), i < e.length →
    nthN (pickL O e) i = nthN O (nthN e i)
  | [], i, h => absurd h (by simp)
  | _ :: e, 0, _ => rfl
  | _ :: e, i + 1, h => nthN_pickL O e i (by simp at h; omega)

theorem dropLast_eq : ∀ O : List ℕ, dropLast O = O.dropLast
  | [] => rfl
  | [_] => rfl
  | x :: y :: O => by
    change x :: dropLast (y :: O) = _
    rw [dropLast_eq (y :: O)]
    rfl

theorem nthN_tail : ∀ (O : List ℕ) (k : ℕ), nthN O.tail k = nthN O (k + 1)
  | [], _ => rfl
  | _ :: _, _ => rfl

theorem nthN_dropLast {O : List ℕ} {k : ℕ} (hk : k + 1 < O.length) : nthN O.dropLast k = nthN O k := by
  have h1 : k < O.dropLast.length := by rw [List.length_dropLast]; omega
  rw [nthN_eq_getD, nthN_eq_getD, List.getD_eq_getElem _ _ h1, List.getElem_dropLast,
    List.getD_eq_getElem _ _ (by omega)]

theorem tailL_eq : ∀ O : List ℕ, tailL O = O.tail
  | [] => rfl
  | _ :: _ => rfl

theorem spreadL_eq (w : ℕ) : ∀ Sr : List (List (List ℕ)),
    List.rec (motive := fun _ => List (List (List ℕ))) List.nil
      (fun S _ ih => List.cons (spreadS S 1 w) ih) Sr = Sr.map fun S => spreadS S 1 w
  | [] => rfl
  | S :: Sr => congrArg (List.cons _) (spreadL_eq w Sr)

theorem getD_spread (w : ℕ) : ∀ (Sr : List (List (List ℕ))) (l : ℕ),
    (Sr.map fun S => spreadS S 1 w).getD l [] = spreadS (Sr.getD l []) 1 w
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: Sr, l + 1 => getD_spread w Sr l

theorem walkElt_spread1 (Ms : List ℕ) (S : List (List ℕ)) {w i : ℕ} (hi : i < w) :
    walkElt Ms (spreadS S 1 w) i = walkElt Ms (spreadS S 1 w) 0 := by
  have h1 := walkElt_spread Ms 1 w i 0 Nat.one_pos hi S
  have h2 := walkElt_spread Ms 1 w 0 0 Nat.one_pos (by omega) S
  simp only [Nat.mul_one, Nat.add_zero, Nat.zero_mul] at h1 h2
  rw [h1, h2]

theorem refFact_of_refOK (D : CentData) {A B : ℕ} (hA : Rep A (toMat nativeAB.1))
    (hB : Rep B (toMat nativeAB.2)) (hV : ∀ i < lenN D.V, Rep (nthV D.V i) (vM D.prog i))
    (hRI : ∀ j, 1 ≤ j → j < D.p → ∀ r ∈ D.RI j, r < lenN D.V)
    (hβv : ∀ j < D.p, vecK (nthN D.βs j) = D.βK j) (heL : D.eL.length = D.p)
    (helt : ∀ i < D.p, D.e i < D.p) (he0 : D.e 0 = 0)
    {O : List ℕ} {Sr : List (List (List ℕ))} {m : ℕ} (hm1 : 1 ≤ m) (hmp : m < D.p)
    (hO : O.length = D.p)
    (h : refOK (D.xB A B) A B O D.eL ((List.range (m - 1)).map fun l => (D.RI (l + 1)).map (nthV D.V))
      Sr D.βs (D.FP m) (D.nf m) m = true) :
    D.RefFact (vecK (nthN O 0)) := by
  have hX : Rep (D.xB A B) (wM D.xw) := rep_wM hA hB D.xw
  unfold refOK at h
  rw [andB_eq, Bool.and_eq_true, spreadL_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hstep : ∀ k, k + 1 < O.length → wM D.xw *ᵥ vecK (nthN O k) = vecK (nthN O (k + 1)) := by
    intro k hk
    have hb := congrArg (fun x => x.testBit k) (Nat.eq_of_beq_eq_true h1)
    simp only [Nat.zero_testBit] at hb
    rw [neqMask_sound (by rw [lenN_mapRows, lenN_vecsPl]), Bool.not_eq_false'] at hb
    have he := (eqB_iff (lenN_mapRows _ _) (lenN_vecsPl _) k).1 hb
    have hk1 : k < (dropLast O).length := by rw [dropLast_eq, List.length_dropLast]; omega
    have hk2 : k < (tailL O).length := by rw [tailL_eq, List.length_tail]; omega
    have he' := ptB_inj he
    rw [ptK_mapRows (lenN_vecsPl _) hX, ptK_vecsPl _ hk1, ptK_vecsPl _ hk2] at he'
    rwa [dropLast_eq, tailL_eq, nthN_dropLast hk, nthN_tail] at he'
  have hpow : ∀ k < O.length, vecK (nthN O k) = wM D.xw ^ k *ᵥ vecK (nthN O 0) := by
    intro k hk
    induction k with
    | zero => rw [pow_zero, Matrix.one_mulVec]
    | succ k ih =>
      rw [← hstep k hk, ih (by omega), Matrix.mulVec_mulVec, ← pow_succ']
  set v := vecK (nthN O 0) with hv
  set T0 := vecsPl (pickL O D.eL) with hT0
  have hT0p : ∀ i < D.p, ptK T0 i = wM D.xw ^ D.e i *ᵥ v := by
    intro i hi
    have hi' : i < (pickL O D.eL).length := by rw [lenN_pickL, heL]; exact hi
    rw [hT0, ptK_vecsPl _ hi', nthN_pickL _ _ _ (by rw [heL]; exact hi), hpow _ (by
      rw [hO, nthN_eq_getD]; exact helt i hi), nthN_eq_getD]
    rfl
  obtain ⟨Tl, h0, hlen, hend, hlev⟩ := siftK_sound _ _ 0 T0 (lenN_vecsPl _) h2
  have hLsl : (([A, B] : List ℕ) :: (List.range (m - 1)).map fun l =>
      (D.RI (l + 1)).map (nthV D.V)).length = m := by simp; omega
  rw [hLsl] at hend
  have hlevl : ∀ l, 1 ≤ l → l < m → (([A, B] : List ℕ) :: (List.range (m - 1)).map fun l =>
      (D.RI (l + 1)).map (nthV D.V)).getD l [] = (D.RI l).map (nthV D.V) := by
    intro l h1 h2
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    rw [List.getD_cons_succ, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map,
      List.getElem_range]
  set w := lenN D.eL with hw
  have hwp : w = D.p := by rw [hw, CFSG.KS.StdOdd.Chain.lenN_eq_length, heL]
  have hel : ∀ l < m, ∀ i < D.p, ptB (Tl (l + 1)) i =
      walkElt ((([A, B] : List ℕ) :: (List.range (m - 1)).map fun l =>
        (D.RI (l + 1)).map (nthV D.V)).getD l []) (spreadS (Sr.getD l []) 1 w) 0 *ᵥ ptB (Tl l) i := by
    intro l hl i hi
    rw [(hlev l (by rw [hLsl]; exact hl)).1 i, getD_spread, walkElt_spread1 _ _ (by rw [hwp]; exact hi)]
  have hlen0 : lenN [A, B] = [toMat nativeAB.1, toMat nativeAB.2].length := rfl
  have hrep0 : ∀ l < lenN [A, B], Rep (nthN [A, B] l) ([toMat nativeAB.1, toMat nativeAB.2].getD l 0) := by
    intro l hl
    change l < 2 at hl
    rcases l with _ | _ | l
    · exact hA
    · exact hB
    · omega
  obtain ⟨g0, hg0, hge0⟩ := walk_lift hlen0 hrep0 (spreadS (Sr.getD 0 []) 1 w) 0
  have hp0 : 0 < D.p := Nat.lt_of_le_of_lt (Nat.zero_le m) hmp
  have ht1 : ∀ i < D.p, ptK (Tl 1) i = g0 *ᵥ (wM D.xw ^ D.e i *ᵥ v) := by
    intro i hi
    rw [← hT0p i hi, ← h0]
    exact ptK_of_mat (hel 0 (by omega) i hi) hge0
  have hb0 : ptK (Tl 1) 0 = D.βK 0 := by
    have := (hlev 0 (by rw [hLsl]; omega)).2
    rw [Nat.zero_add] at this
    rw [ptK_eq_vecK this, hβv 0 hp0]
  have hf : ∀ j, 1 ≤ j → j < m → ∃ f ∈ monL (D.regK j), ∀ i < D.p,
      ptK (Tl (j + 1)) i = f *ᵥ ptK (Tl j) i := by
    intro j hj1 hjm
    obtain ⟨hl, hr⟩ := rep_letters hV (D.RI j) (hRI j hj1 (by omega))
    obtain ⟨f, hfm, hfe⟩ := walk_lift hl hr (spreadS (Sr.getD j []) 1 w) 0
    refine ⟨f, hfm, fun i hi => ptK_of_mat ?_ hfe⟩
    rw [hel j hjm i hi, hlevl j hj1 hjm]
  choose! f hfm hfe using hf
  refine ⟨g0, monL_AB hg0, ?_, m, fun j i => ptK (Tl j) i, f, hm1, hmp, ht1, hb0,
    fun j hj1 hjm => ⟨hfm j hj1 hjm, ?_, hfe j hj1 hjm⟩, ?_⟩
  · have := ht1 0 hp0
    rw [he0, pow_zero, Matrix.one_mulVec, hb0] at this
    rw [← this]
    simp [CentData.βK, he0]
  · rw [← hfe j hj1 hjm j (by omega)]
    have := (hlev j (by rw [hLsl]; exact hjm)).2
    rw [Nat.zero_add] at this
    rw [ptK_eq_vecK this, hβv j (by omega)]
  ·
    intro hmem
    obtain ⟨k, hk, hke⟩ := Finset.mem_image.1 hmem
    have hb : ((memMask (Tl m) (D.FL m) (D.nf m) (m + 1)) &&& (1 <<< m)).testBit m = false :=
      (congrArg (fun x => x.testBit m) (Nat.eq_of_beq_eq_true hend)).trans (Nat.zero_testBit m)
    rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.sub_self, one_testBit] at hb
    simp only [ge_iff_le, le_refl, decide_true, Bool.true_and, Bool.and_true] at hb
    have hFL : lenN (D.FL m) = 156 := lenN_splitPl _ _ _ _
    have hmm := (memMask_sound (hlen m) hFL (D.nf m) (m + 1) m).2
      ⟨by omega, k, Finset.mem_range.1 hk, (ptK_inj hke).symm⟩
    rw [hmm] at hb
    simp at hb

theorem walkAB_sound {A B : ℕ} (hA : Rep A (toMat nativeAB.1)) (hB : Rep B (toMat nativeAB.2))
    {S : List (List ℕ)} {U : List ℕ} {k : List ℕ → Bool} (hU : lenN U = 156)
    (h : walkK [A, B] S U k = true) :
    ∃ V, k V = true ∧ lenN V = 156 ∧ ∀ i, ∃ g ∈ monAB, ptK V i = g *ᵥ ptK U i := by
  obtain ⟨V, hk, hV, hpt⟩ := walkK_sound _ _ hU h
  have hlen : lenN [A, B] = [toMat nativeAB.1, toMat nativeAB.2].length := rfl
  have hrep : ∀ l < lenN [A, B],
      Rep (nthN [A, B] l) ([toMat nativeAB.1, toMat nativeAB.2].getD l 0) := by
    intro l hl
    change l < 2 at hl
    rcases l with _ | _ | l
    · exact hA
    · exact hB
    · omega
  refine ⟨V, hk, hV, fun i => ?_⟩
  obtain ⟨g, hg, hge⟩ := walk_lift hlen hrep S i
  exact ⟨g, monL_AB hg, ptK_walk (hpt i) hge⟩

theorem ptK_of_neqMask {U V : List ℕ} (hU : lenN U = 156) (hV : lenN V = 156)
    (h : Nat.beq (neqMask U V) 0 = true) (i : ℕ) : ptK U i = ptK V i := by
  apply ptB_inj
  have he := neqMask_sound (hU.trans hV.symm) i
  rw [Nat.eq_of_beq_eq_true h, Nat.zero_testBit] at he
  exact (eqB_iff hU hV i).1 (by cases h' : eqB U V i <;> simp_all)

theorem walk_chain {v : ℕ → Fin 78 → K} : ∀ m : ℕ,
    (∀ k < m, ∃ g ∈ monAB, v (k + 1) = g *ᵥ v k) → ∃ g ∈ monAB, v m = g *ᵥ v 0
  | 0, _ => ⟨1, Submonoid.one_mem _, by rw [Matrix.one_mulVec]⟩
  | m + 1, h => by
    obtain ⟨g, hg, hge⟩ := walk_chain m fun k hk => h k (by omega)
    obtain ⟨g', hg', hge'⟩ := h m (by omega)
    exact ⟨g' * g, Submonoid.mul_mem _ hg' hg, by rw [hge', hge, Matrix.mulVec_mulVec]⟩

theorem lenN_ckP (D : CentData) (ck : ℕ) : ∀ k, lenN (D.ckP ck k) = 156
  | 0 => lenN_vecsPl _
  | _ + 1 => by
    unfold CentData.ckP
    exact lenN_splitPl _ _ _ _

theorem segF_sound (D : CentData) {A B ck m k : ℕ} (hA : Rep A (toMat nativeAB.1))
    (hB : Rep B (toMat nativeAB.2)) (h : D.segF A B ck m k = true) (i : ℕ) :
    ∃ g ∈ monAB, (k + 1 ≠ m → ptK (D.ckP ck (k + 1)) i = g *ᵥ ptK (D.ckP ck k) i) ∧
      (k + 1 = m → i < lenN D.reps → vecK D.bv = g *ᵥ ptK (D.ckP ck k) i) := by
  obtain ⟨V, hk, hV, hpt⟩ := walkAB_sound hA hB (lenN_ckP D ck k) h
  obtain ⟨g, hg, hge⟩ := hpt i
  refine ⟨g, hg, fun hm => ?_, fun hm hi => ?_⟩
  · have hb : Nat.beq (Nat.succ k) m = false := beq_false_of_ne' hm
    rw [hb] at hk
    rw [← hge]
    exact (ptK_of_neqMask hV (lenN_ckP D ck _) hk i).symm
  · have hb : Nat.beq (Nat.succ k) m = true := by
      rw [← hm]
      exact Nat.beq_refl _
    rw [hb] at hk
    rw [← hge]
    exact (ptK_of_neqV hV hk hi).symm

theorem start_of_startF (D : CentData) {A B : ℕ} (hA : Rep A (toMat nativeAB.1))
    (hB : Rep B (toMat nativeAB.2)) (hstart : D.startF A B = true) :
    ∀ r < lenN D.reps, ∃ g ∈ monAB, g *ᵥ vecK (nthN D.reps r) = vecK D.bv := by
  intro r hr
  unfold CentData.startF startOK at hstart
  obtain ⟨V, hk, hV, hpt⟩ := walkAB_sound hA hB (lenN_vecsPl _) hstart
  obtain ⟨g, hg, hge⟩ := hpt r
  have hr' : r < D.reps.length := by rw [← CFSG.KS.StdOdd.Chain.lenN_eq_length]; exact hr
  exact ⟨g, hg, by rw [← ptK_vecsPl D.reps hr', ← hge, ptK_of_neqV hV hk hr]⟩

theorem start_of_segs (D : CentData) {A B ck m : ℕ} (hA : Rep A (toMat nativeAB.1))
    (hB : Rep B (toMat nativeAB.2)) (hm : 0 < m) (h : ∀ k < m, D.segF A B ck m k = true) :
    ∀ r < lenN D.reps, ∃ g ∈ monAB, g *ᵥ vecK (nthN D.reps r) = vecK D.bv := by
  intro r hr
  obtain ⟨g, hg, hge⟩ := walk_chain (v := fun k => ptK (D.ckP ck k) r) (m - 1) fun k hk => by
    obtain ⟨g, hg, h1, -⟩ := segF_sound D hA hB (h k (by omega)) r
    exact ⟨g, hg, h1 (by omega)⟩
  obtain ⟨g', hg', -, h2⟩ := segF_sound D hA hB (h (m - 1) (by omega)) r
  have hr' : r < D.reps.length := by rw [← CFSG.KS.StdOdd.Chain.lenN_eq_length]; exact hr
  have h0 : ptK (D.ckP ck 0) r = vecK (nthN D.reps r) := ptK_vecsPl D.reps hr'
  refine ⟨g' * g, Submonoid.mul_mem _ hg' hg, ?_⟩
  rw [← Matrix.mulVec_mulVec, ← h0, ← hge]
  exact (h2 (by omega) hr).symm

theorem walkElt_append (Ms : List ℕ) (i : ℕ) : ∀ S₁ S₂ : List (List ℕ),
    walkElt Ms (S₁ ++ S₂) i = walkElt Ms S₂ i * walkElt Ms S₁ i
  | [], S₂ => by rw [List.nil_append, walkElt, Matrix.mul_one]
  | ms :: S₁, S₂ => by
    rw [List.cons_append, walkElt, walkElt, walkElt_append Ms i S₁ S₂, Matrix.mul_assoc]

theorem ptB_of_neqMask {U V : List ℕ} (hU : lenN U = 156) (hV : lenN V = 156)
    (h : Nat.beq (neqMask U V) 0 = true) (i : ℕ) : ptB U i = ptB V i :=
  ptK_inj (ptK_of_neqMask hU hV h i)

def CentData.CandWalk (D : CentData) (A B : ℕ) : Prop :=
  ∃ Vf, lenN Vf = 156 ∧ D.candEnd A B Vf = true ∧
    ∀ j, ∃ S, ptB Vf j = walkElt (D.hLet A B) S j *ᵥ ptB D.CL j

theorem lenN_ccP (D : CentData) (cc : ℕ) : ∀ k, lenN (D.ccP cc k) = 156
  | 0 => by
    change lenN (splitPl D.CP (Nat.div (Nat.add D.s 7) 8) D.s 156) = 156
    exact lenN_splitPl _ _ _ _
  | _ + 1 => by
    unfold CentData.ccP
    exact lenN_splitPl _ _ _ _

theorem candWalk_of_candF (D : CentData) {A B : ℕ} (h : D.candF A B = true) :
    D.candIni A B = true ∧ D.CandWalk A B := by
  unfold CentData.candF candOK at h
  rw [forceLB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, forceB_eq] at h
  obtain ⟨⟨hsort, hprof1⟩, hwalk⟩ := h
  refine ⟨by unfold CentData.candIni; rw [andB_eq, Bool.and_eq_true]; exact ⟨hsort, hprof1⟩, ?_⟩
  obtain ⟨V, hk, hV, hpt⟩ := walkK_sound _ _ (lenN_splitPl _ _ _ _) hwalk
  exact ⟨V, hV, by unfold CentData.candEnd; rw [forceB_eq]; exact hk, fun j => ⟨_, hpt j⟩⟩

theorem cand_of_csegs (D : CentData) {A B cc g m : ℕ} (hm : 0 < m)
    (h : ∀ k < m, D.csegF A B cc g m k = true) : D.CandWalk A B := by
  have hc : ∀ k, k + 1 < m → ∀ j, ∃ S, ptB (D.ccP cc (k + 1)) j =
      walkElt (D.hLet A B) S j *ᵥ ptB (D.ccP cc k) j := by
    intro k hk j
    have hs := h k (by omega)
    unfold CentData.csegF at hs
    obtain ⟨V, hkV, hV, hpt⟩ := walkK_sound _ _ (lenN_ccP D cc k) hs
    rw [beq_false_of_ne' (by omega : Nat.succ k ≠ m)] at hkV
    exact ⟨_, (ptB_of_neqMask hV (lenN_ccP D cc _) hkV j).symm.trans (hpt j)⟩
  have hch : ∀ k, k < m → ∀ j, ∃ S, ptB (D.ccP cc k) j =
      walkElt (D.hLet A B) S j *ᵥ ptB D.CL j := by
    intro k
    induction k with
    | zero => exact fun _ j => ⟨[], by rw [walkElt, Matrix.one_mulVec]; rfl⟩
    | succ k ih =>
      intro hk j
      obtain ⟨S₁, h₁⟩ := ih (by omega) j
      obtain ⟨S₂, h₂⟩ := hc k hk j
      exact ⟨S₁ ++ S₂, by rw [h₂, h₁, Matrix.mulVec_mulVec, walkElt_append]⟩
  have hs := h (m - 1) (by omega)
  unfold CentData.csegF at hs
  obtain ⟨V, hkV, hV, hpt⟩ := walkK_sound _ _ (lenN_ccP D cc _) hs
  have hb : Nat.beq (Nat.succ (m - 1)) m = true := by
    rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hm]
    exact Nat.beq_refl _
  rw [hb] at hkV
  refine ⟨V, hV, hkV, fun j => ?_⟩
  obtain ⟨S₁, h₁⟩ := hch (m - 1) (by omega) j
  exact ⟨S₁ ++ _, by rw [hpt j, h₁, Matrix.mulVec_mulVec, walkElt_append]⟩

theorem centFacts_of_walks (D : CentData) {PL : List ℕ} {A B r N : ℕ}
    (hA : Rep A (toMat nativeAB.1)) (hB : Rep B (toMat nativeAB.2))
    (hPL : OrbitBits PL A B 3968055 r) (hPLl : lenN PL = 156)
    (hv0 : Nat.beq (nthV D.V 0) A = true) (hv1 : Nat.beq (nthV D.V 1) B = true)
    (hp : ∀ t < lenLL D.prog, slpLine D.V D.prog 2 t = true)
    (hn : Nat.beq (lenN D.V) (Nat.add 2 (lenLL D.prog)) = true)
    (he0 : D.e 0 = 0) (helt : ∀ i < D.p, D.e i < D.p) (hcov : ∀ j < D.p, ∃ i < D.p, D.e i = j)
    (hbase : D.baseOK A B = true) (hlev : ∀ j < D.p - 1, D.levOK (j + 1) = true)
    (hL : D.LOK A B = true) (hLnd : (D.LI.map (nthV D.V)).Nodup)
    (hLcop : Nat.Coprime D.LI.length D.p)
    (hprod : 3968055 * (∏ i ∈ Finset.Ico 1 D.p, D.nf i) * D.LI.length = 76532479683774853939200)
    (hts1 : ∀ q ∈ D.K1, q.2 = 0 ∨ q.2 = 3 ∨ q.2 = 4 ∨ q.2 = 5)
    (htsA : ∀ q ∈ D.Kall, q.2 = 0 ∨ q.2 = 3 ∨ q.2 = 4 ∨ q.2 = 5)
    (hch : ∀ q < 16, D.chunkF PL A B q = true)
    (hcnt : ∑ q ∈ Finset.range 16, nthN D.cnts q = D.s)
    (hH : D.HOK A B = true) (hcandI : D.candIni A B = true) (hcw : D.CandWalk A B)
    (hstart : ∀ r < lenN D.reps, ∃ g ∈ monAB, g *ᵥ vecK (nthN D.reps r) = vecK D.bv)
    (hN : N = D.m₀ * D.LI.length)
    (hrefs : ∀ r < lenN D.reps, nthN D.st r = 1 → D.RefFact (vecK (nthN D.reps r))) :
    CentFacts D.p N D.xw D.d0 D.e D.K1 D.Kall := by
  have hX : Rep (D.xB A B) (wM D.xw) := rep_wM hA hB D.xw
  have hV : ∀ i < lenN D.V, Rep (nthV D.V i) (vM D.prog i) := fun i hi =>
    rep_vM hA hB hv0 hv1 hp hn hi
  simp only [CentData.baseOK, andB_eq, Bool.and_eq_true] at hbase
  obtain ⟨⟨⟨⟨hb, hβ⟩, hlβ⟩, hk1⟩, hka⟩ := hbase
  have hlβ' : D.βs.length = D.p := by rw [← CFSG.KS.StdOdd.Chain.lenN_eq_length]; exact Nat.eq_of_beq_eq_true hlβ
  have hbv : vecK D.bv = D.bK := by
    have := map1_K (rep_wM hA hB D.d0) hb
    rw [vecK_e7] at this
    exact this.symm
  have hβv : ∀ j < D.p, vecK (nthN D.βs j) = D.βK j := by
    intro j hj
    have := map1_K (rep_powB hX (nthN D.eL j)) (allN_true hβ j hj)
    rw [hbv, nthN_eq_getD] at this
    exact this.symm
  have hb1 : ∀ (K : List (ℕ × ℕ)), (∀ q ∈ K, q.2 = 0 ∨ q.2 = 3 ∨ q.2 = 4 ∨ q.2 = 5) →
      Nat.beq (profAll (D.xB A B) (K.map Prod.fst) (K.map Prod.snd) (vecsPl [D.bv]) 1
        Form.fmPk Form.brPk) (full 1) = true →
      ∀ q ∈ K, rhoC D.bK (wM D.xw ^ q.1 *ᵥ D.bK) = q.2 := by
    intro K hK h q hq
    have h0 : (profAll (D.xB A B) (K.map Prod.fst) (K.map Prod.snd) (vecsPl [D.bv]) 1
        Form.fmPk Form.brPk).testBit 0 = true := by
      rw [Nat.eq_of_beq_eq_true h, testBit_full]
      rfl
    have := ((prof_K hX (lenN_vecsPl _) 1 K hK 0).1 h0).2 q hq
    rwa [ptK_vecsPl [D.bv] (by simp), nthN_cons_zero, hbv] at this
  have hlev' : ∀ j, 1 ≤ j → j < D.p → D.levOK j = true := fun j h1 h2 => by
    have := hlev (j - 1) (by omega)
    rwa [Nat.sub_add_cancel h1] at this
  have hlevs : ∀ j, 1 ≤ j → j < D.p →
      (∀ r ∈ D.RI j, r < lenN D.V ∧ fixesOK (nthV D.V r) D.βs j = true) ∧
        forestOK (D.FP j) (D.WN j) (Nat.div (Nat.add (D.nf j) 7) 8) (D.nf j) (D.Df j)
          ((D.RI j).map (nthV D.V)) (nthN D.βs j) = true := by
    intro j h1 h2
    have h := hlev' j h1 h2
    simp only [CentData.levOK, andB_eq, Bool.and_eq_true] at h
    refine ⟨fun r hr => ?_, h.2⟩
    have := allL_true h.1 r hr
    rw [Bool.and_eq_true] at this
    exact ⟨Nat.blt_eq.mp this.1, this.2⟩
  have hfor : ∀ j, 1 ≤ j → j < D.p →
      (∀ i < D.nf j, ∀ i' < D.nf j, ptK (D.FL j) i = ptK (D.FL j) i' → i = i') ∧
        ∀ i < D.nf j, ∃ g ∈ monL (D.regK j), g *ᵥ ptK (D.FL j) i = D.βK j := by
    intro j h1 h2
    obtain ⟨hr, hf⟩ := hlevs j h1 h2
    obtain ⟨hlen, hrep⟩ := rep_letters hV (D.RI j) fun r hr' => (hr r hr').1
    obtain ⟨hinj, hw⟩ := forest_K hlen hrep hf
    refine ⟨hinj, fun i hi => ?_⟩
    obtain ⟨g, hg, hge⟩ := hw i hi
    exact ⟨g, hg, by rw [CentData.FL, hge, hβv j h2]⟩
  have hcardB : ∀ j, 1 ≤ j → j < D.p → (D.BlK j).card = D.nf j := by
    intro j h1 h2
    rw [CentData.BlK, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi i' hi' e
    exact (hfor j h1 h2).1 i (Finset.mem_range.1 hi) i' (Finset.mem_range.1 hi') e
  have hLs : ∀ r ∈ D.LI, r < lenN D.V ∧ vM D.prog r * wM D.xw = wM D.xw * vM D.prog r ∧
      ∀ j < D.p, vM D.prog r *ᵥ D.βK j = D.βK j := by
    intro r hr
    have := allL_true hL r hr
    simp only [andB_eq, Bool.and_eq_true] at this
    obtain ⟨h1, h2, h3⟩ := this
    have hr' := Nat.blt_eq.mp h1
    refine ⟨hr', comm_K (hV r hr') hX h2, fun j hj => ?_⟩
    rw [← hβv j hj]
    exact fix_K (hV r hr') (fixesOK_sound h3 j hj (by omega))
  set Hk : List M78 := wM D.xw ^ (D.p - 1) :: D.HI.map (lineProdG (gM D.prog)) with hHk
  have hHs : ∀ line ∈ D.HI, allL line (fun r => Nat.blt r (lenN D.V)) = true ∧
      Nat.beq (mulB (lineB D.V line) (D.xB A B)) (mulB (D.xB A B) (lineB D.V line)) = true := by
    intro line hl
    have := allLL_true hH line hl
    rw [andB_eq, Bool.and_eq_true] at this
    exact this
  have hHrep : lenN (D.hLet A B) = Hk.length ∧
      ∀ l < lenN (D.hLet A B), Rep (nthN (D.hLet A B) l) (Hk.getD l 0) := by
    refine ⟨by rw [CentData.hLet, CFSG.KS.StdOdd.Chain.lenN_eq_length, hHk]; simp, fun l hl => ?_⟩
    rw [CentData.hLet, CFSG.KS.StdOdd.Chain.lenN_eq_length, List.length_cons, List.length_map] at hl
    cases l with
    | zero => exact rep_powB hX _
    | succ l =>
      have hl' : l < D.HI.length := by omega
      have e1 : nthN (D.hLet A B) (l + 1) = lineB D.V D.HI[l] := by
        rw [CentData.hLet, nthN_cons_succ, nthN_eq_getD,
          List.getD_eq_getElem _ _ (by simpa using hl'), List.getElem_map]
      have e2 : Hk.getD (l + 1) 0 = lineProdG (gM D.prog) D.HI[l] := by
        rw [hHk, List.getD_cons_succ, List.getD_eq_getElem _ _ (by simpa using hl'),
          List.getElem_map]
      rw [e1, e2]
      exact rep_line hV _ fun r hr =>
        Nat.blt_eq.mp (allL_true (hHs _ (List.getElem_mem hl')).1 r hr)
  have hHmem : ∀ M ∈ Hk, M ∈ monAB ∧ M * wM D.xw = wM D.xw * M := by
    intro M hM
    rw [hHk, List.mem_cons] at hM
    rcases hM with rfl | hM
    · exact ⟨Submonoid.pow_mem _ (wM_mem _) _, (Commute.pow_left (Commute.refl _) _).eq⟩
    · obtain ⟨line, hl, rfl⟩ := List.mem_map.1 hM
      have hr : ∀ r ∈ line, r < lenN D.V := fun r hr =>
        Nat.blt_eq.mp (allL_true (hHs line hl).1 r hr)
      exact ⟨lineProdG_memS monAB (gM_mem _) line, comm_K (rep_line hV line hr) hX (hHs line hl).2⟩
  have hst : ∀ r < lenN D.reps, ∃ g ∈ monAB, g *ᵥ vecK (nthN D.reps r) = D.bK := by
    rw [← hbv]
    exact hstart
  unfold CentData.candIni at hcandI
  rw [andB_eq, Bool.and_eq_true] at hcandI
  obtain ⟨hsort, hprof1⟩ := hcandI
  have hCl : lenN D.CL = 156 := by
    change lenN (splitPl D.CP (Nat.div (Nat.add D.s 7) 8) D.s 156) = 156
    exact lenN_splitPl _ _ _ _
  set C := D.CL with hC
  obtain ⟨Vf, hVf, hk, hpt⟩ := hcw
  unfold CentData.candEnd at hk
  rw [forceB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at hk
  obtain ⟨⟨hall, hpop⟩, hlast⟩ := hk
  have hHw : ∀ j, ∃ g ∈ monL Hk, ptK Vf j = g *ᵥ ptK C j := by
    intro j
    obtain ⟨S, hS⟩ := hpt j
    obtain ⟨g, hg, hge⟩ := walk_lift hHrep.1 hHrep.2 S j
    exact ⟨g, hg, ptK_walk hS hge⟩
  have hHle : monL Hk ≤ monAB := monL_le fun M hM => (hHmem M hM).1
  have hin : ∀ j < D.s, ∃ r < lenN D.reps, ptK Vf j = vecK (nthN D.reps r) := by
    intro j hj
    obtain ⟨v, hv, he⟩ := allIn_sound hVf hall j hj
    obtain ⟨r, hr, rfl⟩ := exists_nthN hv
    exact ⟨r, hr, ptK_eq_vecK he⟩
  have hprofC : ∀ (K : List (ℕ × ℕ)), (∀ q ∈ K, q.2 = 0 ∨ q.2 = 3 ∨ q.2 = 4 ∨ q.2 = 5) → ∀ j,
      (profAll (D.xB A B) (K.map Prod.fst) (K.map Prod.snd) C D.s Form.fmPk Form.brPk).testBit j =
        true ↔ j < D.s ∧ ∀ q ∈ K, rhoC (ptK C j) (wM D.xw ^ q.1 *ᵥ ptK C j) = q.2 :=
    fun K hK j => prof_K hX hCl D.s K hK j
  have hchunk : ∀ q < 16, ((Finset.range (min 262144 (3968055 - q * 262144))).filter fun i =>
      ∀ k ∈ D.K1, rhoC (ptK PL (q * 262144 + i)) (wM D.xw ^ k.1 *ᵥ ptK PL (q * 262144 + i)) = k.2).card
        = nthN D.cnts q := by
    intro q hq
    have h := hch q hq
    unfold CentData.chunkF chunkOK at h
    rw [forceB_eq] at h
    set w := Nat.min 262144 (Nat.sub 3968055 (Nat.mul q 262144)) with hw
    have hw' : w = min 262144 (3968055 - q * 262144) := rfl
    set U := chunkPl PL (Nat.mul q 262144) w with hU
    have hUl : lenN U = 156 := by rw [hU, lenN_chunkPl, hPLl]
    have hpr := prof_K hX hUl w D.K1 hts1
    have hlt : profAll (D.xB A B) (D.K1.map Prod.fst) (D.K1.map Prod.snd) U w Form.fmPk Form.brPk <
        2 ^ w := testBit_lt_of fun i hi => ((hpr i).1 hi).1
    have hc := popK_sound _ _ w h hlt
    rw [← hw', ← hc]
    congr 1
    refine Finset.filter_congr fun i hi => ?_
    have hi' : i < w := Finset.mem_range.1 hi
    have hpt' : ptK U i = ptK PL (q * 262144 + i) :=
      ptB_inj (ptB_chunkPl PL (Nat.mul q 262144) w i hi')
    rw [hpr i, hpt']
    exact ⟨fun h => ⟨hi', h⟩, fun h => h.2⟩
  have hcount := card_filter_chunks (fun i => ∀ k ∈ D.K1,
    rhoC (ptK PL i) (wM D.xw ^ k.1 *ᵥ ptK PL i) = k.2) 262144 3968055 16 (by norm_num)
  rw [Finset.sum_congr rfl fun q hq => hchunk q (Finset.mem_range.1 hq), hcnt] at hcount
  obtain ⟨hoinj, hroot, hcA, hcB, hdep⟩ := facts_ptK hA hB hPL
  refine ⟨he0, helt, hcov, D.regK, D.BlK, D.LI.map (vM D.prog), ptK PL, Hk, ptK C, ptK Vf,
    D.s, D.m₀, fun i M hM => ?_, fun i hi M hM j hj => ?_, fun i h1 h2 y hy => ?_, fun M hM => ?_,
    ?_, ?_, ?_, hroot, hcA, hcB, hb1 D.K1 hts1 hk1, hb1 D.Kall htsA hka, hoinj, hdep, hcount,
    fun j hj => ((hprofC D.K1 hts1 j).1 ?_).2, fun j hj => ?_, fun j hj j' hj' e => ?_,
    hHmem, fun j hj => ?_, ?_, ?_, fun j hj hne => ?_⟩
  · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hM
    exact vM_mem _ _
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
    have h1 : 1 ≤ i := by omega
    obtain ⟨hr1, hr2⟩ := (hlevs i h1 hi).1 r hr
    change vM D.prog r *ᵥ D.βK j = D.βK j
    rw [← hβv j (by omega)]
    exact fix_K (hV r hr1) (fixesOK_sound hr2 j hj (by omega))
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hy
    exact (hfor i h1 h2).2 k (Finset.mem_range.1 hk)
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
    obtain ⟨-, h2, h3⟩ := hLs r hr
    exact ⟨vM_mem _ _, h2, h3⟩
  · refine List.Nodup.map_on (fun x hx y hy hxy => List.inj_on_of_nodup_map hLnd hx hy
      ((eq_iff_of_rep (hV x (hLs x hx).1) (hV y (hLs y hy).1)).2 hxy)) (List.Nodup.of_map _ hLnd)
  · exact (List.length_map (vM D.prog) : (D.LI.map (vM D.prog)).length = D.LI.length).symm ▸ hLcop
  · have hI : ∏ i ∈ Finset.Ico 1 D.p, (D.BlK i).card = ∏ i ∈ Finset.Ico 1 D.p, D.nf i :=
      Finset.prod_congr rfl fun i hi => by
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hi
        exact hcardB i h1 h2
    have e : (D.LI.map (vM D.prog)).length = D.LI.length := List.length_map _
    calc 3968055 * (∏ i ∈ Finset.Ico 1 D.p, (D.BlK i).card) * (D.LI.map (vM D.prog)).length
        = 3968055 * (∏ i ∈ Finset.Ico 1 D.p, D.nf i) * D.LI.length := by rw [hI, e]
      _ = 76532479683774853939200 := hprod
  · rw [Nat.eq_of_beq_eq_true hprof1, testBit_full]
    exact decide_eq_true hj
  · obtain ⟨r, hr, he⟩ := hin j hj
    obtain ⟨g, hg, hge⟩ := hHw j
    obtain ⟨g', hg', hge'⟩ := hst r hr
    refine ⟨g' * g, Submonoid.mul_mem _ hg' (hHle hg), ?_⟩
    rw [← Matrix.mulVec_mulVec, ← hge, he, hge']
    rfl
  · exact sort_inj hCl hsort j hj j' hj' (ptK_inj e)
  · obtain ⟨g, hg, hge⟩ := hHw j
    exact ⟨g, hg, hge.symm⟩
  · have hm := popK_sound _ _ D.s hpop (testBit_lt_of fun i hi => ((eqMaskV_sound hVf _ _ i).1 hi).1)
    refine Eq.trans (congrArg Finset.card (Finset.filter_congr fun j hj => ?_)) hm
    rw [eqMaskV_sound hVf, ptK_eq_iff_vecB, hbv]
    exact ⟨fun h => ⟨Finset.mem_range.1 hj, h⟩, fun h => h.2⟩
  · exact hN.trans (congrArg (D.m₀ * ·) (List.length_map (vM D.prog) : (D.LI.map (vM D.prog)).length = D.LI.length).symm)
  ·
    have hb0 : ((profAll (D.xB A B) (D.Kall.map Prod.fst) (D.Kall.map Prod.snd) C D.s Form.fmPk
        Form.brPk) &&& andNot (andNot (full D.s) (eqMaskV Vf D.bv D.s))
          (refMask Vf D.reps D.st D.s)).testBit j = false :=
      (congrArg (fun x => x.testBit j) (Nat.eq_of_beq_eq_true hlast)).trans (Nat.zero_testBit j)
    simp only [Nat.testBit_and, andNot_testBit, testBit_full] at hb0
    have hne' : (eqMaskV Vf D.bv D.s).testBit j = false := by
      cases h : (eqMaskV Vf D.bv D.s).testBit j
      · rfl
      · exact absurd (by change ptK Vf j = D.bK; rw [← hbv]; exact ptK_eq_vecK ((eqMaskV_sound hVf _ _ j).1 h).2) hne
    rw [hne', decide_eq_true hj] at hb0
    by_cases hA' : (profAll (D.xB A B) (D.Kall.map Prod.fst) (D.Kall.map Prod.snd) C D.s Form.fmPk
        Form.brPk).testBit j = true
    · rw [hA'] at hb0
      have href : (refMask Vf D.reps D.st D.s).testBit j = true := by
        cases h : (refMask Vf D.reps D.st D.s).testBit j
        · rw [h] at hb0; simp at hb0
        · rfl
      obtain ⟨r, hr, hs1, -, he⟩ := refMask_sound hVf _ _ _ _ href
      right
      rw [ptK_eq_vecK he]
      exact hrefs r hr hs1
    · left
      have hn := mt (hprofC D.Kall htsA j).2 hA'
      by_contra hc
      exact hn ⟨hj, fun q hq => by
        by_contra hq'
        exact hc ⟨q, hq, hq'⟩⟩

theorem centFacts_of_start (D : CentData) {PL : List ℕ} {A B r N : ℕ}
    (hA : Rep A (toMat nativeAB.1)) (hB : Rep B (toMat nativeAB.2))
    (hPL : OrbitBits PL A B 3968055 r) (hPLl : lenN PL = 156)
    (hv0 : Nat.beq (nthV D.V 0) A = true) (hv1 : Nat.beq (nthV D.V 1) B = true)
    (hp : ∀ t < lenLL D.prog, slpLine D.V D.prog 2 t = true)
    (hn : Nat.beq (lenN D.V) (Nat.add 2 (lenLL D.prog)) = true)
    (he0 : D.e 0 = 0) (helt : ∀ i < D.p, D.e i < D.p) (hcov : ∀ j < D.p, ∃ i < D.p, D.e i = j)
    (hbase : D.baseOK A B = true) (hlev : ∀ j < D.p - 1, D.levOK (j + 1) = true)
    (hL : D.LOK A B = true) (hLnd : (D.LI.map (nthV D.V)).Nodup)
    (hLcop : Nat.Coprime D.LI.length D.p)
    (hprod : 3968055 * (∏ i ∈ Finset.Ico 1 D.p, D.nf i) * D.LI.length = 76532479683774853939200)
    (hts1 : ∀ q ∈ D.K1, q.2 = 0 ∨ q.2 = 3 ∨ q.2 = 4 ∨ q.2 = 5)
    (htsA : ∀ q ∈ D.Kall, q.2 = 0 ∨ q.2 = 3 ∨ q.2 = 4 ∨ q.2 = 5)
    (hch : ∀ q < 16, D.chunkF PL A B q = true)
    (hcnt : ∑ q ∈ Finset.range 16, nthN D.cnts q = D.s)
    (hH : D.HOK A B = true) (hcand : D.candF A B = true)
    (hstart : ∀ r < lenN D.reps, ∃ g ∈ monAB, g *ᵥ vecK (nthN D.reps r) = vecK D.bv)
    (hN : N = D.m₀ * D.LI.length)
    (hrefs : ∀ r < lenN D.reps, nthN D.st r = 1 → D.RefFact (vecK (nthN D.reps r))) :
    CentFacts D.p N D.xw D.d0 D.e D.K1 D.Kall :=
  centFacts_of_walks D hA hB hPL hPLl hv0 hv1 hp hn he0 helt hcov hbase hlev hL hLnd hLcop hprod
    hts1 htsA hch hcnt hH (candWalk_of_candF D hcand).1 (candWalk_of_candF D hcand).2 hstart hN
    hrefs

theorem centFacts_of_checks (D : CentData) {PL : List ℕ} {A B r N : ℕ}
    (hA : Rep A (toMat nativeAB.1)) (hB : Rep B (toMat nativeAB.2))
    (hPL : OrbitBits PL A B 3968055 r) (hPLl : lenN PL = 156)
    (hv0 : Nat.beq (nthV D.V 0) A = true) (hv1 : Nat.beq (nthV D.V 1) B = true)
    (hp : ∀ t < lenLL D.prog, slpLine D.V D.prog 2 t = true)
    (hn : Nat.beq (lenN D.V) (Nat.add 2 (lenLL D.prog)) = true)
    (he0 : D.e 0 = 0) (helt : ∀ i < D.p, D.e i < D.p) (hcov : ∀ j < D.p, ∃ i < D.p, D.e i = j)
    (hbase : D.baseOK A B = true) (hlev : ∀ j < D.p - 1, D.levOK (j + 1) = true)
    (hL : D.LOK A B = true) (hLnd : (D.LI.map (nthV D.V)).Nodup)
    (hLcop : Nat.Coprime D.LI.length D.p)
    (hprod : 3968055 * (∏ i ∈ Finset.Ico 1 D.p, D.nf i) * D.LI.length = 76532479683774853939200)
    (hts1 : ∀ q ∈ D.K1, q.2 = 0 ∨ q.2 = 3 ∨ q.2 = 4 ∨ q.2 = 5)
    (htsA : ∀ q ∈ D.Kall, q.2 = 0 ∨ q.2 = 3 ∨ q.2 = 4 ∨ q.2 = 5)
    (hch : ∀ q < 16, D.chunkF PL A B q = true)
    (hcnt : ∑ q ∈ Finset.range 16, nthN D.cnts q = D.s)
    (hH : D.HOK A B = true) (hcand : D.candF A B = true) (hstart : D.startF A B = true)
    (hN : N = D.m₀ * D.LI.length)
    (hrefs : ∀ r < lenN D.reps, nthN D.st r = 1 → D.RefFact (vecK (nthN D.reps r))) :
    CentFacts D.p N D.xw D.d0 D.e D.K1 D.Kall :=
  centFacts_of_start D hA hB hPL hPLl hv0 hv1 hp hn he0 helt hcov hbase hlev hL hLnd hLcop hprod
    hts1 htsA hch hcnt hH hcand (start_of_startF D hA hB hstart) hN hrefs

end CFSG.KD.StdOdd.Cent

end
