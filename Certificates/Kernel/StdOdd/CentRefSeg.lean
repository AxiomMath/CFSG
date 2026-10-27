module

public import Certificates.Kernel.StdOdd.CentRef

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KS.StdOdd.Orbit CFSG.KS.StdOdd.Chain
  CFSG.KD.StdOdd.Orbit CFSG.KC.Misc.E6Std CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.Existence.StdOdd.Cert Matrix CFSG.KC.LQT.P

@[expose] def sliceL (a n : ℕ) (S : List (List ℕ)) : List (List ℕ) := (S.drop a).take n

namespace CentData

variable (D : CentData)

@[expose] noncomputable def rkP (RK K ri : ℕ) (O : List ℕ) (c : ℕ) : List ℕ :=
  Nat.casesOn (motive := fun _ => List ℕ) c (vecsPl (pickL O D.eL)) fun c' =>
    splitPl (Nat.shiftRight RK (Nat.mul (Nat.mul 1248 (Nat.div (Nat.add D.p 7) 8))
      (Nat.add (Nat.mul (Nat.mul ri (Nat.sub D.p 1)) K) c'))) (Nat.div (Nat.add D.p 7) 8) D.p 156

@[expose] noncomputable def refLet (A B l : ℕ) : List ℕ :=
  Bool.rec (motive := fun _ => List ℕ) ((D.RI l).map (nthV D.V)) [A, B] (Nat.beq l 0)

@[expose] noncomputable def rchF (A B RK K ri : ℕ) (O : List ℕ) (Sr : List (List (List ℕ)))
    (l k : ℕ) : Bool :=
  walkK (D.refLet A B l) (spreadS (sliceL (Nat.mul 20 k) 20 (Sr.getD l [])) 1 (lenN D.eL))
      (D.rkP RK K ri O (Nat.add (Nat.mul l K) k)) fun T =>
    andB (Nat.beq (neqMask T (D.rkP RK K ri O (Nat.succ (Nat.add (Nat.mul l K) k)))) 0)
      (Bool.rec (motive := fun _ => Bool) true
        (Nat.beq (Nat.land (neqV T (nthN D.βs l) (Nat.succ l)) (Nat.shiftLeft 1 l)) 0)
        (Nat.beq (Nat.succ k) K))

@[expose] noncomputable def rfinF (RK K ri : ℕ) (O : List ℕ) (m : ℕ) : Bool :=
  Nat.beq (neqPt (D.FL m) (D.rkP RK K ri O (Nat.mul m K)) m (full (D.nf m))) (full (D.nf m))

@[expose] noncomputable def rbF (A B : ℕ) (O : List ℕ) (m r : ℕ) : Bool :=
  andB (andB (Nat.beq (lenN O) D.p) (andB (Nat.ble 1 m) (Nat.blt m D.p)))
    (andB (Nat.beq (neqMask (mapRows (D.xB A B) (vecsPl (dropLast O))) (vecsPl (tailL O))) 0)
      (Nat.beq (nthN O 0) (nthN D.reps r)))

end CentData

theorem lenN_rkP (D : CentData) (RK K ri : ℕ) (O : List ℕ) : ∀ c, lenN (D.rkP RK K ri O c) = 156
  | 0 => lenN_vecsPl _
  | _ + 1 => by
    unfold CentData.rkP
    exact lenN_splitPl _ _ _ _

theorem spreadS_app (r k : ℕ) : ∀ S₁ S₂ : List (List ℕ),
    spreadS (S₁ ++ S₂) r k = spreadS S₁ r k ++ spreadS S₂ r k
  | [], _ => rfl
  | ms :: S₁, S₂ => by
    change List.cons _ (spreadS (S₁ ++ S₂) r k) = List.cons _ (spreadS S₁ r k ++ spreadS S₂ r k)
    rw [spreadS_app r k S₁ S₂]

theorem neqPt_full {U T : List ℕ} (hU : lenN U = 156) (hT : lenN T = 156) {k w : ℕ}
    (h : Nat.beq (neqPt U T k (full w)) (full w) = true) {i : ℕ} (hi : i < w) :
    ptB U i ≠ ptB T k := by
  intro he
  have hb : (neqPt U T k (full w)).testBit i = true := by
    rw [Nat.eq_of_beq_eq_true h, testBit_full]
    exact decide_eq_true hi
  rw [neqPt, neqPt_aux (full w) i k U T 0 (hU.trans hT.symm), Nat.zero_testBit, Bool.false_or,
    List.any_eq_true] at hb
  obtain ⟨c, hc, hne⟩ := hb
  rw [List.mem_range, hU] at hc
  have := congrFun he ⟨c, hc⟩
  rw [ptB_eq, ptB_eq] at this
  rw [testBit_full, decide_eq_true hi, Bool.and_true, bz_inj this] at hne
  simp at hne

theorem refFact_of_chunks (D : CentData) {A B : ℕ} (hA : Rep A (toMat nativeAB.1))
    (hB : Rep B (toMat nativeAB.2)) (hV : ∀ i < lenN D.V, Rep (nthV D.V i) (vM D.prog i))
    (hRI : ∀ j, 1 ≤ j → j < D.p → ∀ r ∈ D.RI j, r < lenN D.V)
    (hβv : ∀ j < D.p, vecK (nthN D.βs j) = D.βK j) (heL : D.eL.length = D.p)
    (helt : ∀ i < D.p, D.e i < D.p) (he0 : D.e 0 = 0)
    {RK K ri : ℕ} {O : List ℕ} {Sr : List (List (List ℕ))} {m : ℕ} (hK : 0 < K) (hm1 : 1 ≤ m)
    (hmp : m < D.p) (hO : O.length = D.p)
    (h1 : Nat.beq (neqMask (mapRows (D.xB A B) (vecsPl (dropLast O))) (vecsPl (tailL O))) 0 = true)
    (hch : ∀ l < m, ∀ k < K, D.rchF A B RK K ri O Sr l k = true)
    (hfin : D.rfinF RK K ri O m = true) :
    D.RefFact (vecK (nthN O 0)) := by
  have hX : Rep (D.xB A B) (wM D.xw) := rep_wM hA hB D.xw
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
  set Tl : ℕ → List ℕ := fun l => D.rkP RK K ri O (l * K) with hTl
  have hlen : ∀ l, lenN (Tl l) = 156 := fun l => lenN_rkP D RK K ri O _
  have hT0p : ∀ i < D.p, ptK (Tl 0) i = wM D.xw ^ D.e i *ᵥ v := by
    intro i hi
    have hi' : i < (pickL O D.eL).length := by rw [lenN_pickL, heL]; exact hi
    change ptK (D.rkP RK K ri O (0 * K)) i = _
    rw [Nat.zero_mul]
    change ptK (vecsPl (pickL O D.eL)) i = _
    rw [ptK_vecsPl _ hi', nthN_pickL _ _ _ (by rw [heL]; exact hi), hpow _ (by
      rw [hO, nthN_eq_getD]; exact helt i hi), nthN_eq_getD]
    rfl
  set w := lenN D.eL with hw
  have hwp : w = D.p := by rw [hw, CFSG.KS.StdOdd.Chain.lenN_eq_length, heL]
  have hchunk : ∀ l < m, ∀ k ≤ K, ∃ S, ∀ i, ptB (D.rkP RK K ri O (l * K + k)) i =
      walkElt (D.refLet A B l) (spreadS S 1 w) i *ᵥ ptB (Tl l) i := by
    intro l hl k
    induction k with
    | zero =>
      have e0 : spreadS ([] : List (List ℕ)) 1 w = [] := rfl
      exact fun _ => ⟨[], fun i => by rw [Nat.add_zero, e0, walkElt, Matrix.one_mulVec]⟩
    | succ k ih =>
      intro hk
      obtain ⟨S, hS⟩ := ih (by omega)
      have hc := hch l hl k (by omega)
      unfold CentData.rchF at hc
      obtain ⟨V, hkV, hVl, hpt⟩ := walkK_sound _ _ (lenN_rkP D RK K ri O _) hc
      rw [andB_eq, Bool.and_eq_true] at hkV
      have he := ptB_of_neqMask hVl (lenN_rkP D RK K ri O _) hkV.1
      refine ⟨S ++ sliceL (Nat.mul 20 k) 20 (Sr.getD l []), fun i => ?_⟩
      change ptB (D.rkP RK K ri O (Nat.succ (Nat.add (Nat.mul l K) k))) i = _
      rw [← he i, hpt i, spreadS_app, walkElt_append, ← Matrix.mulVec_mulVec]
      change _ = _ *ᵥ (walkElt (D.refLet A B l) (spreadS S 1 w) i *ᵥ ptB (Tl l) i)
      rw [← hS i]
      rfl
  have hlevel : ∀ l < m, (∃ S, ∀ i < D.p, ptB (Tl (l + 1)) i =
      walkElt (D.refLet A B l) (spreadS S 1 w) 0 *ᵥ ptB (Tl l) i) ∧
      ptB (Tl (l + 1)) l = vecB (nthN D.βs l) := by
    intro l hl
    have e : (l + 1) * K = l * K + K := Nat.succ_mul l K
    refine ⟨?_, ?_⟩
    · obtain ⟨S, hS⟩ := hchunk l hl K le_rfl
      refine ⟨S, fun i hi => ?_⟩
      change ptB (D.rkP RK K ri O ((l + 1) * K)) i = _
      rw [e, hS i, walkElt_spread1 _ _ (by rw [hwp]; exact hi)]
    · have hc := hch l hl (K - 1) (by omega)
      unfold CentData.rchF at hc
      obtain ⟨V, hkV, hVl, hpt⟩ := walkK_sound _ _ (lenN_rkP D RK K ri O _) hc
      rw [andB_eq, Bool.and_eq_true] at hkV
      obtain ⟨hk1, hk2⟩ := hkV
      have hb : Nat.beq (Nat.succ (K - 1)) K = true := by
        rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hK]
        exact Nat.beq_refl _
      rw [hb] at hk2
      have he := ptB_of_neqMask hVl (lenN_rkP D RK K ri O _) hk1 l
      have hidx : Nat.succ (Nat.add (Nat.mul l K) (K - 1)) = (l + 1) * K := by
        rw [e]
        change l * K + (K - 1) + 1 = l * K + K
        omega
      rw [hidx] at he
      change ptB (D.rkP RK K ri O ((l + 1) * K)) l = _
      rw [← he]
      by_contra hne
      have hb' := (neqV_sound hVl (nthN D.βs l) (l + 1) l).2 ⟨by omega, hne⟩
      have h0' := congrArg (fun x => x.testBit l) (Nat.eq_of_beq_eq_true hk2)
      change ((neqV V (nthN D.βs l) (l + 1)) &&& (1 <<< l)).testBit l = (0 : ℕ).testBit l at h0'
      rw [Nat.testBit_and, hb', Nat.testBit_shiftLeft, Nat.zero_testBit] at h0'
      simp at h0'
  have hlen0 : lenN [A, B] = [toMat nativeAB.1, toMat nativeAB.2].length := rfl
  have hrep0 : ∀ l < lenN [A, B], Rep (nthN [A, B] l) ([toMat nativeAB.1, toMat nativeAB.2].getD l 0) := by
    intro l hl
    change l < 2 at hl
    rcases l with _ | _ | l
    · exact hA
    · exact hB
    · omega
  have hp0 : 0 < D.p := Nat.lt_of_le_of_lt (Nat.zero_le m) hmp
  obtain ⟨⟨S0, hS0⟩, hβ0⟩ := hlevel 0 (by omega)
  have hlet0 : D.refLet A B 0 = [A, B] := rfl
  rw [hlet0] at hS0
  obtain ⟨g0, hg0, hge0⟩ := walk_lift hlen0 hrep0 (spreadS S0 1 w) 0
  have ht1 : ∀ i < D.p, ptK (Tl 1) i = g0 *ᵥ (wM D.xw ^ D.e i *ᵥ v) := by
    intro i hi
    rw [← hT0p i hi]
    exact ptK_of_mat (hS0 i hi) hge0
  have hb0 : ptK (Tl 1) 0 = D.βK 0 := by
    rw [ptK_eq_vecK hβ0, hβv 0 hp0]
  have hf : ∀ j, 1 ≤ j → j < m → ∃ f ∈ monL (D.regK j), ∀ i < D.p,
      ptK (Tl (j + 1)) i = f *ᵥ ptK (Tl j) i := by
    intro j hj1 hjm
    obtain ⟨⟨S, hS⟩, -⟩ := hlevel j hjm
    have hlet : D.refLet A B j = (D.RI j).map (nthV D.V) := by
      unfold CentData.refLet
      rw [beq_false_of_ne' (by omega : j ≠ 0)]
    rw [hlet] at hS
    obtain ⟨hl, hr⟩ := rep_letters hV (D.RI j) (hRI j hj1 (by omega))
    obtain ⟨f, hfm, hfe⟩ := walk_lift hl hr (spreadS S 1 w) 0
    exact ⟨f, hfm, fun i hi => ptK_of_mat (hS i hi) hfe⟩
  choose! f hfm hfe using hf
  refine ⟨g0, monL_AB hg0, ?_, m, fun j i => ptK (Tl j) i, f, hm1, hmp, ht1, hb0,
    fun j hj1 hjm => ⟨hfm j hj1 hjm, ?_, hfe j hj1 hjm⟩, ?_⟩
  · have := ht1 0 hp0
    rw [he0, pow_zero, Matrix.one_mulVec, hb0] at this
    rw [← this]
    simp [CentData.βK, he0]
  · rw [← hfe j hj1 hjm j (by omega)]
    rw [ptK_eq_vecK (hlevel j hjm).2, hβv j (by omega)]
  ·
    intro hmem
    obtain ⟨k, hk, hke⟩ := Finset.mem_image.1 hmem
    have hFL : lenN (D.FL m) = 156 := lenN_splitPl _ _ _ _
    exact neqPt_full hFL (hlen m) hfin (Finset.mem_range.1 hk) (ptK_inj hke)

namespace CentData

variable (D : CentData)

@[expose] noncomputable def refSegOK (A B RK K ri : ℕ) (O : List ℕ) (Sr : List (List (List ℕ)))
    (m r : ℕ) : Prop :=
  D.rbF A B O m r = true ∧ (∀ l < m, ∀ k < K, D.rchF A B RK K ri O Sr l k = true) ∧
    D.rfinF RK K ri O m = true

end CentData

theorem refs_of_chunks (D : CentData) {A B : ℕ} (hA : Rep A (toMat nativeAB.1))
    (hB : Rep B (toMat nativeAB.2)) (hv0 : Nat.beq (nthV D.V 0) A = true)
    (hv1 : Nat.beq (nthV D.V 1) B = true) (hp : ∀ t < lenLL D.prog, slpLine D.V D.prog 2 t = true)
    (hn : Nat.beq (lenN D.V) (Nat.add 2 (lenLL D.prog)) = true)
    (hbase : D.baseOK A B = true) (hlev : ∀ j < D.p - 1, D.levOK (j + 1) = true)
    (heL : D.eL.length = D.p) (helt : ∀ i < D.p, D.e i < D.p) (he0 : D.e 0 = 0)
    {RK K R : ℕ} (hK : 0 < K) {O : ℕ → List ℕ} {Sr : ℕ → List (List (List ℕ))} {fl sidx : ℕ → ℕ}
    (hchk : ∀ ri < R, D.refSegOK A B RK K ri (O ri) (Sr ri) (fl ri) (sidx ri))
    (hcov : D.covF sidx R = true) :
    ∀ r < lenN D.reps, nthN D.st r = 1 → D.RefFact (vecK (nthN D.reps r)) := by
  have hV : ∀ i < lenN D.V, Rep (nthV D.V i) (vM D.prog i) := fun i hi =>
    rep_vM hA hB hv0 hv1 hp hn hi
  have hX : Rep (D.xB A B) (wM D.xw) := rep_wM hA hB D.xw
  simp only [CentData.baseOK, andB_eq, Bool.and_eq_true] at hbase
  obtain ⟨⟨⟨⟨hb, hβ⟩, -⟩, -⟩, -⟩ := hbase
  have hbv : vecK D.bv = D.bK := by
    have := map1_K (rep_wM hA hB D.d0) hb
    rw [vecK_e7] at this
    exact this.symm
  have hβv : ∀ j < D.p, vecK (nthN D.βs j) = D.βK j := by
    intro j hj
    have := map1_K (rep_powB hX (nthN D.eL j)) (allN_true hβ j hj)
    rw [hbv, nthN_eq_getD] at this
    exact this.symm
  have hRI : ∀ j, 1 ≤ j → j < D.p → ∀ r ∈ D.RI j, r < lenN D.V := by
    intro j h1 h2 r hr
    have h := hlev (j - 1) (by omega)
    rw [Nat.sub_add_cancel h1] at h
    simp only [CentData.levOK, andB_eq, Bool.and_eq_true] at h
    have := allL_true h.1 r hr
    rw [Bool.and_eq_true] at this
    exact Nat.blt_eq.mp this.1
  intro r hr hs
  have hc := allN_true hcov r hr
  rw [Bool.or_eq_true, Bool.not_eq_true', hs] at hc
  rcases hc with hc | hc
  · exact absurd hc (by decide)
  obtain ⟨ri, hri, hre⟩ := List.any_eq_true.1 hc
  rw [List.mem_range] at hri
  have hsr : sidx ri = r := Nat.eq_of_beq_eq_true hre
  obtain ⟨hb0, hch, hfin⟩ := hchk ri hri
  simp only [CentData.rbF, andB_eq, Bool.and_eq_true] at hb0
  obtain ⟨⟨hlen, hm1, hmp⟩, h1, h0⟩ := hb0
  have hO : (O ri).length = D.p := by
    rw [← CFSG.KS.StdOdd.Chain.lenN_eq_length]
    exact Nat.eq_of_beq_eq_true hlen
  have hf := refFact_of_chunks D hA hB hV hRI hβv heL helt he0 hK (Nat.le_of_ble_eq_true hm1)
    (Nat.blt_eq.mp hmp) hO h1 hch hfin
  rwa [Nat.eq_of_beq_eq_true h0, hsr] at hf

@[expose] def flatC (L K : ℕ) (fl : ℕ → ℕ) (F : ℕ → ℕ → ℕ → Bool) (q : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) true (F (q / (L * K)) (q / K % L) (q % K))
    (Nat.blt (q / K % L) (fl (q / (L * K))))

theorem flatC_all {R L K : ℕ} {fl : ℕ → ℕ} {F : ℕ → ℕ → ℕ → Bool}
    (h : ∀ q < R * (L * K), flatC L K fl F q = true) {ri l k : ℕ} (hri : ri < R) (hl : l < fl ri)
    (hlL : l < L) (hk : k < K) : F ri l k = true := by
  have hK : 0 < K := by omega
  have hLK : l * K + k < L * K := by nlinarith
  have hq : ri * (L * K) + (l * K + k) < R * (L * K) := by
    have : (ri + 1) * (L * K) ≤ R * (L * K) := Nat.mul_le_mul_right _ hri
    rw [Nat.succ_mul] at this
    omega
  have e1 : (ri * (L * K) + (l * K + k)) / (L * K) = ri := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hLK, Nat.zero_add]
  have e2 : (ri * (L * K) + (l * K + k)) = k + (ri * L + l) * K := by ring
  have e3 : (ri * (L * K) + (l * K + k)) / K % L = l := by
    rw [e2, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hk, Nat.zero_add, Nat.add_comm,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlL]
  have e4 : (ri * (L * K) + (l * K + k)) % K = k := by
    rw [e2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  have := h _ hq
  unfold flatC at this
  rw [e1, e3, e4, Nat.blt_eq.mpr hl] at this
  exact this

theorem refs_of_flat (D : CentData) {A B : ℕ} (hA : Rep A (toMat nativeAB.1))
    (hB : Rep B (toMat nativeAB.2)) (hv0 : Nat.beq (nthV D.V 0) A = true)
    (hv1 : Nat.beq (nthV D.V 1) B = true) (hp : ∀ t < lenLL D.prog, slpLine D.V D.prog 2 t = true)
    (hn : Nat.beq (lenN D.V) (Nat.add 2 (lenLL D.prog)) = true)
    (hbase : D.baseOK A B = true) (hlev : ∀ j < D.p - 1, D.levOK (j + 1) = true)
    (heL : D.eL.length = D.p) (helt : ∀ i < D.p, D.e i < D.p) (he0 : D.e 0 = 0)
    {RK K R : ℕ} (hK : 0 < K) {O : ℕ → List ℕ} {Sr : ℕ → List (List (List ℕ))} {fl sidx : ℕ → ℕ}
    (hrb : ∀ ri < R, D.rbF A B (O ri) (fl ri) (sidx ri) = true)
    (hrc : ∀ q < R * ((D.p - 1) * K),
      flatC (D.p - 1) K fl (fun ri l k => D.rchF A B RK K ri (O ri) (Sr ri) l k) q = true)
    (hrf : ∀ ri < R, D.rfinF RK K ri (O ri) (fl ri) = true)
    (hcov : D.covF sidx R = true) :
    ∀ r < lenN D.reps, nthN D.st r = 1 → D.RefFact (vecK (nthN D.reps r)) := by
  refine refs_of_chunks D hA hB hv0 hv1 hp hn hbase hlev heL helt he0 (RK := RK) hK (O := O)
    (Sr := Sr) (fl := fl) (fun ri hri => ?_) hcov
  have hb := hrb ri hri
  refine ⟨hb, fun l hl k hk => flatC_all hrc hri hl ?_ hk, hrf ri hri⟩
  simp only [CentData.rbF, andB_eq, Bool.and_eq_true] at hb
  have := Nat.blt_eq.mp hb.1.2.2
  omega

end CFSG.KD.StdOdd.Cent

end
