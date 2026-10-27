module

public import Certificates.Kernel.J4Q.QTBase
public import Certificates.Kernel.J4Q.CommData
public import CFSG.Certificates.Kernel.J4Q.RepComm
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.J4.QTOutObsNative
public import CFSG.Sporadic.J4.QTRankWitNative

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

theorem cmMG_chk : andB (Nat.beq MG0 (wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] mWord0))
    (Nat.beq MG1 (wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] mWord1)) = true := by quickRfl

theorem mat0_enc : WfA mat0 ∧ encR mat0 = MG0 := by
  have h := cmMG_chk
  rw [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := enc_wordRows hK loc_gens loc_invs mWord0
  exact ⟨h1, h2.trans (Nat.eq_of_beq_eq_true h.1).symm⟩

theorem mat1_enc : WfA mat1 ∧ encR mat1 = MG1 := by
  have h := cmMG_chk
  rw [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := enc_wordRows hK loc_gens loc_invs mWord1
  exact ⟨h1, h2.trans (Nat.eq_of_beq_eq_true h.2).symm⟩

@[expose] noncomputable def cmMGK (g : Nat) : Nat := Bool.rec (motive := fun _ => Nat) MG1 MG0 (Nat.beq g 0)

theorem mg_enc (g : Nat) : WfA (mg g) ∧ encR (mg g) = cmMGK g := by
  unfold mg cmMGK
  by_cases h : g = 0
  · subst h
    exact mat0_enc
  · simp only [h, ↓reduceIte]
    rw [nbeq_false h]
    exact mat1_enc

@[expose] noncomputable def cmPathK (w : List Nat) : Nat :=
  List.foldl (fun acc g => mulJ c rm acc (cmMGK g)) one w

theorem foldl_mg_enc : ∀ (w : List Nat) (acc : Array V2) (a : Nat), WfA acc ∧ encR acc = a →
    WfA (w.foldl (fun acc g => mulRows acc (mg g)) acc) ∧
      encR (w.foldl (fun acc g => mulRows acc (mg g)) acc) = w.foldl (fun a g => mulJ c rm a (cmMGK g)) a
  | [], _, _, h => h
  | g :: w, acc, a, h => by
    rw [List.foldl_cons, List.foldl_cons]
    exact foldl_mg_enc w _ _ (mul_enc hK h (mg_enc g))

theorem pathMat_enc (w : List Nat) : WfA (pathMat w) ∧ encR (pathMat w) = cmPathK w :=
  foldl_mg_enc w _ _ (id_enc hK)

@[expose] noncomputable def cmWK (l : Nat) : Bool := Nat.beq (getN one WLS l) (cmPathK (spinWords.getD l []))

#j4q_all CFSG.KD.J4Q.CMW CertificateChecks.KernelJ4Q.cmWK 111

theorem wmat_enc {l : Nat} (hl : l < 111) : WfA (wmat l) ∧ encR (wmat l) = getN one WLS l := by
  obtain ⟨h1, h2⟩ := pathMat_enc (spinWords.getD l [])
  exact ⟨h1, h2.trans (Nat.eq_of_beq_eq_true (CMW.all l hl)).symm⟩

theorem wmats_get {l : Nat} (hl : l < 111) : wmats[l]! = wmat l := by
  simp [wmats, hl]

theorem wTabs_get {l : Nat} (hl : l < 111) : wTabs[l]! = frTable (wmat l) := by
  simp [wTabs, wmats, hl]

theorem v0_wf : v0Vec.wf = true := by decide

theorem v1_wf : v1Vec.wf = true := by decide

theorem bvec_enc {l : Nat} (hl : l < 111) :
    (bvec l).wf = true ∧ v2N (bvec l) = vecJ rm (v2N v0Vec) (getN one WLS l) := by
  have hw := wmat_enc hl
  unfold bvec
  rw [wTabs_get hl]
  exact ⟨wf_frApply hw.1 _, by rw [v2N_frApply hK hw.1 v0_wf, hw.2]⟩

@[expose] noncomputable def cmPRows (i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (v2N v1Vec) (Nat.beq i 111))
    (vecJ rm (v2N v0Vec) (getN one WLS i)) (Nat.blt i 111)

theorem cmP_chk : andB (Nat.beq PR (rowsJ cmPRows))
    (andB (canonJ pad PRI) (Nat.beq (mulJ c rm PR PRI) one)) = true := by quickRfl

theorem pRows_enc : WfA pRows ∧ encR pRows = PR := by
  have hc := cmP_chk
  simp only [andB_eq, Bool.and_eq_true] at hc
  have hlen : (((List.range 111).map bvec) ++ [v1Vec]).length = 112 := by simp
  have hwf : ∀ v ∈ ((List.range 111).map bvec) ++ [v1Vec], v.wf = true := by
    intro v hv
    rcases List.mem_append.1 hv with h | h
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 h
      exact (bvec_enc (List.mem_range.1 hl)).1
    · rw [List.mem_singleton.1 h]
      exact v1_wf
  obtain ⟨h1, h2⟩ := enc_toArray _ hlen hwf
  refine ⟨h1, h2.trans ((rowsJ_congr fun i hi => ?_).trans (Nat.eq_of_beq_eq_true hc.1).symm)⟩
  unfold cmPRows
  by_cases h : i < 111
  · have hb : Nat.blt i 111 = true := by
      rw [Nat.blt_eq]
      exact h
    rw [hb, List.getD_append _ _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h),
      List.getElem_map, List.getElem_range]
    exact (bvec_enc h).2
  · have hi' : i = 111 := by omega
    subst hi'
    rfl

theorem pInv_enc : WfA pInv ∧ encR pInv = PRI := by
  have hc := cmP_chk
  simp only [andB_eq, Bool.and_eq_true] at hc
  exact invRows_enc hK pRows_enc.1 hc.2.1 (by rw [pRows_enc.2]; exact hc.2.2)

theorem coords_enc {x : V2} (hx : x.wf = true) :
    (coordsOf x).wf = true ∧ v2N (coordsOf x) = vecJ rm (v2N x) PRI :=
  ⟨wf_frApply pInv_enc.1 _, by rw [coordsOf, v2N_frApply hK pInv_enc.1 hx, pInv_enc.2]⟩

@[expose] noncomputable def cmSumK (x : Nat) : Nat :=
  List.foldl (fun acc l => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (getN one WLS l)) (bitB x l))
    (nat_lit 0) (List.range 111)

theorem foldl_sumW_enc {cv : V2} (hc : cv.wf = true) : ∀ (L : List Nat), (∀ l ∈ L, l < 111) →
    ∀ (acc : Array V2) (a : Nat), WfA acc ∧ encR acc = a →
      WfA (L.foldl (fun acc l => if cv.testBit l then xorMat acc (wmats[l]!) else acc) acc) ∧
        encR (L.foldl (fun acc l => if cv.testBit l then xorMat acc (wmats[l]!) else acc) acc) =
          L.foldl (fun acc l => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (getN one WLS l))
            (bitB (v2N cv) l)) a
  | [], _, _, _, h => h
  | l :: L, hL, acc, a, h => by
    have hl := hL l List.mem_cons_self
    rw [List.foldl_cons, List.foldl_cons]
    refine foldl_sumW_enc hc L (fun x hx => hL x (List.mem_cons_of_mem _ hx)) _ _ ?_
    rw [bitB_eq, ← testBit_v2N _ (by omega)]
    by_cases hb : cv.testBit l
    · simp only [hb, ↓reduceIte]
      rw [wmats_get hl]
      obtain ⟨h1, h2⟩ := enc_xorMat h.1 (wmat_enc hl).1
      exact ⟨h1, by rw [h2, h.2, (wmat_enc hl).2]⟩
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact h

theorem sumW_enc {cv : V2} (hc : cv.wf = true) : WfA (sumW cv) ∧ encR (sumW cv) = cmSumK (v2N cv) :=
  foldl_sumW_enc hc (List.range 111) (fun _ hl => List.mem_range.1 hl) _ _ enc_zeroMat

@[expose] noncomputable def cmEdgeK (p g : Nat) : Nat :=
  Nat.xor (mulJ c rm (getN one WLS p) (cmMGK g))
    (cmSumK (vecJ rm (vecJ rm (vecJ rm (v2N v0Vec) (getN one WLS p)) (cmMGK g)) PRI))

@[expose] noncomputable def cmRgK (g : Nat) : Nat :=
  cmSumK (vecJ rm (Nat.xor (vecJ rm (v2N v1Vec) (cmMGK g)) (v2N v1Vec)) PRI)

theorem cmE_chk : andB (allR 6 fun e => Nat.beq (getN one EMS e)
      (cmEdgeK (kEdges.getD e (0, 0)).1 (kEdges.getD e (0, 0)).2))
    (allR 2 fun g => Nat.beq (getN one RGS g) (cmRgK g)) = true := by quickRfl

theorem kEdges_lt : ∀ e < 6, (kEdges.getD e (0, 0)).1 < 111 := by decide

theorem edgeMat_enc {e : Nat} (he : e < 6) : WfA (edgeMat e) ∧ encR (edgeMat e) = getN one EMS e := by
  have hc := cmE_chk
  rw [andB_eq, Bool.and_eq_true] at hc
  have hp := kEdges_lt e he
  have hb := bvec_enc hp
  have hm := mg_enc (kEdges.getD e (0, 0)).2
  have hv := wf_frApply hm.1 (bvec (kEdges.getD e (0, 0)).1)
  obtain ⟨hcw, hcv⟩ := coords_enc hv
  obtain ⟨hs1, hs2⟩ := sumW_enc hcw
  unfold edgeMat edgeCoords
  rw [wmats_get hp]
  obtain ⟨h1, h2⟩ := enc_xorMat (mul_enc hK (wmat_enc hp) hm).1 hs1
  refine ⟨h1, ?_⟩
  rw [h2, (mul_enc hK (wmat_enc hp) hm).2, hs2, hcv, v2N_frApply hK hm.1 hb.1, hb.2, hm.2]
  exact (Nat.eq_of_beq_eq_true (allR_spec hc.1 e he)).symm

theorem edgeMats_get {e : Nat} (he : e < 6) : edgeMats[e]! = edgeMat e := by
  simp [edgeMats, he]

theorem rg_enc {g : Nat} (hg : g < 2) : WfA (rg g) ∧ encR (rg g) = getN one RGS g := by
  have hc := cmE_chk
  rw [andB_eq, Bool.and_eq_true] at hc
  have hm := mg_enc g
  have hv := wf_xor (wf_frApply hm.1 v1Vec) v1_wf
  obtain ⟨hcw, hcv⟩ := coords_enc hv
  obtain ⟨hs1, hs2⟩ := sumW_enc hcw
  unfold rg v1Coords
  refine ⟨hs1, ?_⟩
  rw [hs2, hcv, v2N_xor, v2N_frApply hK hm.1 v1_wf, hm.2]
  exact (Nat.eq_of_beq_eq_true (allR_spec hc.2 g hg)).symm

theorem mgp_enc (g : Nat) : WfA (mgp g) ∧ encR (mgp g) = Nat.xor (cmMGK g) one := by
  have hm := mg_enc g
  obtain ⟨h1, h2⟩ := enc_xorMat hm.1 wf_idRows
  unfold mgp
  exact ⟨h1, by rw [h2, hm.2, enc_idRows hK]⟩

theorem mgps_get {g : Nat} (hg : g < 2) : mgps[g]! = mgp g := by
  rcases g with _ | _ | g
  · rfl
  · rfl
  · omega

theorem bk_pack : andB (packOK BK bkRows.toList) (andB (canonJ pad BK)
    (andB (canonJ pad BKI) (Nat.beq (mulJ c rm BK BKI) one))) = true := by quickRfl

theorem bf_pack : andB (packOK BF bfRows.toList) (andB (canonJ pad BF)
    (andB (canonJ pad BFI) (Nat.beq (mulJ c rm BF BFI) one))) = true := by quickRfl

theorem bk_enc : WfA bkRows ∧ encR bkRows = BK := by
  have h := bk_pack
  simp only [andB_eq, Bool.and_eq_true] at h
  exact packOK_sound hK h.1 h.2.1

theorem bf_enc : WfA bfRows ∧ encR bfRows = BF := by
  have h := bf_pack
  simp only [andB_eq, Bool.and_eq_true] at h
  exact packOK_sound hK h.1 h.2.1

theorem bkInv_enc : WfA (invRows bkRows) ∧ encR (invRows bkRows) = BKI := by
  have h := bk_pack
  simp only [andB_eq, Bool.and_eq_true] at h
  exact invRows_enc hK bk_enc.1 h.2.2.1 (by rw [bk_enc.2]; exact h.2.2.2)

theorem bfInv_enc : WfA (invRows bfRows) ∧ encR (invRows bfRows) = BFI := by
  have h := bf_pack
  simp only [andB_eq, Bool.and_eq_true] at h
  exact invRows_enc hK bf_enc.1 h.2.2.1 (by rw [bf_enc.2]; exact h.2.2.2)

theorem bitsJ_congr {f g : Nat → Bool} (h : ∀ j < 112, f j = g j) : bitsJ f = bitsJ g := by
  have : ∀ n ≤ 112, Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.lor acc (Nat.shiftLeft (nat_lit 1) j)) (f j)) n =
      Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.lor acc (Nat.shiftLeft (nat_lit 1) j)) (g j)) n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      change Bool.rec (motive := fun _ => Nat) _ _ (f n) = Bool.rec (motive := fun _ => Nat) _ _ (g n)
      rw [ih (by omega), h n (by omega)]
  exact this 112 (le_refl _)

@[expose] noncomputable def cmPhiK (Ms : List Nat) (cols : List (Nat × Nat)) : Nat :=
  rowsJ fun i => bitsJ fun m => Option.rec (motive := fun _ => Bool) false
    (fun p => Prod.rec (motive := fun _ => Bool) (fun e c => Nat.testBit (rowJ rm (getN one Ms e) i) c) p) cols[m]?

theorem phiOf_enc {mats : Array (Array V2)} {Ms : List Nat} {cols : List (Nat × Nat)} {n : Nat}
    (hM : ∀ e < n, WfA (mats[e]!) ∧ encR (mats[e]!) = getN one Ms e)
    (hc : ∀ p ∈ cols, p.1 < n ∧ p.2 < 112) :
    WfA (phiOf mats cols) ∧ encR (phiOf mats cols) = cmPhiK Ms cols := by
  obtain ⟨h1, h2⟩ := enc_ofFn (fun i => V2.ofFn fun m => match cols[m]? with
    | some (e, c) => ((mats[e]!)[i]!).testBit c
    | none => false) (fun i _ => wf_ofFn _)
  refine ⟨h1, h2.trans (rowsJ_congr fun i _ => ?_)⟩
  rw [v2N_ofFn]
  apply bitsJ_congr
  intro m _
  rcases hm : cols[m]? with _ | ⟨e, c⟩
  · rfl
  · have hp := hc (e, c) (List.mem_of_getElem? hm)
    have he := hM e hp.1
    change ((mats[e]!)[i]!).testBit c = Nat.testBit (rowJ rm (getN one Ms e) i) c
    rw [testBit_v2N _ (by omega), v2N_getElem! hK he.1, he.2]

theorem psiRows_enc (s : Nat) : WfA (psiRows s) ∧
    encR (psiRows s) = rowsJ fun i => bitsJ fun j => decide (s ≤ i ∧ j = i - s) := by
  obtain ⟨h1, h2⟩ := enc_ofFn (fun i => V2.ofFn fun j => decide (s ≤ i ∧ j = i - s)) (fun i _ => wf_ofFn _)
  refine ⟨h1, h2.trans (rowsJ_congr fun i _ => ?_)⟩
  rw [v2N_ofFn]

end CertificateChecks.KernelJ4Q

end
