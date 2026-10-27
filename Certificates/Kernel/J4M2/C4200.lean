module

public import Certificates.Data.J4M2.Orbit
public import Certificates.Kernel.J4M2.Base
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M2

open CFSG.KC.Loop CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2A
  CFSG.Quasithin.J4M2 CertificateChecks.KernelJ4Q

@[expose] noncomputable def gL : List Nat := smapK gmK (rangeK 32)

theorem getN_eq_getD (d : Nat) : ∀ (l : List Nat) (i : Nat), getN d l i = l.getD i d
  | [], i => by cases i <;> rfl
  | x :: l, 0 => rfl
  | x :: l, i + 1 => getN_eq_getD d l i

theorem getN_map_range (f : Nat → Nat) {n i : Nat} (hi : i < n) (d : Nat) :
    getN d ((List.range n).map f) i = f i := by
  rw [getN_eq_getD, List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem gL_get {g : Nat} (hg : g < 32) : getN one gL g = gmK g := by
  rw [gL, smapK_eq, rangeK_eq, getN_map_range gmK hg]

private theorem v2N_eq_toNat' (a : V2) : v2N a = a.toNat := by
  unfold v2N V2.toNat
  rw [Nat.lor_eq, Nat.shiftLeft_eq', Nat.or_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt (UInt64.toNat_lt a.lo) a.hi.toNat,
    Nat.shiftLeft_eq]
  omega

private theorem natToV2_toNat' (n : Nat) : (natToV2 n).toNat = n % 2 ^ 128 := by
  unfold natToV2 V2.toNat
  simp only [UInt64.toNat_ofNat']
  have h : 2 ^ 128 = 2 ^ 64 * 2 ^ 64 := by norm_num
  rw [h, Nat.mod_mul, Nat.mod_mod]

theorem v2N_natToV2 {n : Nat} (hn : n < 2 ^ 112) : v2N (natToV2 n) = n := by
  rw [v2N_eq_toNat', natToV2_toNat']
  exact Nat.mod_eq_of_lt (lt_trans hn (by norm_num))

@[expose] noncomputable def vd (i : Nat) : Nat := getN 0 vecData i

theorem vecs_get (m : Nat) : vecs[m]! = natToV2 (vd m) := by
  unfold vecs vd
  rw [getN_eq_getD]
  by_cases hm : m < vecData.length
  · rw [getElem!_pos _ m (by simpa using hm), List.getD_eq_getElem _ _ hm]
    simp
  · rw [getElem!_neg _ m (by simpa using hm), List.getD_eq_default _ _ (by omega)]
    rfl

theorem vd_chk : (List.range 77).all (fun i => Nat.blt (vd i) (2 ^ 112)) = true := by quickRfl

theorem vd_lt {i : Nat} (hi : i < 77) : vd i < 2 ^ 112 :=
  lt_of_blt (List.all_eq_true.1 vd_chk i (List.mem_range.2 hi))

theorem vecs_wf {i : Nat} (hi : i < 77) : (vecs[i]!).wf = true ∧ v2N vecs[i]! = vd i := by
  rw [vecs_get]
  exact ⟨wf_of_lt (by rw [v2N_natToV2 (vd_lt hi)]; exact vd_lt hi), v2N_natToV2 (vd_lt hi)⟩

theorem vecData_length : vecData.length = 77 := rfl

theorem gen_data : ∀ i < 77, genData[i]! < 32 ∧ (i = 0 ∨ parData[i]! < i) := by decide

theorem sig_data : ∀ n < 32, ∀ i < 77, (sigData[n]!)[i]! < 77 := by decide

theorem frApply_enc {M : Array V2} {m : Nat} (hM : WfA M ∧ encR M = m) {i : Nat} (hi : i < 77) :
    v2N (frApply (frTable M) vecs[i]!) = vecJ rm (vd i) m ∧ (frApply (frTable M) vecs[i]!).wf = true := by
  rw [v2N_frApply hK hM.1 (vecs_wf hi).1, (vecs_wf hi).2, hM.2]
  exact ⟨rfl, wf_frApply hM.1 _⟩

theorem gens_chk : (List.range 32).all (fun n => Nat.beq (mulJ c rm (getN one gL n) ZM)
    (mulJ c rm ZM (getN one gL n))) = true := by quickRfl

theorem gens_ok : chkGens = true := by
  rw [← gens_chk]
  unfold chkGens
  refine all_range_congr fun n hn => ?_
  have hg := gm_enc hn
  have hw : wfR gmats[n]! = true := wf_bool hg.1
  rw [hw, Bool.true_and, gtabs_get hn, zT_eq, mulT_frTable, mulT_frTable,
    eqRows_of (mul_enc hK hg zM_enc) (mul_enc hK zM_enc hg), gL_get hn]

theorem root_chk : Nat.beq (vd 0) (v2N rootV) = true := by quickRfl

theorem tree_chk : (List.range 77).all (fun i => i == 0 ||
    Nat.beq (vecJ rm (vd i) (getN one gL genData[i]!)) (vd parData[i]!)) = true := by quickRfl

theorem dist_chk : (List.range 77).all (fun i => (List.range i).all fun j =>
    !Nat.beq (vd i) (vd j)) = true := by quickRfl

theorem sig_chk : (List.range 32).all (fun n => (List.range 77).all fun i =>
    Nat.beq (vecJ rm (vd (sigData[n]!)[i]!) (getN one gL n)) (vd i)) = true := by quickRfl

theorem orbit_ok : chkOrbit = true := by
  unfold chkOrbit
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨by simp [vecs, vecData_length], ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [← Array.all_toList, List.all_eq_true]
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    have hi' : i < 77 := by simpa [vecs, vecData_length] using hi
    have := (vecs_wf hi').1
    rwa [getElem!_pos vecs i (by simpa [vecs, vecData_length] using hi'),
      ← Array.getElem_toList] at this
  · rw [beq_v2N, (vecs_wf (by decide)).2]
    exact root_chk
  · intro i hi
    rcases (gen_data i hi).2 with h0 | hp
    · exact Or.inl h0
    · right
      have hg := (gen_data i hi).1
      have h := List.all_eq_true.1 tree_chk i (List.mem_range.2 hi)
      have hne : (i == 0) = false := by simp; omega
      rw [hne, Bool.false_or, gL_get hg] at h
      refine ⟨⟨hp, hg⟩, ?_⟩
      rw [beq_v2N, gtabs_get hg, (frApply_enc (gm_enc hg) hi).1, (vecs_wf (by omega)).2]
      exact h
  · intro i hi j hj
    have h := List.all_eq_true.1 (List.all_eq_true.1 dist_chk i (List.mem_range.2 hi)) j
      (List.mem_range.2 hj)
    rw [beq_v2N, (vecs_wf hi).2, (vecs_wf (by omega)).2]
    exact h
  · intro n hn i hi
    have hs := sig_data n hn i hi
    refine ⟨hs, ?_⟩
    have h := List.all_eq_true.1 (List.all_eq_true.1 sig_chk n (List.mem_range.2 hn)) i
      (List.mem_range.2 hi)
    rw [gL_get hn] at h
    rw [beq_v2N, gtabs_get hn, (frApply_enc (gm_enc hn) hs).1, (vecs_wf hi).2]
    exact h

theorem cc_chk : (Nat.beq (mulJ c rm YA (oiK 0)) one && Nat.beq (mulJ c rm YB (oiK 1)) one &&
    !Nat.beq cmK one && Nat.beq (mulJ c rm (mulJ c rm cmK cmK) cmK) one &&
    (List.range 77).all fun i => Nat.beq (vecJ rm (vd i) cmK) (vd i)) = true := by quickRfl

theorem cc_ok : chkC = true := by
  have ha := gm_enc (n := 12) (by omega)
  have hb := gm_enc (n := 13) (by omega)
  simp only [gmK] at ha hb
  have hai := oInv_enc (i := 0) (by omega)
  have hbi := oInv_enc (i := 1) (by omega)
  simp only [Nat.add_zero, Nat.reduceAdd] at hai hbi
  have h := cc_chk
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  unfold chkC
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, wf_bool cMat_enc.1⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [mulT_frTable, eqRows_of (mul_enc hK ha hai) (id_enc hK)]
    exact h1
  · rw [mulT_frTable, eqRows_of (mul_enc hK hb hbi) (id_enc hK)]
    exact h2
  · rw [eqRows_of cMat_enc (id_enc hK)]
    exact h3
  · rw [mulT_frTable, mulT_frTable,
      eqRows_of (mul_enc hK (mul_enc hK cMat_enc cMat_enc) cMat_enc) (id_enc hK)]
    exact h4
  · rw [List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    rw [beq_v2N, (frApply_enc cMat_enc hi').1, (vecs_wf hi').2]
    exact List.all_eq_true.1 h5 i hi

@[expose] noncomputable def tOf (G : List Nat) : List Nat :=
  (List.range 77).foldl (fun acc i => strictL (if i == 0 then one
    else mulJ c rm (getN one G genData[i]!) (getN one acc parData[i]!)) fun v => acc ++ [v]) []

theorem strictL_eq' {α : Type} (y : Nat) (k : Nat → List α) : strictL y k = k y := by
  cases y <;> rfl

theorem push_get! {a : Array (Array V2)} {x : Array V2} {i : Nat} (hi : i < a.size) :
    (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos _ i (by simp; omega), getElem!_pos _ i hi, Array.getElem_push_lt]

theorem push_get!_size {a : Array (Array V2)} {x : Array V2} : (a.push x)[a.size]! = x := by
  rw [getElem!_pos _ a.size (by simp), Array.getElem_push_eq]

theorem tMats_enc : ∀ i < 77, WfA tMats[i]! ∧ encR tMats[i]! = getN one (tOf gL) i := by
  let f : Array (Array V2) → Nat → Array (Array V2) := fun acc i =>
    acc.push (if i == 0 then idRows else mulT gmats[genData[i]!]! (frTable acc[parData[i]!]!))
  let g : List Nat → Nat → List Nat := fun acc i => strictL (if i == 0 then one
    else mulJ c rm (getN one gL genData[i]!) (getN one acc parData[i]!)) fun v => acc ++ [v]
  have key : ∀ k ≤ 77, ((List.range k).foldl f #[]).size = k ∧ ((List.range k).foldl g []).length = k ∧
      ∀ i < k, WfA ((List.range k).foldl f #[])[i]! ∧
        encR ((List.range k).foldl f #[])[i]! = getN one ((List.range k).foldl g []) i := by
    intro k
    induction k with
    | zero => intro _; exact ⟨rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨hs, hl, hm⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons,
        List.foldl_nil, List.foldl_nil]
      generalize hA : (List.range k).foldl f #[] = A at hs hm ⊢
      generalize hL : (List.range k).foldl g [] = L at hl hm ⊢
      have hx : WfA (if k == 0 then idRows else mulT gmats[genData[k]!]! (frTable A[parData[k]!]!)) ∧
          encR (if k == 0 then idRows else mulT gmats[genData[k]!]! (frTable A[parData[k]!]!)) =
            (if k == 0 then one else mulJ c rm (getN one gL genData[k]!) (getN one L parData[k]!)) := by
        by_cases h0 : k = 0
        · subst h0
          exact id_enc hK
        · have hne : (k == 0) = false := by simp [h0]
          rw [hne]
          simp only [Bool.false_eq_true, ↓reduceIte]
          obtain ⟨hgk, hpk⟩ := gen_data k (by omega)
          have hp : parData[k]! < k := hpk.resolve_left h0
          rw [mulT_frTable, gL_get hgk]
          exact mul_enc hK (gm_enc hgk) (hm _ hp)
      simp only [f, g, strictL_eq']
      refine ⟨by simp [hs], by simp [hl], fun i hi => ?_⟩
      rw [getN_append, hl]
      by_cases hik : i < k
      · rw [if_pos hik, push_get! (by omega)]
        exact hm i hik
      · have e : i = k := by omega
        subst e
        have e2 : ∀ x : Array V2, (A.push x)[i]! = x := fun x => by
          rw [← hs]
          exact push_get!_size
        rw [if_neg (lt_irrefl i), Nat.sub_self, e2]
        exact hx
  intro i hi
  exact (key 77 le_rfl).2.2 i hi

@[expose] noncomputable def giK (n : Nat) : Nat :=
  if n < 12 then getN one QIs n
  else if n < 17 then oiK (n - 12)
  else if n < 28 then getN one Us (n - 17)
  else wordJ c rm one G5 G5i (negRev (mkKW.getD (n - 28) []))

@[expose] noncomputable def tiOf (GI : List Nat) : List Nat :=
  (List.range 77).foldl (fun acc i => strictL (if i == 0 then one
    else mulJ c rm (getN one acc parData[i]!) (getN one GI genData[i]!)) fun v => acc ++ [v]) []

theorem eSet_contains (X : Array V2) :
    eSet.contains X = (List.range 2048).any fun c => etaM c == X := by
  have key : ∀ (l : List Nat) (S : Std.HashSet (Array V2)),
      (l.foldl (fun S c => S.insert (etaM c)) S).contains X = (S.contains X || l.any fun c => etaM c == X) := by
    intro l
    induction l with
    | nil => intro S; simp
    | cons c l ih =>
      intro S
      rw [List.foldl_cons, ih, Std.HashSet.contains_insert, List.any_cons]
      cases S.contains X <;> cases etaM c == X <;> rfl
  unfold eSet
  rw [key, Std.HashSet.contains_empty, Bool.false_or]

@[expose] noncomputable def wv : Nat := Nat.lor w0Lo (Nat.shiftLeft w0Hi 64)

@[expose] noncomputable def evL : List Nat := smapK (fun e => vecJ rm wv (etaK c rm one Us e)) (rangeK 2048)

@[expose] noncomputable def idxF (v : Nat) (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun k => k)
    (fun x _ ih k => Bool.rec (motive := fun _ => Nat) (strictN (Nat.succ k) ih) k (Nat.beq v x)) l

theorem idxF_lt (v : Nat) : ∀ (l : List Nat) (k : Nat), v ∈ l → idxF v l k < k + l.length
  | [], _, h => absurd h List.not_mem_nil
  | x :: l, k, h => by
    change Bool.rec (motive := fun _ => Nat) (strictN (Nat.succ k) (idxF v l)) k (Nat.beq v x) < _
    cases hb : Nat.beq v x
    · have hv : v ∈ l := by
        rcases List.mem_cons.1 h with e | e
        · subst e
          simp at hb
        · exact e
      change strictN (Nat.succ k) (idxF v l) < _
      rw [CFSG.KC.J4Q.strictN_eq, Nat.succ_eq_add_one]
      have := idxF_lt v l (k + 1) hv
      simp only [List.length_cons]
      omega
    · simp

theorem evL_eq : evL = (List.range 2048).map fun e => vecJ rm wv (etaK c rm one Us e) := by
  rw [evL, smapK_eq, rangeK_eq]

theorem evL_length : evL.length = 2048 := by rw [evL_eq]; simp

@[expose] noncomputable def memK (ev : List Nat) (x : Nat) (b : Bool) : Bool :=
  strictB (idxF (vecJ rm wv x) ev 0) fun r => Bool.rec (motive := fun _ => Bool)
    (Nat.beq r 2048) (andB (Nat.blt r 2048) (Nat.beq (etaK c rm one Us r) x)) b

theorem memK_false {ev : List Nat} {x : Nat} (h : memK ev x false = true) :
    Nat.beq (idxF (vecJ rm wv x) ev 0) 2048 = true := by
  unfold memK at h
  rw [strictB_eq] at h
  exact h

theorem memK_true {ev : List Nat} {x : Nat} (h : memK ev x true = true) :
    andB (Nat.blt (idxF (vecJ rm wv x) ev 0) 2048)
      (Nat.beq (etaK c rm one Us (idxF (vecJ rm wv x) ev 0)) x) = true := by
  unfold memK at h
  rw [strictB_eq] at h
  exact h

theorem memK_sound {ev : List Nat} (hev : ev = (List.range 2048).map fun e => vecJ rm wv (etaK c rm one Us e))
    {X : Array V2} {x : Nat} (hX : WfA X ∧ encR X = x) {b : Bool}
    (h : memK ev x b = true) : eSet.contains X = b := by
  rw [eSet_contains]
  cases b
  · have h' := memK_false h
    rw [List.any_eq_false]
    intro e he hq
    have hXe : etaM e = X := (beq_iff_eq).1 hq
    have hmem : vecJ rm wv x ∈ ev := by
      rw [hev]
      refine List.mem_map.2 ⟨e, he, ?_⟩
      rw [← hX.2, ← hXe, (etaM_enc e).2]
    have hl := idxF_lt _ _ 0 hmem
    have hlen : ev.length = 2048 := by rw [hev]; simp
    rw [hlen, Nat.eq_of_beq_eq_true h'] at hl
    omega
  · have h' := memK_true h
    rw [andB_eq, Bool.and_eq_true] at h'
    rw [List.any_eq_true]
    refine ⟨idxF (vecJ rm wv x) ev 0, List.mem_range.2 (lt_of_blt h'.1), ?_⟩
    rw [beq_iff_eq]
    refine (CFSG.Sporadic.J4.eqRows_iff).1 ?_
    rw [eqRows_of (etaM_enc _) hX]
    exact h'.2

@[expose] noncomputable def v0K (ev TL TIL : List Nat) (i : Nat) : Bool :=
  strictB (getN one TL i) fun t => strictB (getN one TIL i) fun ti =>
    andB (andB (canonJ pad ti) (Nat.beq (mulJ c rm t ti) one))
      (Bool.rec (motive := fun _ => Bool)
        (orB (memK ev (mulJ c rm (mulJ c rm ti (etaK c rm one Us 422)) t) false)
          (orB (memK ev (mulJ c rm (mulJ c rm ti (etaK c rm one Us 553)) t) false)
            (memK ev (mulJ c rm (mulJ c rm ti ZM) t) false)))
        (andB (memK ev (mulJ c rm (mulJ c rm ti (etaK c rm one Us 422)) t) true)
          (andB (memK ev (mulJ c rm (mulJ c rm ti (etaK c rm one Us 553)) t) true)
            (memK ev (mulJ c rm (mulJ c rm ti ZM) t) true)))
        (i5List.contains i))

theorem v0_chk : (List.range 77).all (v0K evL (tOf gL) (tiOf (smapK giK (rangeK 32)))) = true := by
  quickRfl

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem v0_ok : chkV0 = true := by
  unfold chkV0
  rw [List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.1 hi
  have h := List.all_eq_true.1 v0_chk i hi
  unfold v0K at h
  rw [strictB_eq, strictB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hc, hm⟩, hb⟩ := h
  have hT := tMats_enc i hi'
  have hTi := invRows_enc hK hT.1 hc (by rw [hT.2]; exact hm)
  have h422 := etaM_enc 422
  have h553 := etaM_enc 553
  have hconj : ∀ {V : Array V2} {v : Nat}, WfA V ∧ encR V = v →
      WfA (mulT (mulT (invRows tMats[i]!) (frTable V)) (frTable tMats[i]!)) ∧
        encR (mulT (mulT (invRows tMats[i]!) (frTable V)) (frTable tMats[i]!)) =
          mulJ c rm (mulJ c rm (getN one (tiOf (smapK giK (rangeK 32))) i) v) (getN one (tOf gL) i) :=
    fun hV => by
      rw [mulT_frTable, mulT_frTable]
      exact mul_enc hK (mul_enc hK hTi hV) hT
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · unfold invOK
    rw [mulT_frTable, eqRows_of (mul_enc hK hT hTi) (id_enc hK)]
    exact hm
  · unfold inI5
    simp only [v0Tabs, List.all_cons, List.all_nil, Bool.and_true]
    rw [zT_eq]
    cases hcon : i5List.contains i
    · rw [hcon] at hb
      change orB _ (orB _ _) = true at hb
      rw [orB_eq, orB_eq, Bool.or_eq_true, Bool.or_eq_true] at hb
      rcases hb with hb | hb | hb
      · rw [memK_sound evL_eq (hconj h422) hb]
        simp
      · rw [memK_sound evL_eq (hconj h553) hb]
        simp
      · rw [memK_sound evL_eq (hconj zM_enc) hb]
        simp
    · rw [hcon] at hb
      change andB _ (andB _ _) = true at hb
      rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at hb
      rw [memK_sound evL_eq (hconj h422) hb.1, memK_sound evL_eq (hconj h553) hb.2.1,
        memK_sound evL_eq (hconj zM_enc) hb.2.2]
      rfl

open CFSG.Quasithin.J4M2 in
theorem c4200 : chkGens = true ∧ chkOrbit = true ∧ chkV0 = true ∧ chkC = true := ⟨gens_ok, orbit_ok, v0_ok, cc_ok⟩

end CertificateChecks.KernelJ4M2

end
