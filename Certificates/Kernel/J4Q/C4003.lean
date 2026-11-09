module

public import CFSG.Sporadic.J4.QT2LocCntNative
public import Certificates.Kernel.J4Q.LocM
public import Certificates.Kernel.J4Q.Orb
import Certificates.Kernel.J4Q.AllN
public import Certificates.Data.Kernel.J4Q.EvsMask
public import Certificates.Data.Kernel.J4Q.EvsBuckets
public import Certificates.Data.Kernel.TreeK
import CFSG.Certificates.Kernel.TreeKSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2

theorem blt_bitZ (m j : Nat) :
    Nat.blt (nat_lit 0) (Nat.land m (Nat.shiftLeft (nat_lit 1) j)) = m.testBit j := by
  change Nat.blt 0 (m &&& 1 <<< j) = _
  have e : m &&& 1 <<< j = if m.testBit j then 2 ^ j else 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases e : j = i
    · subst e
      cases h : m.testBit j <;> simp [Nat.testBit_two_pow_self]
    · cases h : m.testBit j <;> simp [e, Nat.testBit_two_pow_of_ne e]
  rw [e]
  cases m.testBit j
  · rfl
  · simp only [↓reduceIte]
    exact Nat.blt_eq.mpr (Nat.two_pow_pos j)

@[expose] noncomputable def hitZML (m : Nat) : Bool :=
  Nat.blt 0 (Nat.land zmlMask (Nat.shiftLeft 1 m))

@[expose] noncomputable def orMaskZ : List Nat → Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun c _ ih => Nat.lor ih (Nat.shiftLeft 1 c))

theorem zml_orMaskZ : Nat.beq zmlMask (orMaskZ ZML) = true := by quickRfl

theorem testBit_orMaskZ : ∀ (L : List Nat) (x : Nat), (orMaskZ L).testBit x = true → x ∈ L
  | [], x, h => by
    change (0 : Nat).testBit x = true at h
    rw [Nat.zero_testBit] at h
    exact absurd h Bool.false_ne_true
  | c :: L, x, h => by
    change (orMaskZ L ||| 1 <<< c).testBit x = true at h
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true] at h
    rcases h with h | h
    · exact List.mem_cons_of_mem c (testBit_orMaskZ L x h)
    · rw [of_decide_eq_true h]
      exact List.mem_cons_self

theorem hitZML_mem {x : Nat} (h : hitZML x = true) : x ∈ ZML := by
  have e : hitZML x = zmlMask.testBit x := blt_bitZ zmlMask x
  rw [e, Nat.eq_of_beq_eq_true zml_orMaskZ] at h
  exact testBit_orMaskZ ZML x h

@[expose] noncomputable def rowXZ (R : List Nat) : Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun x _ ih j c acc => ih (Nat.succ j) c
      (Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc x)
        (Nat.blt 0 (Nat.land c (Nat.shiftLeft 1 j))))) R

theorem rowXZ_eq (r : Nat → Nat) (c : Nat) : ∀ (R : List Nat) (j acc : Nat),
    (∀ i < R.length, R.getD i 0 = r (j + i)) →
    rowXZ R j c acc = (List.range' j R.length).foldl
      (fun acc k => if c.testBit k then acc ^^^ r k else acc) acc
  | [], _, _, _ => rfl
  | x :: R, j, acc, hR => by
    have hx : x = r j := hR 0 (Nat.succ_pos _)
    have hR' : ∀ i < R.length, R.getD i 0 = r (j + 1 + i) := fun i hi => by
      rw [Nat.add_assoc, Nat.add_comm 1 i]
      exact hR (i + 1) (Nat.succ_lt_succ hi)
    change rowXZ R (j + 1) c (Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc x)
      (Nat.blt (nat_lit 0) (Nat.land c (Nat.shiftLeft (nat_lit 1) j)))) = _
    rw [rowXZ_eq r c R (j + 1) _ hR', blt_bitZ, List.length_cons, List.range'_succ,
      List.foldl_cons, hx]
    cases c.testBit j <;> rfl

@[expose] noncomputable def actRZ (l c : Nat) : Nat := rowXZ (letterRows.getD l []) 0 c 0

theorem act_actRZ {l : Nat} (hl : l < 6) (c : Nat) : act (letters.getD l 0) c = actRZ l c := by
  have hi : letters.idxOf (letters.getD l 0) = l := by
    rcases l with _ | _ | _ | _ | _ | _ | l
    all_goals first | rfl | omega
  have hlen : (letterRows.getD l []).length = 11 := by
    rcases l with _ | _ | _ | _ | _ | _ | l
    all_goals first | rfl | omega
  unfold act rowsXor actRZ
  rw [rowXZ_eq (letterRow (letters.getD l 0)) c _ 0 0 (fun i _ => by
    rw [Nat.zero_add]
    unfold letterRow
    rw [hi]), hlen, List.range_eq_range']

theorem zml_clos : (ZML.all fun c => (List.range 6).all fun l => hitZML (actRZ l c)) = true := by
  quickRfl

theorem zml_lt : (ZML.all fun c => decide (c < 2048)) = true := by quickRfl

theorem zml_len : Nat.beq ZML.length 1771 = true := by quickRfl

theorem zml_dist : CFSG.KC.TreeK.distinctK 11 ZML = true := by quickRfl

theorem zMasks_ok : chkZMasks = true := by
  have hlen := Nat.eq_of_beq_eq_true zml_len
  have h1 : (ZML.all fun c => decide (c < 2048) && letters.all fun ℓ => ZML.contains (act ℓ c)) =
      true := by
    refine List.all_eq_true.2 fun c hc => ?_
    have hcl := List.all_eq_true.1 (List.all_eq_true.1 zml_clos c hc)
    have hm : ∀ l < 6, ZML.contains (act (letters.getD l 0) c) = true := fun l hl => by
      rw [act_actRZ hl]
      exact List.elem_eq_true_of_mem (hitZML_mem (hcl l (List.mem_range.2 hl)))
    rw [Bool.and_eq_true]
    refine ⟨List.all_eq_true.1 zml_lt c hc, ?_⟩
    simp only [letters, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide),
      hm 4 (by decide), hm 5 (by decide)⟩
  have h2 : (ZML.length == 1771) = true := by rw [hlen]; rfl
  have h3 : decide ZML.Nodup = true := decide_eq_true (CFSG.KC.TreeK.distinctK_sound zml_dist)
  have h4 : ZML.contains 3 = true := by quickRfl
  have h5 : ZML.contains 1131 = true := by quickRfl
  have h6 : ((orbits.getD 1 (3, [], [])).1 == 3) = true := by quickRfl
  unfold chkZMasks
  rw [zMasks_ZML, h1, h2, h3, h4, h5, h6]
  rfl

@[expose] noncomputable def CZs : List (List Nat) := [CZ_0, CZ_1, CZ_2, CZ_3, CZ_4, CZ_5]

@[expose] noncomputable def boolEqK (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB b) b a

theorem boolEqK_spec {a b : Bool} (h : boolEqK a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

@[expose] noncomputable def hitK (v : Nat) : Bool :=
  Nat.blt 0 (Nat.land evsMask (Nat.shiftLeft 1 (Nat.land v 65535)))

theorem evs_hit : EVS.all hitK = true := by quickRfl

@[expose] noncomputable def inB (v : Nat) : Bool :=
  ((evsB.getD (Nat.land (Nat.shiftRight v 5) 31) []).getD (Nat.land v 31) []).any fun u => Nat.beq v u

theorem evsB_all : EVS.all inB = true := by quickRfl

theorem evsB_perm : eqLK (CFSG.KC.TreeK.sortP 11 (evsB.map List.flatten).flatten)
    (CFSG.KC.TreeK.sortP 11 EVS) = true := by quickRfl

theorem mem_getD_flatZ {α : Type} {L : List (List α)} {i : Nat} {u : α} (h : u ∈ L.getD i []) :
    ∃ l ∈ L, u ∈ l := by
  rw [List.getD_eq_getElem?_getD] at h
  cases e : L[i]? with
  | none =>
    rw [e] at h
    exact absurd h List.not_mem_nil
  | some l =>
    rw [e] at h
    exact ⟨l, List.mem_of_getElem? e, h⟩

theorem evsB_iff (v : Nat) : inB v = true ↔ v ∈ EVS := by
  constructor
  · intro h
    unfold inB at h
    obtain ⟨u, hu, hb⟩ := List.any_eq_true.1 h
    rw [Nat.eq_of_beq_eq_true hb]
    obtain ⟨l1, hl1, hu1⟩ := mem_getD_flatZ hu
    obtain ⟨l2, hl2, hl12⟩ := mem_getD_flatZ hl1
    have h1 : u ∈ (evsB.map List.flatten).flatten :=
      List.mem_flatten.2 ⟨l2.flatten, List.mem_map_of_mem hl2, List.mem_flatten.2 ⟨l1, hl12, hu1⟩⟩
    have h3 := (CFSG.KC.TreeK.sortP_perm 11 _).mem_iff.2 h1
    rw [eqLK_spec evsB_perm] at h3
    exact (CFSG.KC.TreeK.sortP_perm 11 EVS).mem_iff.1 h3
  · intro h
    exact List.all_eq_true.1 evsB_all v h

@[expose] noncomputable def inEVS (v : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (inB v) (hitK v)

theorem inEVS_eq (v : Nat) : inEVS v = EVS.any fun u => notB (neN v u) := by
  have key : (EVS.any fun u => notB (neN v u)) = true ↔ v ∈ EVS := by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨u, hu, hvu⟩
      have hb : Nat.beq v u = true := by
        revert hvu
        unfold neN
        cases Nat.beq v u <;> decide
      rw [Nat.eq_of_beq_eq_true hb]
      exact hu
    · intro hv
      refine ⟨v, hv, ?_⟩
      unfold neN
      rw [Nat.beq_refl]
      rfl
  rw [Bool.eq_iff_iff, key]
  unfold inEVS
  cases h : hitK v
  · change false = true ↔ _
    refine ⟨fun h' => absurd h' (by decide), fun hv => ?_⟩
    rw [List.all_eq_true.1 evs_hit v hv] at h
    exact absurd h (by decide)
  · exact evsB_iff v

theorem zml_hitZ : ZML.all hitZML = true := by quickRfl

@[expose] noncomputable def leafZK (i m y : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (boolEqK (strictB (vecJ rm y (getN one MLIs i)) inEVS) ((CZs.getD i []).contains m)) (hitZML m)

@[expose] noncomputable def dfsEtaK (leaf : Nat → Nat → Bool) (Ts : List Nat) : Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool) (fun _ m x => leaf m x)
    (fun T _ ih j m x => Bool.rec (motive := fun _ => Bool) false
      (strictB (vecJ rm x T) fun x' => ih (Nat.succ j) (Nat.add m (Nat.shiftLeft 1 j)) x')
      (ih (Nat.succ j) m x)) Ts

@[expose] noncomputable def zWalkK (i : Nat) : Bool :=
  strictB (vecJ rm (v2N w0) (getN one MLs i)) fun x => dfsEtaK (leafZK i) Us 0 0 x

#j4q_all CFSG.KD.J4Q.ZWalk CertificateChecks.KernelJ4Q.zWalkK 6

theorem dfsEtaK_sound (leaf : Nat → Nat → Bool) : ∀ (Ts : List Nat) (j m x M : Nat),
    dfsEtaK leaf Ts j m x = true → M % 2 ^ j = m → M < 2 ^ (j + Ts.length) →
    leaf M (vecEtaFrom rm Ts M j x) = true
  | [], j, m, x, M, h, hm, hM => by
    rw [List.length_nil, Nat.add_zero] at hM
    rw [Nat.mod_eq_of_lt hM] at hm
    subst hm
    exact h
  | T :: Ts, j, m, x, M, h, hm, hM => by
    have hd : dfsEtaK leaf (T :: Ts) j m x = Bool.rec (motive := fun _ => Bool) false
        (strictB (vecJ rm x T) fun x' => dfsEtaK leaf Ts (Nat.succ j) (Nat.add m (Nat.shiftLeft 1 j)) x')
        (dfsEtaK leaf Ts (Nat.succ j) m x) := rfl
    have hv : vecEtaFrom rm (T :: Ts) M j x = Bool.rec (motive := fun _ => Nat)
        (vecEtaFrom rm Ts M (j + 1) x) (CFSG.KC.Loop.strictN (vecJ rm x T) (vecEtaFrom rm Ts M (j + 1)))
        (Nat.blt (nat_lit 0) (Nat.land M (Nat.shiftLeft (nat_lit 1) j))) := rfl
    have hl : j + (T :: Ts).length = j + 1 + Ts.length := by
      rw [List.length_cons]
      omega
    rw [hl] at hM
    have hmod : M % 2 ^ (j + 1) = M % 2 ^ j + 2 ^ j * (M / 2 ^ j % 2) := Nat.mod_pow_succ
    have h2 := Nat.mod_lt (M / 2 ^ j) (by decide : 2 > 0)
    rw [hd] at h
    rw [hv, blt_bitZ, Nat.testBit_eq_decide_div_mod_eq]
    cases h1 : dfsEtaK leaf Ts (Nat.succ j) m x
    · rw [h1] at h
      exact absurd h Bool.false_ne_true
    rw [h1, strictB_eq] at h
    by_cases hb : M / 2 ^ j % 2 = 1
    · have hb' : decide (M / 2 ^ j % 2 = 1) = true := decide_eq_true hb
      rw [hb']
      change leaf M (CFSG.KC.Loop.strictN (vecJ rm x T) (vecEtaFrom rm Ts M (j + 1))) = true
      rw [strictN_eq]
      refine dfsEtaK_sound leaf Ts (j + 1) _ (vecJ rm x T) M h ?_ hM
      rw [hmod, hb, hm, Nat.mul_one]
      change m + 2 ^ j = m + 1 <<< j
      rw [Nat.one_shiftLeft]
    · have hb' : decide (M / 2 ^ j % 2 = 1) = false := decide_eq_false hb
      rw [hb']
      change leaf M (vecEtaFrom rm Ts M (j + 1) x) = true
      refine dfsEtaK_sound leaf Ts (j + 1) m x M h1 ?_ hM
      rw [hmod, hm, (by omega : M / 2 ^ j % 2 = 0), Nat.mul_zero, Nat.add_zero]

theorem us_len11 : Us.length = 11 := rfl

theorem any_congr_mem {α : Type} {f g : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.any f = l.any g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.any_cons, List.any_cons, h x List.mem_cons_self,
      any_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem candZ_len {i : Nat} (hi : i < 6) :
    (candZ (locMats ()) (locInvs ()) (1 + 1 * i)).length =
      (ZML.filter fun c => (CZs.getD i []).contains c).length := by
  unfold candZ
  simp only []
  rw [zMasks_ZML]
  congr 1
  apply List.filter_congr
  intro m hm
  have hw := ZWalk.all i hi
  rw [zWalkK, strictB_eq] at hw
  have hlt : m < 2 ^ (0 + Us.length) := by
    rw [us_len11]
    exact of_decide_eq_true (List.all_eq_true.1 zml_lt m hm)
  have hs := dfsEtaK_sound (leafZK i) Us 0 0 _ m hw (Nat.mod_one m) hlt
  have h2 : boolEqK (strictB (cvK i m) inEVS) ((CZs.getD i []).contains m) = true := by
    unfold leafZK at hs
    rw [List.all_eq_true.1 zml_hitZ m hm] at hs
    exact hs
  rw [← boolEqK_spec h2, strictB_eq, inEVS_eq]
  unfold memEVec evsOf
  simp only []
  obtain ⟨hwv, hvv⟩ := conjVec_enc hi m
  rw [EVS_eq, List.any_map, List.any_map]
  apply any_congr_mem
  intro c' hc'
  have h' : (etaVec ((uTab (locMats ()) (locInvs ())).map frTable) 11 c').wf = true ∧
      v2N (etaVec ((uTab (locMats ()) (locInvs ())).map frTable) 11 c') = vecEtaK rm Us c' (v2N w0) :=
    v2N_etaVec hK uTab_enc (by simp [uTab, Us]) w0_wf c'
  change (!differs _ _) = notB (neN _ _)
  rw [differs_eq hwv h'.1, hvv, h'.2, notB_eq]

theorem candZ_len' (ℓ : Nat) (h1 : 1 ≤ ℓ) (h6 : ℓ ≤ 6) :
    (candZ (locMats ()) (locInvs ()) ℓ).length =
      (ZML.filter fun c => (CZs.getD (ℓ - 1) []).contains c).length := by
  obtain ⟨i, rfl⟩ : ∃ i, ℓ = 1 + 1 * i := ⟨ℓ - 1, by omega⟩
  have : 1 + 1 * i - 1 = i := by omega
  rw [this]
  exact candZ_len (by omega)

theorem cntZ_ok : chkCntZ (locMats ()) (locInvs ()) = true := by
  unfold chkCntZ
  rw [candZ_len' 1 (by decide) (by decide), candZ_len' 2 (by decide) (by decide),
    candZ_len' 3 (by decide) (by decide), candZ_len' 4 (by decide) (by decide),
    candZ_len' 5 (by decide) (by decide), candZ_len' 6 (by decide) (by decide)]
  quickRfl

theorem one_canon : andB (canonJ pad one) (Nat.beq (mulJ c rm one one) one) = true := by quickRfl

theorem pathInv_ok : ((List.range 7).all fun ℓ =>
    eqRows (mulRows (pathRows (repPaths.getD ℓ [])) (invRows (pathRows (repPaths.getD ℓ []))))
      idRows) = true := by
  refine List.all_eq_true.2 fun ℓ hℓ => ?_
  have hℓ' := List.mem_range.1 hℓ
  rcases ℓ with _ | i
  · have h0 : pathRows (repPaths.getD 0 []) = idRows () := rfl
    rw [h0]
    have h := one_canon
    rw [andB_eq, Bool.and_eq_true] at h
    have hI := invRows_enc hK wf_idRows h.1 (by rw [enc_idRows hK]; exact h.2)
    rw [eqRows_of (mul_enc hK (id_enc hK) hI) (id_enc hK)]
    exact h.2
  · have : i + 1 = 1 + 1 * i := by omega
    rw [this]
    have hMi := pathMi_enc (i := i) (by omega)
    rw [eqRows_of (mul_enc hK (pathM_enc (by omega)) ⟨hMi.1, hMi.2.1⟩) (id_enc hK)]
    exact hMi.2.2

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2 in
open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT in
theorem c4003 : (chkZMasks = true)
    ∧ (chkCntZ (locMats ()) (locInvs ()) = true)
    ∧ (vorbOK locTabs rep6Vec orb6 28336 = true)
    ∧ ((List.range 7).all (fun ℓ =>
          eqRows (mulRows (pathRows (repPaths.getD ℓ [])) (invRows (pathRows (repPaths.getD ℓ []))))
            idRows) = true) := ⟨zMasks_ok, cntZ_ok, orb6_vorbOK, pathInv_ok⟩

end CertificateChecks.KernelJ4Q

end
