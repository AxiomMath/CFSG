module

public import Certificates.Kernel.Fi22Uq.Checks
public import Certificates.Kernel.Fi22Syl.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueTabCheck
public import CFSG.Certificates.Kernel.Spor.RelTR
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases
public import Certificates.Data.CFSGNative.Fi22.Inv

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelFi22Uq.c25230act0All CertificateChecks.KernelFi22Uq.c25230act0 16
#kon_join CertificateChecks.KernelFi22Uq.c25230act1All CertificateChecks.KernelFi22Uq.c25230act1 2

namespace CertificateChecks.KernelFi22Uq

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.TW
  CFSG.KS.Fi22S CFSG.KS.Fi22Cent CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native CertificateChecks.KernelFi22S CFSG.EvenSporadicStandard.TwoFi22.DS81
  CFSG.EvenSporadicStandard.TwoFi22.FrameJ

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem inJ_eq {f g : Nat → Nat} (hf : InJ f) (hg : InJ g) (h : ∀ q ∈ QL, f q = g q) :
    ∀ x < 3510, f x = g x := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  have e : b⁻¹ * a = 1 := sep _ fun t ht => by
    have hm : chainQ[t]! ∈ QL := by
      rw [← chain_hyp.chk.1, getElem!_pos chainQ t ht]
      exact Array.getElem_mem_toList ht
    have hq := QL_lt _ hm
    rw [idx_mul, ← ha _ hq, h _ hm, hb _ hq, idx_inv_idx]
  have e' : b = a := inv_mul_eq_one.1 e
  intro x hx
  rw [ha x hx, hb x hx, e']

theorem eqQL_spec (F G : Nat → Nat) : ∀ l : List Nat,
    List.rec (motive := fun _ => Bool) true (fun q _ ih => bAnd(Nat.beq (F q) (G q), ih)) l = true →
      ∀ q ∈ l, F q = G q
  | [], _ => by simp
  | a :: l, h => by
    change bAnd(Nat.beq (F a) (G a), List.rec (motive := fun _ => Bool) true
      (fun q _ ih => bAnd(Nat.beq (F q) (G q), ih)) l) = true at h
    rw [Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact h.1
    · exact eqQL_spec F G l h.2 q hq

theorem neQL_spec (F G : Nat → Nat) : ∀ l : List Nat,
    List.rec (motive := fun _ => Bool) false (fun q _ ih => bIf(Nat.beq (F q) (G q), ih, true)) l =
      true → ∃ q ∈ l, F q ≠ G q
  | [], h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | a :: l, h => by
    change bIf(Nat.beq (F a) (G a), List.rec (motive := fun _ => Bool) false
      (fun q _ ih => bIf(Nat.beq (F q) (G q), ih, true)) l, true) = true at h
    rw [Raw.Orb.bIf_eq] at h
    by_cases e : F a = G a
    · rw [ite_eq_left (by rw [Nat.beq_eq]; exact e)] at h
      obtain ⟨q, hq, hne⟩ := neQL_spec F G l h
      exact ⟨q, List.mem_cons_of_mem a hq, hne⟩
    · exact ⟨a, List.mem_cons_self, e⟩

theorem eqQ_spec {F G : Nat → Nat} (h : eqQ F G = true) : ∀ q ∈ QL, F q = G q :=
  eqQL_spec F G QL h

theorem neQ_spec {F G : Nat → Nat} (h : neQ F G = true) : ∃ q ∈ QL, F q ≠ G q :=
  neQL_spec F G QL h

theorem tab_eq {X Y : Table} {f g : Nat → Nat} (hX : TR 3510 X f) (hY : TR 3510 Y g)
    (h : ∀ x < 3510, f x = g x) : X = Y := by
  refine Array.ext (by rw [hX.1, hY.1]) fun i h1 h2 => ?_
  have hi : i < 3510 := by rw [← hX.1]; exact h1
  have a1 := (hX.2 i hi).1
  have a2 := (hY.2 i hi).1
  unfold ap at a1 a2
  rw [getElem!_pos X i h1] at a1
  rw [getElem!_pos Y i h2] at a2
  exact UInt32.toNat_inj.1 (by rw [a1, a2, h i hi])

theorem tab_beq {X Y : Table} {f g : Nat → Nat} (hX : TR 3510 X f) (hY : TR 3510 Y g)
    (hf : InJ f) (hg : InJ g) (h : ∀ q ∈ QL, f q = g q) : (X == Y) = true :=
  beq_iff_eq.2 (tab_eq hX hY (inJ_eq hf hg h))

theorem tab_bne {X Y : Table} {f g : Nat → Nat} (hX : TR 3510 X f) (hY : TR 3510 Y g)
    (h : ∃ q ∈ QL, f q ≠ g q) : (X != Y) = true := by
  rw [bne_iff_ne]
  intro he
  obtain ⟨q, hq, hne⟩ := h
  have hq' := QL_lt q hq
  have e : ap X q = ap Y q := by rw [he]
  rw [(hX.2 q hq').1, (hY.2 q hq').1] at e
  exact hne e

theorem arr_get (A : Array Nat) (n : Nat) : A[n]! = A.toList[n]! := Array.getElem!_toList.symm

theorem dp_lt : ∀ j < 22, (uqDp[j]!).1 < 1024 ∧ (uqDp[j]!).2 < 128 := by decide

theorem bas_lt : ∀ i < 10, uqBas[i]! < 22 := by decide

theorem dp_size : uqDp.size = 22 := rfl

theorem bas_size : uqBas.size = 10 := rfl

theorem inJ_dK {j : Nat} (hj : j < 22) : InJ (dK j) := by
  obtain ⟨h0, h1⟩ := dp_lt j hj
  exact (inJ_gK h0 h1).congr fun _ _ => rfl

theorem inJ_bK {i : Nat} (hi : i < 10) : InJ (bK i) :=
  (inJ_dK (bas_lt i hi)).congr fun _ _ => rfl

theorem inJ_wP {l k : Nat} (hl : l < 2) (hk : k < CNTS l) : InJ (wP l k) :=
  (inJ_wPF hl k k hk le_rfl).congr fun _ _ => rfl

theorem dP_TR {j : Nat} (hj : j < 22) :
    TR 3510 (compT 3510 (tabK 0)[(uqDp[j]!).1]! (tabK 1)[(uqDp[j]!).2]!) (dK j) := by
  obtain ⟨c0, c1⟩ := cnts
  obtain ⟨h0, h1⟩ := dp_lt j hj
  refine CFSG.KS.Fi22L.TR_congr (CFSG.KS.RelTR.compT_TR (tab_TR (i := 0) (by norm_num) (by rw [c0]; exact h0))
    (tab_TR (i := 1) (by norm_num) (by rw [c1]; exact h1))) fun x _ => ?_
  unfold dK gK
  rw [Raw.Orb.strictN_eq]

noncomputable abbrev DT : Array Table := uqD (tabK 0) (tabK 1) uqDp

noncomputable abbrev BT : Array Table := uqBt DT uqBas

theorem DT_size : DT.size = 22 := by
  unfold DT uqD
  rw [Array.size_map, dp_size]

theorem DT_get {j : Nat} (hj : j < 22) :
    DT[j]! = compT 3510 (tabK 0)[(uqDp[j]!).1]! (tabK 1)[(uqDp[j]!).2]! := by
  unfold DT uqD
  rw [getElem!_pos _ j (by rw [Array.size_map, dp_size]; exact hj), Array.getElem_map,
    ← getElem!_pos uqDp j (by rw [dp_size]; exact hj)]

theorem DT_TR {j : Nat} (hj : j < 22) : TR 3510 DT[j]! (dK j) := by
  rw [DT_get hj]
  exact dP_TR hj

theorem BT_TR {i : Nat} (hi : i < 10) : TR 3510 BT[i]! (bK i) := by
  have e : BT[i]! = DT[uqBas[i]!]! := by
    unfold BT uqBt
    rw [getElem!_pos _ i (by rw [Array.size_map, bas_size]; exact hi), Array.getElem_map,
      ← getElem!_pos uqBas i (by rw [bas_size]; exact hi)]
  rw [e]
  exact DT_TR (bas_lt i hi)

theorem fj_ok {j : Nat} (hj : j < 22) :
    fjDLeaf orbL.alpha (tabK 0)[(uqDp[j]!).1]! (tabK 1)[(uqDp[j]!).2]! = true := by
  have hT := dP_TR hj
  have hG := inJ_dK hj
  have hl := Raw.Orb.allN_iff.1 c25230leaf_ok j hj
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true] at hl
  obtain ⟨h1, h2, h3⟩ := hl
  unfold fjDLeaf
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hS : InJ (KernelFi22S.sq (dK j)) :=
      (hG.comp hG).congr fun x _ => by unfold KernelFi22S.sq; rw [Raw.Orb.strictN_eq]
    unfold CFSG.Sporadic.Th.Native.invoOK
    rw [TW.allIn_iff]
    intro x hx
    have e := hS.eq_id h1 x hx
    unfold KernelFi22S.sq at e
    rw [Raw.Orb.strictN_eq] at e
    rw [(hT.2 x hx).1, (hT.2 _ (hT.2 x hx).2).1, e, beq_self_eq_true]
  · obtain ⟨q, hq, hne⟩ := anyMv_spec h2
    have hq' := QL_lt q hq
    refine not_allIn hq' ?_
    rw [(hT.2 q hq').1]
    simpa using hne
  · have hH : InJ fun x => strictN (gA x) (dK j) :=
      (hG.comp inJ_gA).congr fun x _ => Raw.Orb.strictN_eq _ _
    have hC : InJ (cb fun x => strictN (gA x) (dK j)) :=
      (hH.comp (hH.comp hH)).congr fun x _ => by unfold cb; simp only [Raw.Orb.strictN_eq]
    refine order3OK_of (H := fun x => dK j (gA x)) (fun x hx => ⟨?_, ?_⟩) fun x hx => ?_
    · rw [ap_compT' _ _ hx, (KernelFi22C.alpha_get hx).1]
      change ap _ (Fi22Cent.gA x) = _
      rw [(hT.2 _ (gA_lt' hx)).1]
    · exact hG.lt (gA_lt' hx)
    · have e := hC.eq_id h3 x hx
      unfold cb at e
      simp only [Raw.Orb.strictN_eq] at e
      exact e

theorem dist_ok {i j : Nat} (hi : i < 22) (hj : j < 22) : (i == j || DT[i]! != DT[j]!) = true := by
  rw [Bool.or_eq_true]
  rcases Nat.lt_trichotomy j i with hji | rfl | hij
  · exact Or.inr (tab_bne (DT_TR hi) (DT_TR hj)
      (neQ_spec (Raw.Orb.allN_iff.1 (Raw.Orb.allN_iff.1 c25230dist_ok i hi) j hji)))
  · exact Or.inl (beq_self_eq_true _)
  · obtain ⟨q, hq, hne⟩ :=
      neQ_spec (Raw.Orb.allN_iff.1 (Raw.Orb.allN_iff.1 c25230dist_ok j hj) i hij)
    exact Or.inr (tab_bne (DT_TR hi) (DT_TR hj) ⟨q, hq, Ne.symm hne⟩)

theorem comm_ok {i j : Nat} (hi : i < 10) (hj : j < 10) :
    (compT 3510 BT[i]! BT[j]! == compT 3510 BT[j]! BT[i]!) = true := by
  have hij := (inJ_bK hi).comp (inJ_bK hj)
  have hji := (inJ_bK hj).comp (inJ_bK hi)
  refine tab_beq (CFSG.KS.RelTR.compT_TR (BT_TR hi) (BT_TR hj))
    (CFSG.KS.RelTR.compT_TR (BT_TR hj) (BT_TR hi)) hij hji fun q hq => ?_
  rcases Nat.lt_trichotomy j i with h | rfl | h
  · have e := eqQ_spec (Raw.Orb.allN_iff.1 (Raw.Orb.allN_iff.1 c25230comm_ok i hi) j h) q hq
    simp only [Raw.Orb.strictN_eq] at e
    exact e
  · rfl
  · have e := eqQ_spec (Raw.Orb.allN_iff.1 (Raw.Orb.allN_iff.1 c25230comm_ok j hj) i h) q hq
    simp only [Raw.Orb.strictN_eq] at e
    exact e.symm

theorem phi_gen (m : Nat) : ∀ l : List Nat, (∀ i ∈ l, i < 10) →
    TR 3510 (l.foldr (fun i P => if m.testBit i then compT 3510 BT[i]! P else P) (idT 3510))
      (phiL m l) ∧ InJ (phiL m l)
  | [], _ => ⟨idT_TR (by norm_num), InJ.id⟩
  | i :: l, h => by
    obtain ⟨ih1, ih2⟩ := phi_gen m l fun j hj => h j (List.mem_cons_of_mem _ hj)
    have hi := h i List.mem_cons_self
    have e : ∀ x, phiL m (i :: l) x = if m.testBit i then bK i (phiL m l x) else phiL m l x := by
      intro x
      change strictN (phiL m l x) (fun y => nIf(m.testBit i, bK i y, y)) = _
      rw [Raw.Orb.strictN_eq]
      cases m.testBit i <;> rfl
    simp only [List.foldr_cons]
    by_cases hm : m.testBit i = true
    · rw [if_pos hm]
      exact ⟨CFSG.KS.Fi22L.TR_congr (CFSG.KS.RelTR.compT_TR (BT_TR hi) ih1) fun x _ => by rw [e, if_pos hm],
        ((inJ_bK hi).comp ih2).congr fun x _ => by rw [e, if_pos hm]⟩
    · rw [if_neg hm]
      exact ⟨CFSG.KS.Fi22L.TR_congr ih1 fun x _ => by rw [e, if_neg hm],
        ih2.congr fun x _ => by rw [e, if_neg hm]⟩

theorem phi_ok {j : Nat} (hj : j < 22) : (uqPhiTab BT uqW[j]! == DT[j]!) = true := by
  obtain ⟨h1, h2⟩ := phi_gen uqW[j]! (List.range 10) fun _ hi => List.mem_range.1 hi
  exact tab_beq h1 (DT_TR hj) h2 (inJ_dK hj) (eqQ_spec (Raw.Orb.allN_iff.1 c25230phi_ok j hj))

theorem actRow_spec {l k : Nat} : ∀ (r : List Nat) (i0 : Nat), actRow l k r i0 = true →
    i0 + r.length = 10 ∧ ∀ n < r.length, r[n]! < 22 ∧
      ∀ q ∈ QL, wP l k (bK (i0 + n) q) = dK r[n]! (wP l k q)
  | [], i0, h => by
    change Nat.beq i0 10 = true at h
    rw [Nat.beq_eq] at h
    exact ⟨by simpa using h, fun n hn => absurd hn (by simp)⟩
  | s :: r, i0, h => by
    change bAnd(Nat.blt s 22, bAnd(eqQ (fun x => strictN (bK i0 x) (wP l k))
      (fun x => strictN (wP l k x) (dK s)), actRow l k r (Nat.succ i0))) = true at h
    rw [Raw.Orb.bAnd_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨ih1, ih2⟩ := actRow_spec r (Nat.succ i0) h3
    refine ⟨by simp only [List.length_cons]; omega, fun n hn => ?_⟩
    rcases n with _ | n
    · refine ⟨by simpa using h1, fun q hq => ?_⟩
      have e := eqQ_spec h2 q hq
      simp only [Raw.Orb.strictN_eq] at e
      simpa using e
    · have hn' : n < r.length := by simp only [List.length_cons] at hn; omega
      obtain ⟨a1, a2⟩ := ih2 n hn'
      refine ⟨by simpa using a1, fun q hq => ?_⟩
      have e := a2 q hq
      have e2 : i0 + (n + 1) = Nat.succ i0 + n := by omega
      rw [e2]
      simpa using e

theorem row0 {k : Nat} (hk : k < 1024) :
    actRow 0 k (uqDecode uqSg0S[k]!).toList 0 = true := by
  have hs : k / 64 < 16 := by omega
  have h := c25230act0All (k / 64) hs
  unfold c25230act0 at h
  have h' := Raw.Orb.allN_iff.1 h (k % 64) (Nat.mod_lt _ (by norm_num))
  rw [Raw.Orb.strictB_eq] at h'
  have e : Nat.add (Nat.mul (k / 64) 64) (k % 64) = k := Nat.div_add_mod' k 64
  rw [e] at h'
  exact h'

theorem row1 {k : Nat} (hk : k < 128) :
    actRow 1 k (uqDecode uqSg1S[k]!).toList 0 = true := by
  have hs : k / 64 < 2 := by omega
  have h := c25230act1All (k / 64) hs
  unfold c25230act1 at h
  have h' := Raw.Orb.allN_iff.1 h (k % 64) (Nat.mod_lt _ (by norm_num))
  rw [Raw.Orb.strictB_eq] at h'
  have e : Nat.add (Nat.mul (k / 64) 64) (k % 64) = k := Nat.div_add_mod' k 64
  rw [e] at h'
  exact h'

theorem act_ok {l : Nat} (hl : l < 2) {S : Array String} (hS : S.size = CNTS l)
    (hrow : ∀ k < CNTS l, actRow l k (uqDecode S[k]!).toList 0 = true) :
    uqActOK (tabK l) DT BT (S.map uqDecode) = true := by
  unfold uqActOK
  rw [TW.allIn_iff]
  intro k hk
  rw [tabK_size hl] at hk
  have hkS : k < S.size := by rw [hS]; exact hk
  have esg : (S.map uqDecode)[k]! = uqDecode S[k]! := by
    rw [getElem!_pos _ k (by rw [Array.size_map]; exact hkS), Array.getElem_map,
      getElem!_pos S k hkS]
  obtain ⟨hlen, hr⟩ := actRow_spec _ 0 (hrow k hk)
  dsimp only
  rw [esg, Bool.and_eq_true, beq_iff_eq, TW.allIn_iff]
  refine ⟨by rw [← Array.length_toList]; omega, fun i hi => ?_⟩
  obtain ⟨hs, hq⟩ := hr i (by omega)
  rw [arr_get (uqDecode S[k]!) i, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hs, ?_⟩
  have eD : (DT.map fun d => compT 3510 d (tabK l)[k]!)[(uqDecode S[k]!).toList[i]!]! =
      compT 3510 DT[(uqDecode S[k]!).toList[i]!]! (tabK l)[k]! := by
    rw [getElem!_pos _ _ (by rw [Array.size_map, DT_size]; exact hs), Array.getElem_map,
      ← getElem!_pos DT _ (by rw [DT_size]; exact hs)]
  rw [eD]
  have hT := tab_TR hl hk
  exact tab_beq (CFSG.KS.RelTR.compT_TR hT (BT_TR hi)) (CFSG.KS.RelTR.compT_TR (DT_TR hs) hT)
    ((inJ_wP hl hk).comp (inJ_bK hi)) ((inJ_dK hs).comp (inJ_wP hl hk))
    fun q hq' => by simpa using hq q hq'

theorem tab_ok : uqTabCheckT orbL.alpha (tabK 0) (tabK 1) uqDp uqBas uqW uqSg0 uqSg1 = true := by
  obtain ⟨c0, c1⟩ := cnts
  unfold uqTabCheckT
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp [uqBas]
  · simp [uqW]
  · rw [Array.all_eq_true]
    intro j hj
    rw [dp_size] at hj
    rw [← getElem!_pos uqDp j (by rw [dp_size]; exact hj)]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    obtain ⟨h0, h1⟩ := dp_lt j hj
    refine ⟨⟨by rw [tabK_size (by norm_num), c0]; exact h0,
      by rw [tabK_size (by norm_num), c1]; exact h1⟩, fj_ok hj⟩
  · rw [TW.allIn_iff]
    intro i hi
    rw [TW.allIn_iff]
    intro j hj
    exact dist_ok hi hj
  · rw [TW.allIn_iff]
    intro i hi
    rw [TW.allIn_iff]
    intro j hj
    exact comm_ok hi hj
  · rw [TW.allIn_iff]
    intro j hj
    exact phi_ok hj
  · rw [tabK_size (by norm_num), c0]
    unfold uqSg0
    rw [Array.size_map]
    rfl
  · rw [tabK_size (by norm_num), c1]
    unfold uqSg1
    rw [Array.size_map]
    rfl
  · exact act_ok (l := 0) (by norm_num) (S := uqSg0S) (by rw [c0]; rfl)
      fun k hk => row0 (by rw [c0] at hk; exact hk)
  · exact act_ok (l := 1) (by norm_num) (S := uqSg1S) (by rw [c1]; rfl)
      fun k hk => row1 (by rw [c1] at hk; exact hk)

theorem uq_ok : uqTabCertificate = true := by
  unfold uqTabCertificate uqTabCheck
  rw [KernelFi22C.orbitData_eq]
  exact tab_ok

end CertificateChecks.KernelFi22Uq

end
