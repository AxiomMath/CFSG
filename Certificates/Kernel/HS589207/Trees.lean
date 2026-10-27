module

public import Certificates.Kernel.HS589207.Tabs
public import CFSG.Certificates.Kernel.BfsRecKSound
public import CFSG.Certificates.Kernel.HashBfs
public import Certificates.Kernel.HS589207.Rec

set_option maxRecDepth 100000

public section

namespace CFSG.KD.HS589207.Trees

open CFSG.KC.DcHSOutK CFSG.KC.E64F CFSG.KC.Enum CFSG.Quasithin.H13.LocDbl.HSLoc
  CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.DcRank
  CFSG.KD.HS589207.Tabs CFSG.KS.KeyBfsG CFSG.KS.HashBfs CFSG.KC.BfsRecK

@[expose] def stFn (t : Nat) (s : List Nat) : List Nat :=
  (s.map (img (AB.getD t #[]))).mergeSort fun a b => decide (a ≤ b)

theorem bfsF_eq (cap : Nat) : bfsF cap = hashBfs F0 stFn 4 cap := by
  unfold bfsF hashBfs stFn
  rfl

theorem fent' : (∀ i < 3850, ∀ x ∈ setT FR.TF i, x < 100) ∧ setT FR.TF 0 = F0 := by
  have h := Rec.fent
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨fun i hi x hx => ?_, h.2⟩
  have e := CFSG.KS.allN_spec h.1 i hi
  rw [List.all_eq_true] at e
  simpa [Nat.blt_eq] using e x hx

theorem fstep : ∀ l < 4, ∀ i < 3850, ∀ j < 3850, stF A FR.TF l i j = true →
    stFn l (setT FR.TF i) = setT FR.TF j := by
  intro l hl i hi j _ h
  unfold stF at h
  rw [← of_decide_eq_true h, stFn, List.mergeSort_eq_insertionSort (fun a b : Nat => a ≤ b),
    ← CFSG.KC.E64F.insN_eq]
  congr 1
  apply List.map_congr_left
  intro x hx
  exact good_img (good_AB l hl) (fent'.1 i hi x hx)

theorem frec : GRec (Encodable.encode : List Nat → Nat) stFn 4 F0 (Encodable.encode F0) 3850
    (4 * 3850) (setT FR.TF) FP FL FPOS :=
  grec_of_recOK Encodable.encode_injective (by norm_num) (by norm_num) fent'.2 fstep
    (fun a b h => by unfold keyF; rw [h]) Rec.frec

theorem treeF_eq : treeF =
    (((List.range 3850).map FP).toArray, ((List.range 3850).map FL).toArray) := by
  unfold treeF
  rw [bfsF_eq]
  exact hashBfs_rec Encodable.encode_injective frec
    (by
      change FP 3849 < 4000
      have := (frec.tree 3849 (by norm_num) (by norm_num)).1
      omega) (Nat.le_refl _)

theorem FP_lt : ∀ k, 0 < k → k < 3850 → FP k < k := fun k h0 hk => (frec.tree k h0 hk).1

theorem FL_lt : ∀ k, 0 < k → k < 3850 → FL k < 4 := fun k h0 hk => (frec.tree k h0 hk).2.1

theorem good_treeElems : ∀ k < 3850,
    Good 100 (treeElems.getD k #[]) (ePath FP FL A 3850 k) := by
  unfold treeElems
  rw [treeF_eq]
  refine enumTabs_good good_AB (fun q _ => ePath_zero _ q) (fun k hk0 hk => ?_)
    (fun k hk q hq => ePath_lt (fun l hl q hq => A_lt hl hq) FL_lt FP_lt 3850 k hk q hq)
  rw [getD_toArray_map _ hk, getD_toArray_map _ hk]
  exact ⟨FP_lt k hk0 hk, FL_lt k hk0 hk, fun q _ => ePath_step FP_lt (by omega) hk q⟩

theorem good_g : Good 100 (treeElems.getD kU #[]) gF := by
  have h := Gen.wtab
  simp only [Bool.and_eq_true] at h
  exact good_congr (good_treeElems kU (by decide)) fun q hq => (eqF_spec h.1.1.1.1.1 q hq).symm

theorem wtab' : (∀ q < 100, wF q = uF (gF q)) ∧ (∀ q < 100, r0F q = wF (mF i0 q)) := by
  have h := Gen.wtab
  simp only [Bool.and_eq_true] at h
  exact ⟨eqF_spec h.1.1.1.1.2, eqF_spec h.1.1.1.2⟩

theorem good_wTab : Good 100 wTab wF :=
  good_congr (good_compT good_uTab good_g) fun q hq => (wtab'.1 q hq).symm

theorem good_r0Tab : Good 100 r0Tab r0F :=
  good_congr (good_compT good_wTab (good_mElems i0 (by decide))) fun q hq =>
    (wtab'.2 q hq).symm

@[expose] def stCn (l : Nat) (t : Array Nat) : Array Nat :=
  conjT (AB.getD l #[]) (AB.getD (CFSG.Quasithin.H13.LocDbl.DcNative.invL l) #[]) t

theorem bfsC_eq (cap : Nat) : bfsC cap = hashBfs r0Tab stCn 4 cap := by
  unfold bfsC hashBfs stCn
  rfl

@[expose] noncomputable def TC (i : Nat) : Array Nat := (tabC CR.TF i).toArray

theorem cent' : (∀ i < 1100, ∀ q < 100, fl (CR.TF i) q < 100) ∧
    ∀ q < 100, fl (CR.TF 0) q = r0F q := by
  have h := Rec.cent
  simp only [Bool.and_eq_true] at h
  exact ⟨fun i hi => ltF_spec (CFSG.KS.allN_spec h.1 i hi), eqF_spec h.2⟩

theorem good_TC {i : Nat} (hi : i < 1100) : Good 100 (TC i) (fl (CR.TF i)) := by
  refine ⟨by simp [TC, tabC], fun p hp => ⟨?_, cent'.1 i hi p hp⟩⟩
  simp [TC, tabC, Array.getD_eq_getD_getElem?, hp]

theorem invL_eq (l : Nat) :
    CFSG.Quasithin.H13.LocDbl.DcNative.invL l = CFSG.KC.DcHSOutK.invL l := rfl

theorem cstep : ∀ l < 4, ∀ i < 1100, ∀ j < 1100, stC A CR.TF l i j = true →
    stCn l (TC i) = TC j := by
  intro l hl i hi j hj h
  unfold stCn
  rw [invL_eq]
  refine good_ext (good_conjT (good_AB l hl) (good_AB _ (invL_lt hl)) (good_TC hi)) (good_TC hj)
    fun q hq => ?_
  exact Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h q hq)

theorem toList_inj : Function.Injective (fun a : Array Nat => (Encodable.encode a.toList : Nat)) :=
  fun a b h => Array.toList_inj.1 (Encodable.encode_injective h)

theorem croot : TC 0 = r0Tab := good_ext (good_TC (by norm_num)) good_r0Tab cent'.2

theorem crec : GRec (fun a : Array Nat => (Encodable.encode a.toList : Nat)) stCn 4 r0Tab
    (Encodable.encode r0Tab.toList) 1100 (4 * 1100) TC CP CL CPOS :=
  grec_of_recOK toList_inj (by norm_num) (by norm_num) croot cstep
    (fun a b h => by
      have e : tabC CR.TF a = tabC CR.TF b := by
        have := congrArg Array.toList h
        simpa [TC] using this
      unfold keyC
      rw [e]) Rec.crec

theorem cjTree_eq : cjTree =
    (((List.range 1100).map CP).toArray, ((List.range 1100).map CL).toArray) := by
  unfold cjTree
  rw [bfsC_eq]
  exact hashBfs_rec toList_inj crec
    (by
      change CP 1099 < 1200
      have := (crec.tree 1099 (by norm_num) (by norm_num)).1
      omega) (Nat.le_refl _)

theorem CP_lt : ∀ k, 0 < k → k < 1100 → CP k < k := fun k h0 hk => (crec.tree k h0 hk).1

theorem CL_lt : ∀ k, 0 < k → k < 1100 → CL k < 4 := fun k h0 hk => (crec.tree k h0 hk).2.1

theorem TC_step {k : Nat} (h0 : 0 < k) (hk : k < 1100) : TC k = stCn (CL k) (TC (CP k)) :=
  (crec.tree k h0 hk).2.2

theorem TC_inj {a b : Nat} (ha : a < 1100) (hb : b < 1100) (h : TC a = TC b) : a = b :=
  crec.inj a ha b hb (by rw [h])

end CFSG.KD.HS589207.Trees

end
