module

public import Certificates.Kernel.Sporadic.OddCore.SuzGlS
public import CFSG.Certificates.Kernel.Spor.BfsReplay
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzGl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.Sporadic.SuzRecog.B0Gluing CFSG.Sporadic.SuzRecog.B0GluingData
open CFSG.Sporadic.SuzRecog.C1Model CFSG.PSL3Four.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzTwCF
  CertificateChecks.KernelSpor.SuzMGF CertificateChecks.KernelSpor.SuzC1BF
  CertificateChecks.KernelSpor.SuzC1EG CertificateChecks.KernelSpor.SuzC1EF
  CertificateChecks.KernelSpor.SuzC1EV

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "pgk" => pg 11 (mask 11)
local notation "g7" => pg 7 (mask 7)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)
local notation "T" => SuzC1ET.T

theorem kMul : allN 64 (fun a => allN 64 fun b =>
    Nat.beq (fpT (pgk (T a) (pgk (T b) 0))) (g7 (SuzGlM a) b)) = true := by quickRfl

theorem kOne : Nat.beq (fpT 0) 0 = true := by quickRfl

theorem kGen : allN 4 (fun i => Nat.beq (fpT (pgk (SuzC1ET.G i) 0)) (Nat.succ i)) = true := by
  quickRfl

theorem kT1 : Nat.beq (fpT (pgk (SuzInvT1.F 0) 0)) 45 = true := by quickRfl

theorem kInv : allN 64 (fun a => Nat.beq (((List.range 64).find? fun b => mulK a b == 0).getD 0)
    (g7 (SuzGlI 0) a)) = true := by quickRfl

theorem kCm : allN 64 (fun a => allN 64 fun b =>
    Nat.beq (mulK (mulK a b) (mulK (invK a) (invK b))) (g7 (SuzGlC a) b)) = true := by quickRfl

theorem kZ1 : Nat.beq (cmK 1 4) 53 = true := by quickRfl

theorem kZ2 : Nat.beq (mulK 53 45) 57 = true := by quickRfl

theorem kChi : allN 15 chiRecK = true := by quickRfl

theorem kGam : allN 16 gamRecK = true := by quickRfl

theorem kGamI : allN 16 (fun r => allN 64 fun k =>
    Nat.beq (((List.range 64).find? fun x => gamK r x == k).getD 0) (g7 (SuzGlGI r) k)) = true := by
  quickRfl

theorem negMul : Bool.not (allN 64 fun a => allN 64 fun b =>
    Nat.beq (fpT (pgk (T a) (pgk (T b) 0)))
      (if a = 3 ∧ b = 5 then 0 else g7 (SuzGlM a) b)) = true := by quickRfl

theorem blt_t {a b : Nat} (h : a < b) : Nat.blt a b = true := Eq.mpr Nat.blt_eq h

theorem blt_f {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false :=
  Bool.eq_false_iff.2 fun e => h (Eq.mp Nat.blt_eq e)

theorem fpL_succ (F : Nat → Nat) (d y j : Nat) :
    fpL F d y (j + 1) = if F j = y then j else fpL F d y j := by
  show nIf(Nat.beq (F j) y, j, fpL F d y j) = _
  by_cases e : F j = y
  · rw [if_pos e, e, Nat.beq_refl]
  · rw [if_neg e, beq_false e]

theorem fpL_congr {F F' : Nat → Nat} {d y : Nat} :
    ∀ {k : Nat}, (∀ j < k, F j = F' j) → fpL F d y k = fpL F' d y k
  | 0, _ => rfl
  | k + 1, h => by
    rw [fpL_succ, fpL_succ, h k (by omega), fpL_congr fun j hj => h j (by omega)]

@[expose] def scatter (F : Nat → Nat) (N d n : Nat) : Array Nat :=
  Id.run (forIn (List.range' 0 n) (Array.replicate N d) (fun k (m : Array Nat) =>
    (pure (ForInStep.yield (m.set! (F k) k)) : Id (ForInStep (Array Nat)))))

theorem scatter_get (F : Nat → Nat) (N d n : Nat) :
    (scatter F N d n).size = N ∧ ∀ y < N, (scatter F N d n)[y]! = fpL F d y n := by
  have := CFSG.KS.BfsReplay.forIn_range'_yield n 0 (Array.replicate N d)
    (fun k (m : Array Nat) => (pure (ForInStep.yield (m.set! (F k) k)) : Id (ForInStep (Array Nat))))
    (fun j (m : Array Nat) => m.size = N ∧ ∀ y < N, m[y]! = fpL F d y j)
    (fun j _ m hP => ⟨_, rfl, by simp [hP.1], fun y hy => by
      rw [Nat.zero_add, Array.set!_eq_setIfInBounds, getElem!_pos _ y (by simp [hP.1]; exact hy),
        Array.getElem_setIfInBounds (by rw [hP.1]; exact hy), fpL_succ,
        ← getElem!_pos _ y (by rw [hP.1]; exact hy), hP.2 y hy]⟩)
    ⟨by simp, fun y hy => by
      rw [getElem!_pos _ y (by simp; exact hy)]
      simp [fpL]⟩
  exact this

theorem fpIndex_eq (A : Array Tab) : fpIndex A = scatter (fun k => (A[k]!)[0]!) 1782 A.size A.size := by
  unfold fpIndex scatter
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem fpIndex_get (A : Array Tab) {y : Nat} (hy : y < 1782) :
    (fpIndex A)[y]! = fpL (fun j => (A[j]!)[0]!) A.size y A.size := by
  rw [fpIndex_eq]
  exact (scatter_get _ _ _ _).2 y hy

@[expose] def treeFill (f : Nat → Nat → Nat) (par : Nat → Nat) (init : Nat) : Array Nat :=
  Id.run (forIn (List.range' 1 63) (Array.replicate 64 init) (fun k (m : Array Nat) =>
    (pure (ForInStep.yield (m.set! k (f k m[par k]!))) : Id (ForInStep (Array Nat)))))

theorem treeFill_get (f : Nat → Nat → Nat) (par : Nat → Nat) (init : Nat) (D : Nat → Nat)
    (h0 : D 0 = init) (hD : ∀ k, 0 < k → k < 64 → par k < k ∧ D k = f k (D (par k))) :
    (treeFill f par init).size = 64 ∧ ∀ k < 64, (treeFill f par init)[k]! = D k := by
  have := CFSG.KS.BfsReplay.forIn_range'_yield 63 1 (Array.replicate 64 init)
    (fun k (m : Array Nat) =>
      (pure (ForInStep.yield (m.set! k (f k m[par k]!))) : Id (ForInStep (Array Nat))))
    (fun j (m : Array Nat) => m.size = 64 ∧ ∀ y < 64, m[y]! = if y < j + 1 then D y else init)
    (fun j hj m hP => ⟨_, rfl, by simp [hP.1], fun y hy => by
      obtain ⟨hp, hk⟩ := hD (1 + j) (by omega) (by omega)
      have hm : m[par (1 + j)]! = D (par (1 + j)) := by
        rw [hP.2 _ (by omega), if_pos (by omega)]
      rw [Array.set!_eq_setIfInBounds, getElem!_pos _ y (by simp [hP.1]; exact hy),
        Array.getElem_setIfInBounds (by rw [hP.1]; exact hy)]
      by_cases e : 1 + j = y
      · rw [if_pos e, if_pos (by omega), ← e, hm, hk]
      · rw [if_neg e, ← getElem!_pos _ y (by rw [hP.1]; exact hy), hP.2 y hy]
        by_cases hy' : y < j + 1
        · rw [if_pos hy', if_pos (by omega)]
        · rw [if_neg hy', if_neg (by omega)]⟩)
    ⟨by simp, fun y hy => by
      have e : (Array.replicate 64 init)[y]! = init := by
        rw [getElem!_pos (Array.replicate 64 init) y (by simpa using hy)]
        simp
      rw [e]
      by_cases e1 : y < 0 + 1
      · rw [if_pos e1, show y = 0 by omega, h0]
      · rw [if_neg e1]⟩
  unfold treeFill
  refine ⟨this.1, fun k hk => ?_⟩
  rw [this.2 k hk, if_pos (by omega)]

theorem T_canon {k : Nat} (hk : k < 64) : cn (T k) = true :=
  penumPt_canon (ptT k (by rw [kCnt.1]; exact hk))

theorem pTT {k : Nat} (hk : k < 64) : P ttabs[k]! (T k) := ⟨t0_tabs_get hk, T_canon hk⟩

theorem ttabs_size' : ttabs.size = 64 := t0_size

theorem ttabs_get {k y : Nat} (hk : k < 64) (hy : y < 1782) : (ttabs[k]!)[y]! = pgk (T k) y := by
  rw [(pTT hk).1, unpack_getElem! hy]

theorem tFp_get {y : Nat} (hy : y < 1782) : tFp[y]! = fpT y := by
  unfold tFp
  rw [fpIndex_get _ hy, ttabs_size']
  exact fpL_congr fun j hj => ttabs_get hj (by norm_num)

theorem tPos_P {x : Tab} {X : Nat} (hx : P x X) : tPos x = fpT (pgk X 0) := by
  unfold tPos
  rw [hx.1, unpack_getElem! (by norm_num), tFp_get (pg_lt hx.2 (by norm_num))]

theorem ofFn_neg {α : Type} [Inhabited α] {n : Nat} (f : Nat → α) {i : Nat} (hi : ¬ i < n) :
    (Array.ofFn (n := n) fun i => f i.val)[i]! = default :=
  getElem!_neg _ _ (by simpa using hi)

theorem ofFn_get' {α : Type} [Inhabited α] {n : Nat} (f : Fin n → α) {i : Nat} (hi : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem ofFn_neg' {α : Type} [Inhabited α] {n : Nat} (f : Fin n → α) {i : Nat} (hi : ¬ i < n) :
    (Array.ofFn f)[i]! = default :=
  getElem!_neg _ _ (by simpa using hi)

theorem mulP_eq (a b : Nat) : mulP a b = mulK a b := by
  unfold mulP mulI mulK
  by_cases ha : a < 64
  · rw [ofFn_get' _ ha, blt_t ha]
    by_cases hb : b < 64
    · rw [ofFn_get' _ hb, blt_t hb]
      show tFp[(ttabs[a]!)[(ttabs[b]!)[0]!]!]! = g7 (SuzGlM a) b
      rw [ttabs_get hb (by norm_num), ttabs_get ha (pg_lt (T_canon hb) (by norm_num)),
        tFp_get (pg_lt (T_canon ha) (pg_lt (T_canon hb) (by norm_num)))]
      exact Nat.eq_of_beq_eq_true (allN_spec (allN_spec kMul a ha) b hb)
    · rw [ofFn_neg' _ hb, blt_f hb]
      rfl
  · rw [ofFn_neg' _ ha, blt_f ha]
    rfl

theorem oneI_eq : oneI = 0 := by
  unfold oneI
  rw [tPos_P pId']
  have h : pgk (pidn 1782 11) 0 = 0 := by
    have := unpack_getElem! (n := 1782) (w := 11) (p := pidn 1782 11) (i := 0) (by norm_num)
    rw [← pId'.1] at this
    rw [← this]
    unfold idTab
    rw [ofFn_get' _ (by norm_num)]
  rw [h]
  exact Nat.eq_of_beq_eq_true kOne

theorem invP_eq (a : Nat) : invP a = invK a := by
  unfold invP invI invK
  by_cases ha : a < 64
  · rw [ofFn_get' _ ha, blt_t ha]
    simp only [mulP_eq, oneI_eq]
    exact Nat.eq_of_beq_eq_true (allN_spec kInv a ha)
  · rw [ofFn_neg' _ ha, blt_f ha]
    rfl

theorem cmP_eq (a b : Nat) : cmP a b = cmK a b := by
  unfold cmP cmI cmK
  by_cases ha : a < 64
  · rw [ofFn_get' _ ha, blt_t ha]
    by_cases hb : b < 64
    · rw [ofFn_get' _ hb, blt_t hb]
      simp only [mulP_eq, invP_eq]
      exact Nat.eq_of_beq_eq_true (allN_spec (allN_spec kCm a ha) b hb)
    · rw [ofFn_neg' _ hb, blt_f hb]
      rfl
  · rw [ofFn_neg' _ ha, blt_f ha]
    rfl

theorem gP_eq (i : Nat) : gP i = gK i := by
  unfold gP gK
  by_cases hi : i < 4
  · rw [tPos_P (pT0 hi), blt_t hi]
    exact Nat.eq_of_beq_eq_true (allN_spec kGen i hi)
  · have e : t0Tabs[i]! = default := getElem!_neg _ _ (by simp [t0Tabs]; omega)
    rw [blt_f hi]
    unfold tPos
    rw [e, show (default : Tab)[0]! = 0 from rfl, tFp_get (by norm_num)]
    exact Nat.eq_of_beq_eq_true kOne

theorem tPos_t1 : tPos CFSG.ComponentClassification.AS81.SuzB0.tTab = 45 := by
  rw [tPos_P pt1]
  exact Nat.eq_of_beq_eq_true kT1

theorem zI_eq : zI = zIL := by
  have h1 : cmK 1 4 = 53 := Nat.eq_of_beq_eq_true kZ1
  have h2 : mulK 53 45 = 57 := Nat.eq_of_beq_eq_true kZ2
  unfold zI zIL
  rw [oneI_eq, tPos_t1, cmP_eq, gP_eq, gP_eq, mulP_eq]
  show #[0, 45, cmK 1 4, mulK (cmK 1 4) 45] = _
  rw [h1, h2]

theorem lab_eq (k : Nat) : t0Enum.lab[k]! = labT k := by
  rw [t0E.1, penumRec_eq]
  unfold labT
  by_cases hk : k < 64
  · rw [blt_t hk]
    exact ofFn_get (n := SuzC1ET.cnt) (fun i => labOf SuzC1ET.PL i) (by rw [kCnt.1]; exact hk)
  · rw [blt_f hk]
    exact ofFn_neg (n := SuzC1ET.cnt) (fun i => labOf SuzC1ET.PL i) (by rw [kCnt.1]; exact hk)

theorem par_eq (k : Nat) : t0Enum.par[k]! = parT k := by
  rw [t0E.1, penumRec_eq]
  unfold parT
  by_cases hk : k < 64
  · rw [blt_t hk]
    exact ofFn_get (n := SuzC1ET.cnt) (fun i => parOf SuzC1ET.PL i) (by rw [kCnt.1]; exact hk)
  · rw [blt_f hk]
    exact ofFn_neg (n := SuzC1ET.cnt) (fun i => parOf SuzC1ET.PL i) (by rw [kCnt.1]; exact hk)

theorem tree_rec {X : Nat → Nat} {s : Nat → Nat → Nat}
    (h : bAnd(Nat.beq (X 0) 0, allN 63 fun j => strictB (Nat.succ j) fun k =>
      bAnd(Nat.blt (parT k) k, Nat.beq (X k) (s k (X (parT k))))) = true) :
    X 0 = 0 ∧ ∀ k, 0 < k → k < 64 → parT k < k ∧ X k = s k (X (parT k)) := by
  obtain ⟨h0, h1⟩ := (bAnd_iff _ _).1 h
  refine ⟨Nat.eq_of_beq_eq_true h0, fun k hk0 hk => ?_⟩
  have := allN_spec h1 (k - 1) (by omega)
  rw [strictB_app', show Nat.succ (k - 1) = k by omega] at this
  obtain ⟨a, b⟩ := (bAnd_iff _ _).1 this
  exact ⟨Eq.mp Nat.blt_eq a, Nat.eq_of_beq_eq_true b⟩

theorem chiI_eq (v : Nat) : chiI v =
    treeFill (fun k x => (chiBit v t0Enum.lab[k]! + x) % 2) (fun k => t0Enum.par[k]!) 0 := by
  unfold chiI treeFill
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run]
  rfl

theorem chi_eq (v k : Nat) : (chiIs[v]!)[k]! = chiK v k := by
  unfold chiIs chiK
  by_cases hv : v < 15
  · obtain ⟨h0, hr⟩ := tree_rec (X := fun k => g7 (SuzGlX v) k)
      (s := fun k x => (chiBit v (labT k) + x) % 2) (allN_spec kChi v hv)
    have ht := treeFill_get (fun k x => (chiBit v t0Enum.lab[k]! + x) % 2)
      (fun k => t0Enum.par[k]!) 0 (fun k => g7 (SuzGlX v) k) h0 (fun k hk0 hk => by
        simp only [lab_eq, par_eq]
        exact hr k hk0 hk)
    rw [ofFn_get' _ hv, blt_t hv, chiI_eq]
    by_cases hk : k < 64
    · rw [blt_t hk]
      exact ht.2 k hk
    · rw [blt_f hk, getElem!_neg _ _ (by rw [ht.1]; exact hk)]
      rfl
  · rw [ofFn_neg' _ hv, blt_f hv]
    rfl

theorem gammaI_eq (r : Nat) : gammaI r =
    treeFill (fun k x => mulP (gammaGen r t0Enum.lab[k]!) x) (fun k => t0Enum.par[k]!) oneI := by
  unfold gammaI treeFill
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run]
  rfl

theorem gammaGen_eq (r i : Nat) : gammaGen r i = gammaGenK r i := by
  unfold gammaGen gammaGenK
  rw [mulP_eq, gP_eq, zI_eq]

theorem gam_eq (r k : Nat) : (gammaIs[r]!)[k]! = gamK r k := by
  unfold gammaIs gamK
  by_cases hr : r < 16
  · obtain ⟨h0, hrec⟩ := tree_rec (X := fun k => g7 (SuzGlG r) k)
      (s := fun k x => mulK (gammaGenK r (labT k)) x) (allN_spec kGam r hr)
    have ht := treeFill_get (fun k x => mulP (gammaGen r t0Enum.lab[k]!) x)
      (fun k => t0Enum.par[k]!) oneI (fun k => g7 (SuzGlG r) k) (by rw [oneI_eq]; exact h0)
      (fun k hk0 hk => by
        simp only [lab_eq, par_eq, mulP_eq, gammaGen_eq]
        exact hrec k hk0 hk)
    rw [ofFn_get' _ hr, blt_t hr, gammaI_eq]
    by_cases hk : k < 64
    · rw [blt_t hk]
      exact ht.2 k hk
    · rw [blt_f hk, getElem!_neg _ _ (by rw [ht.1]; exact hk)]
      rfl
  · rw [ofFn_neg' _ hr, blt_f hr]
    rfl

theorem gamI_eq (r k : Nat) : (gammaInvIs[r]!)[k]! = gamIK r k := by
  unfold gammaInvIs gamIK
  by_cases hr : r < 16
  · rw [map_get _ (by simp [gammaIs]; exact hr), blt_t hr]
    unfold invPerm
    by_cases hk : k < 64
    · rw [ofFn_get' _ hk, blt_t hk]
      simp only [gam_eq]
      exact Nat.eq_of_beq_eq_true (allN_spec (allN_spec kGamI r hr) k hk)
    · rw [ofFn_neg' _ hk, blt_f hk]
      rfl
  · rw [getElem!_neg (gammaIs.map invPerm) r (by simp [gammaIs]; omega), blt_f hr]
    rfl

end CertificateChecks.KernelSpor.SuzGl

end
