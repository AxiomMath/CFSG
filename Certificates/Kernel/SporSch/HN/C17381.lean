
module

public import Certificates.Kernel.SporSch.HN.C17381K
public import Certificates.Kernel.SporSch.HN.C13609
public import Certificates.Kernel.SporSch.HN.Pt2109
public import CFSG.Certificates.Kernel.HNLocalSound
public import CFSG.Certificates.Kernel.HNLocal.AddSound
public import CFSG.Certificates.Kernel.SporSch.HNXCnt.Seed
public import CFSG.Certificates.Kernel.SporSch.HNXCnt.Asm
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNFiveCertBase

public section

namespace CertificateChecks.KernelSporSch.HN17381

open CFSG.KC.ConjKey CFSG.KS.Ord CFSG.KS.SporSch CFSG.Sporadic.HNSchreier
open CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.He.Native CFSG.HardMathSupport.Dickson.I271.HNFive
open CFSG.HardMathSupport.Dickson.I271.HNFive.Native CertificateChecks.KernelSporSch Matrix

local notation "OM" => ordMat 5 133 13 1729
local notation "mm" => CFSG.KC.LL.HN.mm
local notation "ONE" => CFSG.KD.OrdHN.ONE
local notation "M133" => Matrix (Fin 133) (Fin 133) (ZMod 5)

def CanonA (d : ℕ) (X : Array (Array ℕ)) : Prop :=
  X.size = d ∧ ∀ i < d, (X[i]!).size = d ∧ ∀ j < d, (X[i]!)[j]! < 5

theorem canonA_ofFn {d : ℕ} (f : Fin d → Fin d → ℕ) (hf : ∀ i j, f i j < 5) :
    CanonA d (Array.ofFn fun i => Array.ofFn fun j => f i j) := by
  refine ⟨by simp, fun i hi => ?_⟩
  rw [getElem!_ofFn _ hi]
  refine ⟨by simp, fun j hj => ?_⟩
  rw [getElem!_ofFn _ hj]
  exact hf _ _

theorem canonA_mulM (d : ℕ) (X Y : Array (Array ℕ)) : CanonA d (mulM 5 d X Y) := by
  unfold mulM
  exact canonA_ofFn _ fun _ _ => Nat.mod_lt _ (by norm_num)

theorem canonA_idM (d : ℕ) : CanonA d (idM d) := by
  unfold idM
  exact canonA_ofFn _ fun _ _ => by split <;> norm_num

theorem canonA_powM (d : ℕ) (X : Array (Array ℕ)) (e : ℕ) : CanonA d (powM 5 d X e) := by
  cases e with
  | zero => exact canonA_idM d
  | succ e => exact canonA_mulM d _ _

theorem canonA_addM (d : ℕ) (X Y : Array (Array ℕ)) : CanonA d (addM 5 d X Y) := by
  unfold addM
  exact canonA_ofFn _ fun _ _ => Nat.mod_lt _ (by norm_num)

theorem canonA_zeroM (d : ℕ) : CanonA d (zeroM d) := by
  unfold zeroM
  refine ⟨by simp, fun i hi => ?_⟩
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_replicate]
  refine ⟨by simp, fun j hj => ?_⟩
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_replicate]
  norm_num

theorem nat_eq_of_cast5 {a b : ℕ} (ha : a < 5) (hb : b < 5) (h : (a : ZMod 5) = b) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h

theorem eq_of_toMat {d : ℕ} {X Y : Array (Array ℕ)} (hX : CanonA d X) (hY : CanonA d Y)
    (h : toMat 5 d X = toMat 5 d Y) : X = Y := by
  have hrow : ∀ i < d, X[i]! = Y[i]! := by
    intro i hi
    obtain ⟨hx1, hx2⟩ := hX.2 i hi
    obtain ⟨hy1, hy2⟩ := hY.2 i hi
    refine Array.ext (hx1.trans hy1.symm) fun j hj1 hj2 => ?_
    have hj : j < d := hx1 ▸ hj1
    have e := congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩
    rw [toMat_apply, toMat_apply] at e
    rw [← getElem!_pos X[i]! j hj1, ← getElem!_pos Y[i]! j hj2]
    exact nat_eq_of_cast5 (hx2 j hj) (hy2 j hj) e
  refine Array.ext (hX.1.trans hY.1.symm) fun i hi1 hi2 => ?_
  have hi : i < d := hX.1 ▸ hi1
  rw [← getElem!_pos X i hi1, ← getElem!_pos Y i hi2]
  exact hrow i hi

theorem beq_of {X Y : Array (Array ℕ)} (hX : CanonA 133 X) (hY : CanonA 133 Y)
    (h : toMat 5 133 X = toMat 5 133 Y) : (X == Y) = true := by
  rw [eq_of_toMat hX hY h]
  exact beq_self_eq_true _

theorem neAt_of {X Y : Array (Array ℕ)} (i j : Fin 133) (h : toMat 5 133 X i j ≠ toMat 5 133 Y i j) :
    neAt 5 X Y i.val j.val = true := by
  unfold neAt
  rw [bne_iff_ne]
  intro e
  apply h
  rw [toMat_apply, toMat_apply]
  exact (ZMod.natCast_eq_natCast_iff' _ _ 5).2 e

def Hn5Full (Mg Mc MA ML MR MW MF : M133) : Prop :=
  Mg ^ 30 = 1 ∧ (Mg ^ 6 : M133) 0 1 ≠ 0 ∧ (Mg ^ 10 : M133) 0 0 ≠ 1 ∧
    (Mg ^ 29 * Mc * Mg * Mc * Mg ^ 29) * Mg ^ 6 = Mg ^ 6 * (Mg ^ 29 * Mc * Mg * Mc * Mg ^ 29) ∧
    (Mg ^ 10 * (Mg ^ 29 * Mc * Mg * Mc * Mg ^ 29) : M133) 0 0 ≠
      ((Mg ^ 29 * Mc * Mg * Mc * Mg ^ 29) * Mg ^ 10 : M133) 0 0 ∧
    (Mg ^ 6 - 1) * MA = 0 ∧ MA * ML + MR * (Mg ^ 6 - 1) = 1 ∧
    (Mg ^ 29 * Mc * Mg * Mc * Mg ^ 29 - 1) * MA = (Mg ^ 6 - 1) * (Mg ^ 6 - 1) * MW ∧
    MF * ((Mg ^ 6 - 1) * (Mg ^ 6 - 1)) = 0 ∧ (MF * (Mg ^ 10 - 1) * MA : M133) 0 1 ≠ 0

theorem hn5Core_of {Ng Nc : Array (Array ℕ)}
    (h : Hn5Full (toMat 5 133 Ng) (toMat 5 133 Nc) (toMat 5 133 (rowsOf 5 133 dataA))
      (toMat 5 133 (rowsOf 5 133 dataLam)) (toMat 5 133 (rowsOf 5 133 dataR))
      (toMat 5 133 (rowsOf 5 133 dataW)) (toMat 5 133 (rowsOf 5 133 dataPhi))) :
    hn5Core Ng Nc = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  unfold hn5Core
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact beq_of (canonA_powM _ _ _) (canonA_idM _) (by rw [toMat_powM, toMat_idM]; exact h1)
  · refine neAt_of (X := powM 5 133 Ng 6) (Y := idM 133) 0 1 ?_
    rw [toMat_powM, toMat_idM, Matrix.one_apply_ne (by decide)]
    exact h2
  · refine neAt_of (X := powM 5 133 Ng 10) (Y := idM 133) 0 0 ?_
    rw [toMat_powM, toMat_idM, Matrix.one_apply_eq]
    exact h3
  · exact beq_of (canonA_mulM _ _ _) (canonA_mulM _ _ _) (by
      simp only [toMat_mulM, toMat_powM]
      exact h4)
  · refine neAt_of 0 0 ?_
    simp only [toMat_mulM, toMat_powM]
    exact h5
  · exact beq_of (canonA_mulM _ _ _) (canonA_zeroM _) (by
      simp only [toMat_mulM, toMat_subIdM, toMat_powM, toMat_zeroM]
      exact h6)
  · exact beq_of (canonA_addM _ _ _) (canonA_idM _) (by
      simp only [toMat_mulM, toMat_addM, toMat_subIdM, toMat_powM, toMat_idM]
      exact h7)
  · exact beq_of (canonA_mulM _ _ _) (canonA_mulM _ _ _) (by
      simp only [toMat_mulM, toMat_subIdM, toMat_powM]
      exact h8)
  · exact beq_of (canonA_mulM _ _ _) (canonA_zeroM _) (by
      simp only [toMat_mulM, toMat_subIdM, toMat_powM, toMat_zeroM]
      exact h9)
  · refine neAt_of 0 1 ?_
    simp only [toMat_mulM, toMat_subIdM, toMat_powM, toMat_zeroM, Matrix.zero_apply]
    exact h10

abbrev Rep (W : ℕ) (M : M133) : Prop := Canon 5 133 13 W ∧ OM W = M

theorem rep_mul {A B : ℕ} {M N : M133} (hA : Rep A M) (hB : Rep B N) : Rep (mm A B) (M * N) := by
  obtain ⟨h1, h2⟩ := HNXP.mm_sound hA.1 hB.1
  exact ⟨h1, by rw [h2, hA.2, hB.2]⟩

theorem rep_congr {A B : ℕ} {M N : M133} (e : A = B) (h : Rep A M) (hM : M = N) : Rep B N := by
  subst e hM
  exact h

theorem eqK_eq {a b : ℕ} (h : eqK a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem subI_eq (X : ℕ) : CFSG.KC.LL.HN.subI X =
    CFSG.KC.Ord.redP 13 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H 5 9 (X + 4 * ONE) := by
  unfold CFSG.KC.LL.HN.subI
  congr 1

theorem rep_sub {X : ℕ} {M : M133} (h : Rep X M) : Rep (CFSG.KC.LL.HN.subI X) (M - 1) := by
  rw [subI_eq]
  obtain ⟨h1, h2⟩ := CFSG.KS.HNLocal.subOne_sound CFSG.KD.OrdHN.consts h.1
  refine ⟨h1, ?_⟩
  rw [← h.2]
  exact h2

theorem rep_add {X Y : ℕ} {M N : M133} (hX : Rep X M) (hY : Rep Y N) : Rep (addL X Y) (M + N) := by
  have e : addL X Y = CFSG.KC.Ord.redP 13 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H 5 9 (X + Y) := rfl
  rw [e]
  obtain ⟨h1, h2⟩ := CFSG.KS.HNLocal.MatPf.addL_sound CFSG.KD.OrdHN.consts hX.1 hY.1
  refine ⟨h1, ?_⟩
  rw [← hX.2, ← hY.2]
  exact h2

theorem om_zero : OM 0 = 0 := by
  funext i j
  rw [CFSG.KS.SporSch.LyM.ordMat_apply, Nat.zero_div, Nat.zero_mod, Nat.cast_zero]
  rfl

theorem rep_zero {X : ℕ} {M : M133} (h : Rep X M) (e : eqK X 0 = true) : M = 0 := by
  rw [← h.2, eqK_eq e, om_zero]

theorem rep_one {X : ℕ} {M : M133} (h : Rep X M) (e : eqK X ONE = true) : M = 1 := by
  rw [← h.2, eqK_eq e, HNXP.one_ord]

theorem ent_lt {X : ℕ} (hX : Canon 5 133 13 X) {j : ℕ} (hj : j < 133) : e0 X j < 5 := by
  have h := hX.2 j (by omega)
  unfold e0
  rw [HNXP.fldW_eq]
  exact h

theorem om_e0 (X : ℕ) {j : ℕ} (hj : j < 133) : OM X 0 ⟨j, hj⟩ = ((e0 X j : ℕ) : ZMod 5) := by
  rw [CFSG.KS.SporSch.LyM.ordMat_apply]
  unfold e0
  rw [HNXP.fldW_eq]
  simp

theorem om_ne {X c j : ℕ} {M : M133} (hX : Rep X M) (hj : j < 133) (hc : c < 5)
    (h : Bool.not (Nat.beq (e0 X j) c) = true) : M 0 ⟨j, hj⟩ ≠ (c : ZMod 5) := by
  rw [← hX.2, om_e0 X hj]
  intro e
  have := nat_eq_of_cast5 (ent_lt hX.1 hj) hc e
  rw [this, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem om_ne2 {X Y j : ℕ} {M N : M133} (hX : Rep X M) (hY : Rep Y N) (hj : j < 133)
    (h : Bool.not (Nat.beq (e0 X j) (e0 Y j)) = true) : M 0 ⟨j, hj⟩ ≠ N 0 ⟨j, hj⟩ := by
  rw [← hX.2, ← hY.2, om_e0 X hj, om_e0 Y hj]
  intro e
  have := nat_eq_of_cast5 (ent_lt hX.1 hj) (ent_lt hY.1 hj) e
  rw [this, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem rep_pay {W : ℕ} {s : String} {cs : List Char} (hs : s = String.ofList cs)
    (h : seedRK W cs = true) (hv : validHN W = true) : Rep W (toMat 5 133 (rowsOf 5 133 s)) := by
  subst hs
  exact ⟨HNXP.canon_of_validHN hv, (HNXP.toMat_rows (HNXP.seedRK_rows h)).symm⟩

theorem pow6 (M : M133) : M * M * M * M * M * M = M ^ 6 := by
  simp only [pow_succ, pow_zero, one_mul]

theorem full_of {G GI Y S C Q A L R W F : ℕ} {Mg Mc MA ML MR MW MF : M133}
    (hG : Rep G Mg) (hC : Rep C Mc) (hA : Rep A MA) (hL : Rep L ML) (hR : Rep R MR)
    (hW : Rep W MW) (hF : Rep F MF)
    (c1 : eqK (mm (mm (mm (mm (mm G G) G) G) G) G) Y = true)
    (c2 : eqK (mm (mm (mm (mm Y G) G) G) G) S = true) (c3 : eqK (mm (mm S S) S) ONE = true)
    (c4 : eqK (mm G GI) ONE = true) (c5 : validHN GI = true)
    (cq : eqK (mm (mm (mm (mm GI C) G) C) GI) Q = true)
    (e1 : Bool.not (Nat.beq (e0 Y 1) 0) = true) (e2 : Bool.not (Nat.beq (e0 S 0) 1) = true)
    (e3 : Bool.not (Nat.beq (e0 (mm S Q) 0) (e0 (mm Q S) 0)) = true)
    (cqy : eqK (mm Q Y) (mm Y Q) = true)
    (k1 : eqK (mm (CFSG.KC.LL.HN.subI Y) A) 0 = true)
    (k2 : eqK (addL (mm A L) (mm R (CFSG.KC.LL.HN.subI Y))) ONE = true)
    (k3 : eqK (mm (CFSG.KC.LL.HN.subI Q) A)
      (mm (mm (CFSG.KC.LL.HN.subI Y) (CFSG.KC.LL.HN.subI Y)) W) = true)
    (k4 : eqK (mm F (mm (CFSG.KC.LL.HN.subI Y) (CFSG.KC.LL.HN.subI Y))) 0 = true)
    (k5 : Bool.not (Nat.beq (e0 (mm (mm F (CFSG.KC.LL.HN.subI S)) A) 1) 0) = true) :
    Hn5Full Mg Mc MA ML MR MW MF := by
  have rY : Rep Y (Mg ^ 6) := rep_congr (eqK_eq c1)
    (rep_mul (rep_mul (rep_mul (rep_mul (rep_mul hG hG) hG) hG) hG) hG) (pow6 Mg)
  have rS : Rep S (Mg ^ 10) := rep_congr (eqK_eq c2)
    (rep_mul (rep_mul (rep_mul (rep_mul rY hG) hG) hG) hG) (by
      simp only [pow_succ, pow_zero, one_mul])
  have h30 : Mg ^ 30 = 1 :=
    calc Mg ^ 30 = Mg ^ 10 * Mg ^ 10 * Mg ^ 10 := by rw [← pow_add, ← pow_add]
      _ = 1 := rep_one (rep_mul (rep_mul rS rS) rS) c3
  have hGI : Rep GI (OM GI) := ⟨HNXP.canon_of_validHN c5, rfl⟩
  have hgi : Mg * OM GI = 1 := rep_one (rep_mul hG hGI) c4
  have e29 : OM GI = Mg ^ 29 := by
    calc OM GI = Mg ^ 30 * OM GI := by rw [h30, one_mul]
      _ = Mg ^ 29 * (Mg * OM GI) := by rw [← mul_assoc, ← pow_succ]
      _ = Mg ^ 29 := by rw [hgi, mul_one]
  have rGI : Rep GI (Mg ^ 29) := ⟨hGI.1, e29⟩
  have rQ : Rep Q (Mg ^ 29 * Mc * Mg * Mc * Mg ^ 29) :=
    rep_congr (eqK_eq cq) (rep_mul (rep_mul (rep_mul (rep_mul rGI hC) hG) hC) rGI) rfl
  have rT := rep_sub rY
  have rT2 := rep_mul rT rT
  refine ⟨h30, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := om_ne (c := 0) rY (j := 1) (by norm_num) (by norm_num) e1
    rw [Nat.cast_zero] at this
    exact this
  · have := om_ne (c := 1) rS (j := 0) (by norm_num) (by norm_num) e2
    rw [Nat.cast_one] at this
    exact this
  · have := congrArg OM (eqK_eq cqy)
    rwa [(rep_mul rQ rY).2, (rep_mul rY rQ).2] at this
  · exact om_ne2 (rep_mul rS rQ) (rep_mul rQ rS) (j := 0) (by norm_num) e3
  · exact rep_zero (rep_mul rT hA) k1
  · exact rep_one (rep_add (rep_mul hA hL) (rep_mul hR rT)) k2
  · have := congrArg OM (eqK_eq k3)
    rwa [(rep_mul (rep_sub rQ) hA).2, (rep_mul rT2 hW).2] at this
  · exact rep_zero (rep_mul hF rT2) k4
  · have := om_ne (c := 0) (rep_mul (rep_mul hF (rep_sub rS)) hA) (j := 1) (by norm_num)
      (by norm_num) k5
    rw [Nat.cast_zero] at this
    exact this

section Concrete

theorem rep_G : Rep CFSG.KD.HNPt2109.C3_6 (matJ g3J) := by
  have h := HNPt2109.C3_mat (j := 6) (by norm_num)
  rw [HN13609.c3J_eq (by norm_num)] at h
  have e : c3J 6 = g3J := by
    unfold c3J
    rw [if_neg (by norm_num)]
  have e2 : HNPt2109.C3W 6 = CFSG.KD.HNPt2109.C3_6 := rfl
  rw [e, e2] at h
  exact h

theorem rep_C : Rep CFSG.KD.HN17381.C (matJ (seedWordJ cWord)) := by
  have hcs : ∀ c ∈ cWord.map (33 + ·), c < 36 := by
    intro c hc
    rw [List.mem_map] at hc
    obtain ⟨l, hl, rfl⟩ := hc
    rcases cWord_letters l hl with rfl | rfl <;> norm_num
  obtain ⟨h1, h2⟩ := HNPt2103.mat_word hcs
  refine rep_congr (eqK_eq ch17381_c) ⟨h1, h2⟩ ?_
  rw [HNPt2103.prod_seed cWord cWord_letters, HNPt2085.seedWordJ_eq]

theorem full17381 : Hn5Full (matJ g3J) (matJ (seedWordJ cWord)) (toMat 5 133 (rowsOf 5 133 dataA))
    (toMat 5 133 (rowsOf 5 133 dataLam)) (toMat 5 133 (rowsOf 5 133 dataR))
    (toMat 5 133 (rowsOf 5 133 dataW)) (toMat 5 133 (rowsOf 5 133 dataPhi)) := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := ch17381_pow
  obtain ⟨e1, e2, e3⟩ := ch17381_ent
  obtain ⟨k1, k2, k3, k4, k5⟩ := ch17381_ker
  obtain ⟨pa, pl, pr, pw, pf, va, vl, vr, vw, vf⟩ := ch17381_pay
  exact full_of rep_G rep_C (rep_pay CFSG.KD.HN17381.pA.eq pa va)
    (rep_pay CFSG.KD.HN17381.pL.eq pl vl) (rep_pay CFSG.KD.HN17381.pR.eq pr vr)
    (rep_pay CFSG.KD.HN17381.pW.eq pw vw) (rep_pay CFSG.KD.HN17381.pF.eq pf vf)
    c1 c2 c3 c4 c5 ch17381_q e1 e2 e3 ch17381_qy k1 k2 k3 k4 k5

theorem check17381 :
    hn5CheckO (hnsData.orbit ()) = true := by
  unfold hn5CheckO
  dsimp only
  rw [← hRegs_eq, ← hStrongArr_eq, ← g3Arr_eq]
  refine hn5Core_of ?_
  rw [toMat_tabMat g3J_rep, toMat_tabMat (prep_seedWordArr cWord cWord_letters)]
  exact full17381

end Concrete

end CertificateChecks.KernelSporSch.HN17381

end
