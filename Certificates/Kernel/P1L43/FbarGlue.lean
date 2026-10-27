module

public import Certificates.Kernel.P1L43.FbarK
public import Certificates.Kernel.HSStd.U43CaseKit
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import CFSG.Certificates.Kernel.Spor.SiftRSound
public import CFSG.Certificates.Kernel.Misc.ArrBind
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.K442264

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.U43Case
open CertificateChecks.KernelP1L43 CFSG.ComponentClassification.HarrisLit.P1.L43
open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.KC.Misc.ArrEnum
open Certificates.Asc82Fbar

theorem fb442sz : szOK 80 7 = true := by decide

theorem bA {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := (bAnd_iff a b).1 h

theorem inv2_eq (x : Nat) : fb442inv2 x =
    (Nat.beq (pp 80 7 x x) (pidn 80 7) && !Nat.beq x (pidn 80 7)) := by
  unfold fb442inv2
  cases Nat.beq (pp 80 7 x x) (pidn 80 7) <;> cases Nat.beq x (pidn 80 7) <;> rfl

theorem invS_spec {p r : Nat} (h : fb442invS p r = true) :
    Cn 80 7 p ∧ Cn 80 7 r ∧ invEqK 80 7 (mask 7) (80 * 7) p r = true := by
  unfold fb442invS fb442cn at h
  obtain ⟨h1, h2⟩ := bA h
  obtain ⟨h3, h4⟩ := bA h2
  exact ⟨h1, h3, h4⟩

theorem lt_blk {i L : Nat} (hL : 0 < L) : i < Nat.mul L (i / L) + L := by
  have e := Nat.div_add_mod i L
  have m := Nat.mod_lt i hL
  change i < L * (i / L) + L
  generalize L * (i / L) = q at e ⊢
  omega

theorem slAll {cnt L K : Nat} {P : Nat → Bool} (hL : 0 < L) (hc : cnt ≤ L * K)
    (h : ∀ k < K, slK cnt P (Nat.mul L k) L = true) : ∀ i < cnt, P i = true := by
  intro i hi
  have hk : i / L < K := Nat.div_lt_of_lt_mul (by omega)
  exact slK_spec (h _ hk) i (Nat.mul_div_le i L) (lt_blk hL) hi

theorem peAll {n w m nw k cnt L K : Nat} {conj : Bool} {G GI T PL POS SRT SRI : Nat → Nat}
    (hL : 0 < L) (hc : cnt ≤ L * K)
    (h : ∀ q < K, penumSlK n w m nw conj G GI k cnt T PL POS SRT SRI (Nat.mul L q) L = true) :
    ∀ i < cnt, penumPtK n w m nw conj G GI k cnt T PL POS SRT SRI i = true := by
  intro i hi
  have hk : i / L < K := Nat.div_lt_of_lt_mul (by omega)
  exact penumSl_spec (h _ hk) i (Nat.mul_div_le i L) (lt_blk hL) hi

theorem rec_facts {k cnt RK RC : Nat} {T PL G GI GJ : Nat → Nat}
    (h : fb442RecB k cnt RK RC T PL G GI GJ = true) :
    RK = k ∧ RC = cnt ∧ penumHdK (pidn 80 7) RC 100000 T PL = true ∧
      (∀ j < k, G j = pidn 80 7) ∧
      (∀ j < k, invEqK 80 7 (mask 7) (80 * 7) (GI j) (GJ j) = true ∧ Cn 80 7 (GJ j)) ∧
      ∀ j < k, Cn 80 7 (GI j) := by
  unfold fb442RecB at h
  obtain ⟨h1, h2⟩ := bA h
  obtain ⟨h3, h4⟩ := bA h2
  obtain ⟨h5, h6⟩ := bA h4
  have hj : ∀ j < k, G j = pidn 80 7 ∧ fb442invS (GI j) (GJ j) = true := fun j hj => by
    obtain ⟨a, b⟩ := bA (allN_spec h6 j hj)
    exact ⟨Nat.eq_of_beq_eq_true a, b⟩
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h3, h5, fun j hj' => (hj j hj').1,
    fun j hj' => ?_, fun j hj' => (invS_spec (hj j hj').2).1⟩
  obtain ⟨-, c, e⟩ := invS_spec (hj j hj').2
  exact ⟨e, c⟩

theorem tab_of {T : Table} {P : Nat} (h : arrBind (natArr T) 80 7 P = true) : T = tb 80 7 P := by
  rw [← tabT_natArr T, arrBind_sound h]
  rfl

theorem tabs2 {a b : Table} {GI : Nat → Nat} (ha : a = tb 80 7 (GI 0)) (hb : b = tb 80 7 (GI 1))
    (hc : ∀ j < 2, Cn 80 7 (GI j)) : TabsOK 80 7 2 GI [a, b].toArray := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  · exact ⟨by simp [ha, tb], hc 0 (by omega)⟩
  · exact ⟨by simp [hb, tb], hc 1 (by omega)⟩

theorem hRec_get' {cnt i : Nat} {T PL : Nat → Nat} (hi : i < (hRec 80 7 cnt T PL).1.size) :
    (hRec 80 7 cnt T PL).1[i] = tb 80 7 (T i) := by
  simp [hRec, tb]

theorem size_hRec {cnt i : Nat} {T PL : Nat → Nat} (hi : i < cnt) :
    i < (hRec 80 7 cnt T PL).1.size := by
  simpa [hRec] using hi

theorem allInvConj_of {cnt : Nat} {T PL W : Nat → Nat} {B : Nat} (hT : ∀ i < cnt, Cn 80 7 (T i))
    (hB : Cn 80 7 B) (hw : ∀ i < cnt, fb442wit cnt T W B i = true) :
    allInvConj 80 (hRec 80 7 cnt T PL).1 (tb 80 7 B) = true := by
  unfold allInvConj
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < cnt := by simpa [hRec] using hi
  rw [hRec_get' hi, involOK_tb fb442sz (hT i hi'), ← inv2_eq]
  have hw' := hw i hi'
  unfold fb442wit at hw'
  cases hv : fb442inv2 (T i)
  · rfl
  · rw [hv] at hw'
    change strictB (r32 W i) _ = true at hw'
    rw [strictB_eq''] at hw'
    obtain ⟨hj, he⟩ := bA hw'
    have hj' : r32 W i < cnt := Nat.le_of_ble_eq_true hj
    rw [Bool.not_true, Bool.false_or, Array.any_eq_true]
    refine ⟨r32 W i, size_hRec hj', ?_⟩
    rw [hRec_get' (size_hRec hj'), compT_tb (hT _ hi') (hT _ hj'), compT_tb (hT _ hj') hB,
      tblEq_tb (cn_pp (hT _ hi') (hT _ hj')) (cn_pp (hT _ hj') hB)]
    exact he

theorem memT_rec {cnt : Nat} {T PL POS Q : Nat → Nat} {j B : Nat} (hB : Cn 80 7 B) (hq : Q j = B)
    (h : findPtK cnt T Q POS j = true) : memT 80 (hRec 80 7 cnt T PL).1 (tb 80 7 B) = true := by
  obtain ⟨h1, h2⟩ := findPt_spec h
  refine memT_of h1 ?_
  rw [h2, hq]
  exact tblEq_self hB

theorem perm_tb {p r : Nat} (h : fb442invS p r = true) :
    CFSG.Sporadic.SmallOddCore.permOK 80 (tb 80 7 p) = true :=
  permOK_unpack (invS_spec h).1 (invS_spec h).2.2

theorem invol_tb {x : Nat} (hx : Cn 80 7 x) (h : fb442inv2 x = true) :
    CFSG.Sporadic.SmallOddCore.involOK 80 (tb 80 7 x) = true := by
  rw [involOK_tb fb442sz hx, ← inv2_eq]
  exact h

theorem binds22240' : Binds 80 7 CertificateChecks.KernelSchreierFam.L43.S 11 6
    CertificateChecks.KernelSchreierFam.L43.BP chainS baseArr :=
  ⟨by norm_num, by norm_num, by norm_num, by decide +kernel,
    fun j hj => arrBind_sound (CertificateChecks.KernelSchreierFam.L43.bS j hj), by decide +kernel,
    CertificateChecks.KernelSchreierFam.L43.bget⟩

theorem sift_of' (T : Table) (h : CertificateChecks.KernelSchreierFam.L43.siftL43 T = true) :
    l43Sift T = true := by
  unfold CertificateChecks.KernelSchreierFam.L43.siftL43 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact siftK_soundR binds22240' CertificateChecks.KernelSchreierFam.L43.perm
    CertificateChecks.KernelSchreierFam.L43.hl (arrBind_sound h1) (Nat.eq_of_beq_eq_true h3) h2 h4

theorem dig {a b c d : Nat} (ha : a < 3) (hb : b < 3) (hc : c < 3) (hd : d < 3) :
    (27 * a + 9 * b + 3 * c + d) / 27 % 3 = a ∧ (27 * a + 9 * b + 3 * c + d) / 9 % 3 = b ∧
      (27 * a + 9 * b + 3 * c + d) / 3 % 3 = c ∧ (27 * a + 9 * b + 3 * c + d) % 3 = d := by
  omega

theorem val3 (x : ZMod 3) : x.val < 3 := ZMod.val_lt x

theorem slCode_mul (A B : SL23) : slCode (A * B) = fb442cmul (slCode A) (slCode B) := by
  obtain ⟨a1, a2, a3, a4⟩ := dig (val3 (A.1 0 0)) (val3 (A.1 0 1)) (val3 (A.1 1 0)) (val3 (A.1 1 1))
  obtain ⟨b1, b2, b3, b4⟩ := dig (val3 (B.1 0 0)) (val3 (B.1 0 1)) (val3 (B.1 1 0)) (val3 (B.1 1 1))
  unfold slCode fb442cmul
  rw [a1, a2, a3, a4, b1, b2, b3, b4]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ZMod.val_add,
    ZMod.val_mul]

theorem eq_one_of_slCode {A : SL23} (h : slCode A = 28) : A = 1 := by
  have e := dig (val3 (A.1 0 0)) (val3 (A.1 0 1)) (val3 (A.1 1 0)) (val3 (A.1 1 1))
  unfold slCode at h
  rw [h] at e
  obtain ⟨e1, e2, e3, e4⟩ := e
  norm_num at e1 e2 e3 e4
  ext i j
  fin_cases i <;> fin_cases j <;> apply ZMod.val_injective <;>
    simp [Matrix.one_apply, ← e1, ← e2, ← e3, ← e4, ZMod.val_one]

theorem p_codes : (slList ()).map slCode = fb442cdL := by
  decide +kernel

theorem cd_of_mem {A : SL23} (hA : A ∈ slList ()) : ∃ j < 24, slCode A = fb442cd j := by
  have hm : slCode A ∈ fb442cdL := by
    rw [← p_codes]
    exact List.mem_map_of_mem hA
  obtain ⟨j, hj, e⟩ := List.getElem_of_mem hm
  refine ⟨j, hj, ?_⟩
  rw [← e]
  unfold fb442cd
  rw [List.getD_eq_getElem _ _ hj]

theorem rho_cd {j : Nat} (hj : j < 24) :
    (fbarRho ()).getD (fb442cd j) (idT 80) = tb 80 7 (FK.GI j) :=
  tab_of (allN_spec fb442rhoB j hj)

theorem rhoT_of {A : SL23} {j : Nat} (hj : j < 24) (h : slCode A = fb442cd j) :
    rhoT 80 (fbarRho ()) A = tb 80 7 (FK.GI j) := by
  unfold rhoT
  rw [h, rho_cd hj]

theorem kl_eq : (slList ()).map (rhoT 80 (fbarRho ())) =
    fb442cdL.map fun c => (fbarRho ()).getD c (idT 80) := by
  rw [← p_codes, List.map_map]
  rfl

end CertificateChecks.K442264

end
