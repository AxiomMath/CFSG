module

public import Certificates.Kernel.ThCentU.Checks
public import CFSG.Certificates.Kernel.ThCentU.Group
public import Certificates.Kernel.ThCent.Leaf3C
public import Certificates.Kernel.ThCent.Consumers
public import Certificates.Certificate17306
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CertificateChecks.KernelThCentU

open CFSG.Sporadic.Th CFSG.KC.Th CFSG.KC.ThCent CFSG.KC.ThCentU CFSG.KC.Th.Spec
  CFSG.KC.Th.Spec.FwdRel CFSG.KD CFSG.KD.ThCentU CFSG.KC.Misc.Clos
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))


@[expose] noncomputable def hU (l : ℕ) : J :=
  slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU (Nat.add 20 l)

@[expose] noncomputable def wU (i : ℕ) : List ℕ := [w0, w1, w2, w3, w4].getD i []

@[expose] noncomputable def rU (i : ℕ) : J :=
  ((wU i).map fun l => if l = 0 then hU 0 else hU 1).prod

@[expose] noncomputable def matU : J →* Matrix (Fin 248) (Fin 248) (ZMod 2) :=
  (Units.coeHom (Matrix (Fin 248) (Fin 248) (ZMod 2))).comp J.subtype

theorem matU_apply (g : J) : matU g = 𝕄 g := rfl

#kc_forall_tree allP (fun k => ch17307P k = true) 2 CertificateChecks.KernelThCentU.ch17307P
#kc_forall_tree allS (fun k => ch17307S k = true) 5 CertificateChecks.KernelThCentU.ch17307S
#kc_forall_tree allC (fun k => ch17307C k = true) 25 CertificateChecks.KernelThCentU.ch17307C
#kc_forall_tree allU (fun k => ch17307U k = true) 2 CertificateChecks.KernelThCentU.ch17307U
#kc_forall_tree allA (fun k => ch17307A k = true) 10 CertificateChecks.KernelThCentU.ch17307A
#kc_forall_tree allK (fun k => ch17307K k = true) 9 CertificateChecks.KernelThCentU.ch17307K
#kc_forall_tree allT (fun k => ch17307T k = true) 15 CertificateChecks.KernelThCentU.ch17307T

theorem wU_0 : wU 0 = w0 := rfl
theorem wU_1 : wU 1 = w1 := rfl
theorem wU_2 : wU 2 = w2 := rfl
theorem wU_3 : wU 3 = w3 := rfl
theorem wU_4 : wU 4 = w4 := rfl

theorem mat_hU {l : ℕ} (hl : l < 2) : 𝕄 (hU l) = pkMat (MT (Nat.add 10 l)) := by
  obtain ⟨hA, hB, -, hk⟩ := KernelThCent.fwd_mats
  have h := allP l hl
  rw [ch17307P.eq_1] at h
  rw [← Nat.eq_of_beq_eq_true h, pkMat_runPk hk _ (by decide +kernel) _ _
    (pkMat_initPk hk a b hA hB), hU, KernelThCent.slpJ_eq]
  rfl

theorem mat_word (w : List ℕ) :
    𝕄 ((w.map fun l => if l = 0 then hU 0 else hU 1).prod) =
      pkMat (wordH ThS.c ThS.rm ThS.ONE (MT 10) (MT 11) w) := by
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  rw [pkMat_wordH hk]
  change matU _ = _
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  simp only [Function.comp_apply, matU_apply]
  split_ifs
  · exact mat_hU (l := 0) (by norm_num)
  · exact mat_hU (l := 1) (by norm_num)

theorem mat_rU_of {i : ℕ} {w : List ℕ} (hw : wU i = w)
    (h : Nat.beq (wordH ThS.c ThS.rm ThS.ONE (MT 10) (MT 11) w) (MT i) = true) :
    𝕄 (rU i) = pkMat (MT i) := by
  rw [← Nat.eq_of_beq_eq_true h, ← mat_word, rU, hw]

theorem mat_rU {i : ℕ} (hi : i < 5) : 𝕄 (rU i) = pkMat (MT i) := by
  interval_cases i
  · exact mat_rU_of wU_0 ch17307W0
  · exact mat_rU_of wU_1 ch17307W1
  · exact mat_rU_of wU_2 ch17307W2
  · exact mat_rU_of wU_3 ch17307W3
  · exact mat_rU_of wU_4 ch17307W4

theorem mat_sq {i : ℕ} (hi : i < 5) :
    pkMat (MT (5 + i)) = pkMat (MT i) ^ 2 ∧ pkMat (MT i) * pkMat (MT (5 + i)) = 1 := by
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  have h := allS i hi
  rw [ch17307S.eq_1] at h
  obtain ⟨h1, h2⟩ := andB_eq_true h
  have e : 5 + i = Nat.add 5 i := rfl
  rw [e]
  refine ⟨?_, ?_⟩
  · rw [← Nat.eq_of_beq_eq_true h1, pkMat_mulB hk, sq]
  · rw [← pkMat_mulB hk, Nat.eq_of_beq_eq_true h2, pkMat_one hk]

theorem mat_phiG (e : ℕ → ℕ) :
    𝕄 (phiG rU e) = ((List.range 5).map fun i => pkMat (MT i) ^ e i).prod := by
  change matU (phiG rU e) = _
  rw [phiG, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun i hi => ?_)
  rw [Function.comp_apply, map_pow, matU_apply, mat_rU (List.mem_range.1 hi)]

theorem allK' : ∀ c < 27 * 9, Nat.beq (TB (Nat.add 2160 c)) (keyK ThS.rm MT c) = true :=
  forall_of_chunks 27 9 _ fun b hb => by
    have h := allK b hb
    rw [ch17307K.eq_1] at h
    exact h

theorem allT' : ∀ k < 48 * 15, node5 AG 2 TB (fun k => TB (Nat.add 720 k)) k = true :=
  forall_of_chunks 48 15 _ fun b hb => by
    have h := allT b hb
    rw [ch17307T.eq_1] at h
    exact h

theorem comm_rU {i j : ℕ} (hi : i < 5) (hj : j < 5) : rU i * rU j = rU j * rU i := by
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  have key : ∀ i j, i < j → j < 5 → rU i * rU j = rU j * rU i := by
    intro i j hij hj
    have h := allC (5 * i + j) (by change 5 * i + j < 25; omega)
    rw [ch17307C.eq_1] at h
    have e1 : Nat.div (5 * i + j) 5 = i := by
      change (5 * i + j) / 5 = i
      omega
    have e2 : Nat.mod (5 * i + j) 5 = j := by
      change (5 * i + j) % 5 = j
      omega
    rw [e1, e2] at h
    have h' := Nat.eq_of_beq_eq_true (impB_eq_true h (Nat.blt_eq.mpr hij))
    apply mat_injective
    change 𝕄 (rU i) * 𝕄 (rU j) = 𝕄 (rU j) * 𝕄 (rU i)
    rw [mat_rU (by omega), mat_rU hj, ← pkMat_mulB hk, h', pkMat_mulB hk]
  rcases Nat.lt_trichotomy i j with h | rfl | h
  · exact key i j h hj
  · rfl
  · exact (key j i h hi).symm

theorem conj_hU {l j : ℕ} (hl : l < 2) (hj : j < 5) :
    hU l * rU j = phiG rU (row5 (AG l) j) * hU l := by
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  have h := allA (5 * l + j) (by change 5 * l + j < 10; omega)
  rw [ch17307A.eq_1] at h
  have e1 : Nat.div (5 * l + j) 5 = l := by
    change (5 * l + j) / 5 = l
    omega
  have e2 : Nat.mod (5 * l + j) 5 = j := by
    change (5 * l + j) % 5 = j
    omega
  rw [e1, e2, conjK] at h
  have h' := Nat.eq_of_beq_eq_true h
  apply mat_injective
  change 𝕄 (hU l) * 𝕄 (rU j) = 𝕄 (phiG rU (row5 (AG l) j)) * 𝕄 (hU l)
  rw [mat_hU hl, mat_rU hj, mat_phiG, ← pkMat_mulB hk, h', pkMat_mulB hk,
    pkMat_phiK hk _ fun i hi => (mat_sq hi).1]
  rfl

theorem phiG_inj : ∀ x < 243, ∀ y < 243, phiG rU (dig3 x) = phiG rU (dig3 y) → x = y := by
  intro x hx y hy hxy
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  have hv : MT 12 < 2 ^ 248 := Nat.blt_eq.mp ch17307V
  have hM : ∀ i < 5, pkMat (MT (5 + i)) = pkMat (MT i) ^ 2 := fun i hi => (mat_sq hi).1
  have hkey : ∀ z, pkVec (keyK ThS.rm MT z) =
      Matrix.vecMul (pkVec (MT 12)) (𝕄 (phiG rU (dig3 z))) := by
    intro z
    rw [pkVec_keyK hk MT hM, mat_phiG]
  have e : keyK ThS.rm MT x = keyK ThS.rm MT y :=
    pkVec_inj (keyK_lt hk MT hv x) (keyK_lt hk MT hv y) (by rw [hkey, hkey, hxy])
  have ex := Nat.eq_of_beq_eq_true (allK' x hx)
  have ey := Nat.eq_of_beq_eq_true (allK' y hy)
  have hs : ∀ i < 243, sortAt 243 (fun c => TB (Nat.add 2160 c)) (fun i => TB (Nat.add 2403 i))
      i = true := fun i hi => (allR_iff _ _ _).1 ch17307Q i (Nat.zero_le _) (by omega)
  exact sort_distinct hs x hx y hy (by rw [ex, ey, e])

theorem th_centU17307 :
    Nat.card (Subgroup.centralizer
        ({slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22} : Set J)) = 174960 ∧
      Subgroup.centralizer
          ({slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22} : Set J) =
        Subgroup.closure {slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 20,
          slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 21} ∧
      ∃ R : Subgroup J, R ≤ Subgroup.centralizer
          ({slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22} : Set J) ∧
        (∀ x ∈ Subgroup.centralizer
          ({slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22} : Set J),
            ∀ r ∈ R, x * r * x⁻¹ ∈ R) ∧ Nat.card R = 3 ^ 5 ∧
        ∀ x ∈ Subgroup.centralizer
          ({slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22} : Set J),
            (∀ r ∈ R, x * r = r * x) → x ∈ R := by
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  have hfin : Finite J := inferInstance
  have hgen : {x | ∃ l < 2, hU l = x} =
      ({slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 20,
        slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 21} : Set J) := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      interval_cases l
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, rfl⟩
      · exact ⟨1, by norm_num, rfl⟩
  have hmem : ∀ l < 2, hU l ∈ Subgroup.closure {x | ∃ l < 2, hU l = x} := fun l hl =>
    Subgroup.subset_closure ⟨l, hl, rfl⟩
  have hR : ∀ i < 5, rU i ∈ Subgroup.closure {x | ∃ l < 2, hU l = x} := by
    intro i _
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    split_ifs
    · exact hmem 0 (by norm_num)
    · exact hmem 1 (by norm_num)
  have h3 : ∀ i < 5, rU i ^ 3 = 1 := by
    intro i hi
    apply mat_injective
    change 𝕄 (rU i ^ 3) = 𝕄 (1 : J)
    rw [mat_pow, mat_one, mat_rU hi]
    obtain ⟨e1, e2⟩ := mat_sq hi
    rw [e1] at e2
    exact (pow_succ' _ 2).trans e2
  have hu : ∀ l < 2, slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22 * hU l =
      hU l * slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22 := by
    intro l hl
    have h := allU l hl
    rw [ch17307U.eq_1] at h
    apply mat_injective
    change 𝕄 (slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22) * 𝕄 (hU l) =
      𝕄 (hU l) * 𝕄 (slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22)
    rw [KernelThCent.mat_u, mat_hU hl, ← pkMat_mulB hk, Nat.eq_of_beq_eq_true h,
      pkMat_mulB hk]
  have hD : ∀ k < 720, ∀ m < 720, TB k = TB m → k = m :=
    sort_distinct fun i hi => (allR_iff _ _ _).1 ch17307E i (Nat.zero_le _) (by omega)
  obtain ⟨hc, hC, hRC, hn, hRc, hcent⟩ := centU_facts
    (slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22) hU rU AG TB
    (fun k => TB (Nat.add 720 k)) hR h3 (fun i hi j hj => comm_rU hi hj)
    (fun l hl j hj => conj_hU hl hj) phiG_inj allT' hD hu Certificates.certificate17306
  rw [hgen] at hC
  exact ⟨hc, hC, subR rU, hRC, hn, hRc, hcent⟩

end CertificateChecks.KernelThCentU

end
