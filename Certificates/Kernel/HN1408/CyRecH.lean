module

public import Certificates.Kernel.HN1408.CayleyDefs
import CFSG.Certificates.Kernel.Spor.MulHSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import Certificates.Data.Kernel.Spor.HKeyU
public import Certificates.Data.Kernel.Spor.PEnumC
import CFSG.Certificates.Kernel.Spor.HKeyUSound
import CFSG.Certificates.Kernel.Spor.PEnumCSound

public section

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.PEnumC

@[expose] noncomputable def hsortPtKH (n w m cnt : Nat) (T HS HSI H : Nat → Nat) (i : Nat) :
    Bool :=
  bAnd(Nat.beq (H i) (hkeyU n w m (T i)), strictB (r32 HS i) (fun s => bAnd(Nat.blt s cnt,
    bAnd(Nat.beq (r32 HSI s) i,
      bIf(Nat.blt (Nat.succ i) cnt, Nat.blt (H s) (H (r32 HS (Nat.succ i))), true)))))

@[expose] noncomputable def cyRecH (K : Nat) (G GI GJ T PL POS SRT SRI HS HSI H CL : Nat → Nat)
    (cnt : Nat) : Bool :=
  bAnd(penumSlK 1408 11 (mask 11) (1408 * 11) true G GI K cnt T PL POS SRT SRI 0 cnt,
    bAnd(slK cnt (hsortPtKH 1408 11 (mask 11) cnt T HS HSI H) 0 cnt,
      slK (Nat.mul cnt (Nat.add K K)) (findPtK cnt T (prodQK 1408 11 (mask 11) (Nat.add K K) T
        (bothK K GI GJ)) CL) 0 (Nat.mul cnt (Nat.add K K))))

@[expose] noncomputable def cyRecC (K : Nat) (G GI GJ T PL POS SRT SRI HS HSI H CL : Nat → Nat)
    (cnt : Nat) : Bool :=
  bAnd(allN K (fun j => bAnd(Nat.beq (G j) idK, canonK 1408 11 (mask 11) (1408 * 11) (GI j))),
  bAnd(canonK 1408 11 (mask 11) (1408 * 11) (T 0),
  bAnd(penumSlC K (Nat.add K K) cnt T PL POS CL SRT SRI 0 cnt,
  bAnd(slK cnt (hsortPtKH 1408 11 (mask 11) cnt T HS HSI H) 0 cnt,
    slK (Nat.mul cnt (Nat.add K K)) (findPtK cnt T (prodQK 1408 11 (mask 11) (Nat.add K K) T
      (bothK K GI GJ)) CL) 0 (Nat.mul cnt (Nat.add K K))))))

theorem bAndH_iff {a b : Bool} : bAnd(a, b) = true ↔ a = true ∧ b = true := by
  cases a <;> simp

theorem bIfH_true {c : Bool} {t : Bool} (hc : c = true) : bIf(c, t, true) = t := by
  rw [hc]

theorem bIfH_false {c : Bool} {t : Bool} (hc : c = false) : bIf(c, t, true) = true := by
  rw [hc]

theorem hsortPtKH_spec {n w m cnt : Nat} {T HS HSI H : Nat → Nat} {i : Nat}
    (h : hsortPtKH n w m cnt T HS HSI H i = true) :
    H i = hkeyU n w m (T i) ∧ r32 HS i < cnt ∧ r32 HSI (r32 HS i) = i ∧
      (i + 1 < cnt → H (r32 HS i) < H (r32 HS (i + 1))) := by
  unfold hsortPtKH at h
  obtain ⟨h1, h⟩ := bAndH_iff.1 h
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h
  obtain ⟨h2, h⟩ := bAndH_iff.1 h
  obtain ⟨h3, h4⟩ := bAndH_iff.1 h
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.blt_eq.mp h2, Nat.eq_of_beq_eq_true h3, fun hc => ?_⟩
  rw [bIfH_true (Nat.blt_eq.mpr hc)] at h4
  exact Nat.blt_eq.mp h4

theorem hsortPtK_of_H {n w cnt : Nat} {T HS HSI H : Nat → Nat}
    (h : ∀ i < cnt, hsortPtKH n w (mask w) cnt T HS HSI H i = true) :
    ∀ i < cnt, hsortPtK n w (mask w) cnt T HS HSI i = true := by
  intro i hi
  obtain ⟨-, a1, a2, a3⟩ := hsortPtKH_spec (h i hi)
  unfold hsortPtK
  rw [CFSG.KS.Raw.Orb.strictB_eq]
  refine bAndH_iff.2 ⟨Nat.blt_eq.mpr a1, bAndH_iff.2 ⟨by rw [a2]; exact Nat.beq_refl i, ?_⟩⟩
  by_cases hc : i + 1 < cnt
  · rw [bIfH_true (Nat.blt_eq.mpr hc)]
    have e1 := (hsortPtKH_spec (h _ a1)).1
    have e2 := (hsortPtKH_spec (h _ (hsortPtKH_spec (h _ hc)).2.1)).1
    rw [hkeyU_eq] at e1 e2
    rw [← e1, ← e2]
    exact Nat.blt_eq.mpr (a3 hc)
  · have hc' : Nat.blt (Nat.succ i) cnt = false := by
      cases e : Nat.blt (Nat.succ i) cnt
      · rfl
      · exact absurd (Nat.blt_eq.mp e) hc
    rw [bIfH_false hc']

theorem slK_of_forall {cnt : Nat} {P : Nat → Bool} (h : ∀ i < cnt, P i = true) :
    slK cnt P 0 cnt = true := by
  unfold slK
  rw [CFSG.KS.Raw.Orb.allN_iff]
  intro d hd
  rw [CFSG.KS.Raw.Orb.strictB_eq]
  have e : Nat.add 0 d = d := Nat.zero_add d
  have hb : Nat.blt d cnt = true := Nat.blt_eq.mpr hd
  rw [e, hb]
  exact h d hd

theorem cyRec_of_cyRecH {K cnt : Nat} {G GI GJ T PL POS SRT SRI HS HSI H CL : Nat → Nat}
    (h : cyRecH K G GI GJ T PL POS SRT SRI HS HSI H CL cnt = true) :
    cyRec K G GI GJ T PL POS SRT SRI HS HSI CL cnt = true := by
  unfold cyRecH at h
  unfold cyRec
  obtain ⟨h1, h⟩ := bAndH_iff.1 h
  obtain ⟨h2, h3⟩ := bAndH_iff.1 h
  refine bAndH_iff.2 ⟨h1, bAndH_iff.2 ⟨slK_of_forall (hsortPtK_of_H (H := H) fun i hi => ?_), h3⟩⟩
  exact slK_spec h2 i (Nat.zero_le _) (by omega) hi

theorem penumSlK_of_forall {n w m nw k cnt : Nat} {conj : Bool} {G GI T PL POS SRT SRI : Nat → Nat}
    (h : ∀ i < cnt, penumPtK n w m nw conj G GI k cnt T PL POS SRT SRI i = true) :
    penumSlK n w m nw conj G GI k cnt T PL POS SRT SRI 0 cnt = true := by
  unfold penumSlK
  rw [CFSG.KS.Raw.Orb.allN_iff]
  intro d hd
  rw [CFSG.KS.Raw.Orb.strictB_eq]
  have e : Nat.add 0 d = d := Nat.zero_add d
  have hb : Nat.blt d cnt = true := Nat.blt_eq.mpr hd
  rw [e, hb]
  exact h d hd

theorem cyBothK_lt {K j : Nat} {GI GJ : Nat → Nat} (hj : j < K) : bothK K GI GJ j = GI j := by
  unfold bothK
  rw [Nat.blt_eq.mpr hj]

theorem cyRecH_of_cyRecC {K cnt : Nat} {G GI GJ T PL POS SRT SRI HS HSI H CL : Nat → Nat}
    (h : cyRecC K G GI GJ T PL POS SRT SRI HS HSI H CL cnt = true) :
    cyRecH K G GI GJ T PL POS SRT SRI HS HSI H CL cnt = true := by
  unfold cyRecC at h
  obtain ⟨hg, h⟩ := bAndH_iff.1 h
  obtain ⟨h0, h⟩ := bAndH_iff.1 h
  obtain ⟨hc, h⟩ := bAndH_iff.1 h
  obtain ⟨hs, hcl⟩ := bAndH_iff.1 h
  have hg' : ∀ j < K, Nat.beq (G j) idK = true ∧
      canonK 1408 11 (mask 11) (1408 * 11) (GI j) = true :=
    fun j hj => bAndH_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 hg j hj)
  have hcl' : ∀ c < cnt * (K + K), findPtK cnt T (prodQK 1408 11 (mask 11) (K + K) T
      (bothK K GI GJ)) CL c = true := fun c hc' =>
    slK_spec hcl c (Nat.zero_le _) (by change c < 0 + cnt * (K + K); omega) hc'
  have hp := CFSG.KS.PEnumC.penumPtK_of_C (n := 1408) (w := 11) (k := K) (K := K + K)
    (Nat.le_add_right K K) (fun j hj => Nat.eq_of_beq_eq_true (hg' j hj).1)
    (fun j hj => cyBothK_lt hj) (fun j hj => (hg' j hj).2) h0 hcl'
    (fun i hi => CFSG.KS.PEnumC.penumSlC_spec hc i (Nat.zero_le _) (by omega) hi)
  unfold cyRecH
  exact bAndH_iff.2 ⟨penumSlK_of_forall hp, bAndH_iff.2 ⟨hs, hcl⟩⟩

end CFSG.KD.HN1408

end
