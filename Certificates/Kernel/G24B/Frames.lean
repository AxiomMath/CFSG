module

public import Certificates.Kernel.G24B.Normal
public import Certificates.Kernel.G24B.Checks733009
public import CFSG.Quasithin.Recognition.St84.G24ModelFrameFacts

public section

noncomputable section

set_option maxRecDepth 100000

namespace CFSG.KD.G24B

open CFSG.Fischer CFSG.Quasithin.F112R.St84.G24M CFSG.KC.Misc.Spec CFSG.KC.F2BfsRec
open CFSG.KC.Misc.G24 (mulF2 oneF2 nthV)
open CFSG.Quasithin.KGC31 (eElt)
open CFSG.Quasithin.St84.G24MF (matV1 matZ1 matV2 matZ2)


theorem anyN_iff' {n : ℕ} {f : ℕ → Bool} :
    CFSG.KLie.CT.anyN n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun h => (Bool.false_ne_true h).elim, fun ⟨_, hi, _⟩ => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    change CFSG.KLie.CT.orB (f n) (CFSG.KLie.CT.anyN n f) = true ↔ _
    cases hf : f n
    · change CFSG.KLie.CT.anyN n f = true ↔ _
      rw [ih]
      constructor
      · rintro ⟨i, hi, h⟩
        exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
      · rintro ⟨i, hi, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ⟨i, hi, h⟩
        · rw [hf] at h
          exact absurd h (by decide)
    · exact ⟨fun _ => ⟨n, Nat.lt_succ_self n, hf⟩, fun _ => rfl⟩

theorem zmod2_val_cases (a : ZMod 2) : (a.val = 0 ∧ a = 0) ∨ (a.val = 1 ∧ a = 1) := by
  fin_cases a
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

theorem psi_eElt {G b : ℕ → ℕ} :
    ∀ (n : ℕ) (v : Fin n → Y) (c : Fin n → ZMod 2), (∀ i : Fin n, psi (v i) = pkMat 28 (G i.val)) →
      (∀ i : Fin n, b i.val = (c i).val) → psi (eElt v c) = pkMat 28 (bitProdK G b n)
  | 0, v, c, _, _ => by
    change psi (List.prod []) = pkMat 28 (oneF2 28)
    rw [pkMat_oneF2, List.prod_nil, map_one]
  | n + 1, v, c, hv, hb => by
    have ih := psi_eElt n (fun i => v i.castSucc) (fun i => c i.castSucc)
      (fun i => hv i.castSucc) (fun i => hb i.castSucc)
    have hsplit : eElt v c = eElt (fun i => v i.castSucc) (fun i => c i.castSucc) *
        v (Fin.last n) ^ (c (Fin.last n)).val := by
      simp only [eElt, List.ofFn_succ', List.prod_concat]
    have hbn : b n = (c (Fin.last n)).val := hb (Fin.last n)
    change psi (eElt v c) = pkMat 28 (Bool.rec (motive := fun _ => ℕ) (bitProdK G b n)
      (mulF2 28 (bitProdK G b n) (G n)) (Nat.beq (b n) 1))
    rw [hsplit, map_mul, ih, hbn]
    rcases zmod2_val_cases (c (Fin.last n)) with ⟨h0, -⟩ | ⟨h1, -⟩
    · rw [h0, pow_zero, map_one, mul_one]
      rfl
    · rw [h1, pow_one, hv (Fin.last n)]
      change _ = pkMat 28 (mulF2 28 (bitProdK G b n) (G n))
      rw [pkMat_mulF2]
      rfl

theorem conjK_spec (hC : ChevFacts) {g X P E : ℕ} {x f e : Y} (hx : psi x = pkMat 28 X)
    (hf : psi f = pkMat 28 P) (he : psi e = pkMat 28 E)
    (h : conjK g X P E = true) :
    (g = 0 → x * f * x⁻¹ = e) ∧ (g ≠ 0 → x⁻¹ * f * x = e) := by
  unfold conjK at h
  cases hg : Nat.beq g 0
  · rw [hg] at h
    have hm : f * x = x * e := psi_injective hC (by
      rw [map_mul, map_mul, hx, hf, he, ← pkMat_mulF2, ← pkMat_mulF2, beq_iff'.mp h])
    refine ⟨fun h0 => absurd (beq_iff'.mpr h0) (by rw [hg]; decide), fun _ => ?_⟩
    rw [mul_assoc, hm, ← mul_assoc, inv_mul_cancel, one_mul]
  · rw [hg] at h
    have hm : x * f = e * x := psi_injective hC (by
      rw [map_mul, map_mul, hx, hf, he, ← pkMat_mulF2, ← pkMat_mulF2, beq_iff'.mp h])
    refine ⟨fun _ => ?_, fun h0 => absurd (beq_iff'.mp hg) h0⟩
    rw [hm, mul_inv_cancel_right]

theorem vAt_eq {k : ℕ} (M : Fin 3 → Matrix (Fin k) (Fin k) (ZMod 2)) (g : Fin 3) (i j : Fin k) :
    vAt M g.val i.val j.val = (M g i j).val := by
  simp [vAt, g.2, i.2, j.2]

@[expose] def cBits {nz : ℕ} (c : ℕ) (t : Fin nz) : ZMod 2 := if c.testBit t.val then 1 else 0

theorem bitN_eq {nz : ℕ} (c : ℕ) (t : Fin nz) : bitN c t.val = (cBits c t).val := by
  unfold bitN cBits
  rw [CFSG.KC.F2Mat.bit_eq_testBit]
  cases c.testBit t.val <;> rfl

theorem img_eq {S img : Fin 3 → Y} (h : img = ![S 0, (S 1)⁻¹, (S 2)⁻¹]) (g : Fin 3) :
    (g.val = 0 → img g = S g) ∧ (g.val ≠ 0 → img g = (S g)⁻¹) := by
  subst h
  fin_cases g
  · exact ⟨fun _ => rfl, fun h => absurd rfl h⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => rfl⟩

theorem conj_img (hC : ChevFacts) {S img : Fin 3 → Y} (h : img = ![S 0, (S 1)⁻¹, (S 2)⁻¹])
    (g : Fin 3) {X P E : ℕ} {f e : Y} (hx : psi (S g) = pkMat 28 X) (hf : psi f = pkMat 28 P)
    (he : psi e = pkMat 28 E) (hk : conjK g.val X P E = true) : img g * f * (img g)⁻¹ = e := by
  obtain ⟨h0, h1⟩ := conjK_spec hC hx hf he hk
  obtain ⟨i0, i1⟩ := img_eq h g
  by_cases hg : g.val = 0
  · rw [i0 hg]
    exact h0 hg
  · rw [i1 hg, inv_inv]
    exact h1 hg

theorem psi_A1gen (hC : ChevFacts) (g : Fin 3) : psi (A1gen g) = pkMat 28 (nthV GA1 g.val) := by
  rw [nthV_eq, GA1, getD_map_lt (by rw [show wA1.length = 3 from rfl]; exact g.2) 0 [],
    show A1gen g = agY (wA1.getD g.val []) by fin_cases g <;> rfl, psi_agY hC]

theorem psi_A2gen (hC : ChevFacts) (g : Fin 3) : psi (A2gen g) = pkMat 28 (nthV GA2 g.val) := by
  rw [nthV_eq, GA2, getD_map_lt (by rw [show wA2.length = 3 from rfl]; exact g.2) 0 [],
    show A2gen g = agY (wA2.getD g.val []) by fin_cases g <;> rfl, psi_agY hC]

theorem frameFacts (hC : ChevFacts) : FrameFacts := by
  have hf1 := allN_iff'.mp ch733009_frames1
  have hz1 := allN_iff'.mp ch733009_centre1
  have hf2 := allN_iff'.mp ch733009_frames2
  have hz2 := allN_iff'.mp ch733009_centre2
  refine ⟨fun g j => ?_, fun g t => ?_, fun g j => ?_, fun g t => ?_⟩
  · obtain ⟨c, -, hc⟩ := anyN_iff'.mp (allN_iff'.mp (hf1 g.val g.2) j.val (by omega))
    refine ⟨cBits c, conj_img hC rfl g (psi_A1gen hC g) (psi_pc1 hC (Fin.castAdd 2 j)) ?_ hc⟩
    rw [map_mul, pkMat_mulF2]
    congr 1
    · exact psi_eElt (G := nthV GQ1) (b := fun i => vAt matV1 g.val i j.val) 8 _ _
        (fun i => psi_pc1 hC (Fin.castAdd 2 i)) (fun i => vAt_eq matV1 g i j)
    · exact psi_eElt (G := fun s => nthV GQ1 (Nat.add 8 s)) (b := bitN c) 2 _ _
        (fun t => psi_pc1 hC (Fin.natAdd 8 t)) (fun t => bitN_eq c t)
  · refine conj_img hC rfl g (psi_A1gen hC g) (psi_pc1 hC (Fin.natAdd 8 t)) ?_
      (allN_iff'.mp (hz1 g.val g.2) t.val t.2)
    exact psi_eElt (G := fun s => nthV GQ1 (Nat.add 8 s)) (b := fun s => vAt matZ1 g.val s t.val)
      2 _ _ (fun s => psi_pc1 hC (Fin.natAdd 8 s)) (fun s => vAt_eq matZ1 g s t)
  · obtain ⟨c, -, hc⟩ := anyN_iff'.mp (allN_iff'.mp (hf2 g.val g.2) j.val (by omega))
    refine ⟨cBits c, conj_img hC rfl g (psi_A2gen hC g) (psi_pc2 hC (Fin.castAdd 4 j)) ?_ hc⟩
    rw [map_mul, pkMat_mulF2]
    congr 1
    · exact psi_eElt (G := nthV GQ2) (b := fun i => vAt matV2 g.val i j.val) 6 _ _
        (fun i => psi_pc2 hC (Fin.castAdd 4 i)) (fun i => vAt_eq matV2 g i j)
    · exact psi_eElt (G := fun s => nthV GQ2 (Nat.add 6 s)) (b := bitN c) 4 _ _
        (fun t => psi_pc2 hC (Fin.natAdd 6 t)) (fun t => bitN_eq c t)
  · refine conj_img hC rfl g (psi_A2gen hC g) (psi_pc2 hC (Fin.natAdd 6 t)) ?_
      (allN_iff'.mp (hz2 g.val g.2) t.val t.2)
    exact psi_eElt (G := fun s => nthV GQ2 (Nat.add 6 s)) (b := fun s => vAt matZ2 g.val s t.val)
      4 _ _ (fun s => psi_pc2 hC (Fin.natAdd 6 s)) (fun s => vAt_eq matZ2 g s t)

end CFSG.KD.G24B
