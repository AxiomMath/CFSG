module

public import Certificates.Kernel.Multipliers.U62Cone
public import Certificates.Kernel.Multipliers.ZProd
public import Certificates.Kernel.Multipliers.Ent
public import CFSG.LieType.Multipliers.U62SylowInputs

set_option exponentiation.threshold 2048
set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelU62

open CFSG.KC CFSG.KC.LceS CFSG.Certificates.LCE CFSG.Certificates.LabZ CFSG.LieType.Multipliers
  CFSG.LieType.Multipliers.U62 CFSG.CosetTable CertificateChecks.KernelMult

abbrev rels₁ : List (List (Fin 4 × Bool)) := restrictWords (subsetOf 5 [0, 1, 2, 3]) rels

@[expose] noncomputable def z₁ (k : ℕ) : PG 4 cover₁ := PresentedGroup.mk _ (FreeGroup.mk (rels₁.getD k []))

noncomputable abbrev gen : ℕ → PG 4 cover₁ := CFSG.KC.MiscCoset.pgGen cover₁

theorem bval_rel {e : ℕ} (w : List (Fin 4 × Bool)) (h : e = ent w) (hlen : w.length < 1024) :
    bval gen (wWord e) (wLen e) = PresentedGroup.mk _ (FreeGroup.mk w) :=
  bval_ent (by norm_num) cover₁ w h hlen

theorem mem_comm : ∀ i : Fin 4, ∀ k < 16, commWord [(i, true)] (rels₁.getD k []) ∈ cover₁ := by
  decide

theorem z₁_central {k : ℕ} (hk : k < 16) : z₁ k ∈ Subgroup.center (PG 4 cover₁) := by
  rw [← Subgroup.centralizer_univ, ← Subgroup.coe_top, ← PresentedGroup.closure_range_of,
    Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro _ ⟨i, rfl⟩
  have h : PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ cover₁.map FreeGroup.mk}
      (FreeGroup.mk (commWord [(i, true)] (rels₁.getD k []))) = 1 :=
    PresentedGroup.one_of_mem (List.mem_map_of_mem (mem_comm i k hk))
  rw [mk_commWord, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

noncomputable def gg (d : ℕ) : PG 4 cover₁ :=
  if d < 20 then bval gen (wWord (CFSG.KC.U62Alt.rel d)) (wLen (CFSG.KC.U62Alt.rel d))
  else if d = 20 then bval gen (wWord (CFSG.KC.U62Alt.sub 0)) (wLen (CFSG.KC.U62Alt.sub 0)) else 1

theorem rel_ent : ∀ k < 16,
    CFSG.KC.U62Alt.rel k = ent (rels₁.getD k []) := by
  decide

theorem cover_ent : ∀ i < 4, ∃ w ∈ cover₁,
    CFSG.KC.U62Alt.rel (16 + i) = ent w ∧ w.length < 1024 := by
  decide

theorem gg_rel {k : ℕ} (hk : k < 16) : gg k = z₁ k := by
  have h20 : k < 20 := by omega
  have hl : ∀ k < 16, (rels₁.getD k []).length < 1024 := by decide
  simp only [gg, h20, ↓reduceIte]
  rw [bval_rel _ (rel_ent k hk) (hl k hk)]
  rfl

theorem gg_cover {i : ℕ} (hi : i < 4) : gg (16 + i) = 1 := by
  obtain ⟨w, hw, he, hl⟩ := cover_ent i hi
  have h20 : 16 + i < 20 := by omega
  simp only [gg, h20, ↓reduceIte]
  rw [bval_rel _ he hl]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)

theorem gg_central {r : ℕ} (hr : r < 20) : gg r ∈ Subgroup.center (PG 4 cover₁) := by
  rcases Nat.lt_or_ge r 16 with h | h
  · exact gg_rel h ▸ z₁_central h
  · have e : r = 16 + (r - 16) := by omega
    rw [e, gg_cover (by omega)]
    exact Subgroup.one_mem _

theorem gg_center_or (d : ℕ) : gg d ∈ Subgroup.center (PG 4 cover₁) ∨ gg d = gg 20 := by
  rcases Nat.lt_or_ge d 20 with h | h
  · exact Or.inl (gg_central h)
  · rcases Nat.lt_or_ge d 21 with h' | h'
    · exact Or.inr (by rw [show d = 20 by omega])
    · left
      simp only [gg, show ¬ (d < 20) from by omega, show ¬ (d = 20) from by omega, ↓reduceIte]
      exact Subgroup.one_mem _

theorem gg_comm (i j : ℕ) : Commute (gg i) (gg j) := by
  rcases gg_center_or i with hi | hi
  · exact (Subgroup.mem_center_iff.mp hi (gg j)).symm
  rcases gg_center_or j with hj | hj
  · exact Subgroup.mem_center_iff.mp hj (gg i)
  rw [hi, hj]

theorem hRT : ∀ r < 20, wWord (CFSG.KD.U52C.selRT r) < 2 ^ (8 * wLen (CFSG.KD.U52C.selRT r)) ∧
    bval gen (wWord (CFSG.KD.U52C.selRT r)) (wLen (CFSG.KD.U52C.selRT r)) = gg r ∧
      ∀ c, Commute (letV gen c) (gg r) := by
  have hcl : ∀ r < 20, wWord (CFSG.KD.U52C.selRT r) < 2 ^ (8 * wLen (CFSG.KD.U52C.selRT r)) := by
    decide
  intro r hr
  refine ⟨hcl r hr, ?_, fun c => Subgroup.mem_center_iff.mp (gg_central hr) _⟩
  simp only [gg, hr, ↓reduceIte]
  rfl

theorem hST : ∀ j < 1, bval gen (wWord (CFSG.KD.U52C.selST j)) (wLen (CFSG.KD.U52C.selST j)) =
    gg (20 + j) := by
  intro j hj
  have : j = 0 := by omega
  subst this
  simp only [gg, show ¬ (20 + 0 < 20) from by omega, show 20 + 0 = 20 from rfl, ↓reduceIte]
  rfl

theorem cyc_of {c wid R V : ℕ} (hc : c < 2 ^ 20) (hwid : wid < 512)
    (h : LabZ.cycZ CFSG.KD.U52C.blk CFSG.KD.U52C.selWT CFSG.KD.U52C.LB CFSG.KD.U52C.BIAS 0x688f c wid R V
      = true) :
    zprod gg 21 (decZ V) = zprod gg 21 (decZ (CFSG.KD.U52C.TG wid)) :=
  cyc_sound gen gg gg_comm
    (KernelU43.coneOk_intro CFSG.KD.U52C.sH0 CFSG.KD.U52C.sH1 (by rfl) (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) CFSG.KD.U52C.sH6 Cids CFSG.KD.U52C.sH7 CFSG.KD.U52C.sH8 Cfacts Clab)
    hRT hST rfl hc hwid h

theorem rel_of {c wid R V : ℕ} (ρ : List ℤ) (hc : c < 2 ^ 20) (hwid : wid < 512)
    (h : LabZ.cycZ CFSG.KD.U52C.blk CFSG.KD.U52C.selWT CFSG.KD.U52C.LB CFSG.KD.U52C.BIAS 0x688f c wid R V
      = true)
    (hρ : ∀ d < 21, decZ V d - decZ (CFSG.KD.U52C.TG wid) d = ρ.getD d 0) :
    zprod gg 21 (fun d => ρ.getD d 0) = 1 := by
  rw [← zprod_congr gg hρ]
  change zprod gg 21 (decZ V - decZ (CFSG.KD.U52C.TG wid)) = 1
  rw [zprod_sub gg_comm, cyc_of hc hwid h, mul_inv_cancel]

end CertificateChecks.KernelU62

end
