module

public import Certificates.Kernel.Multipliers.U43Cone
public import Certificates.Kernel.Multipliers.ZProd
public import Certificates.Kernel.Multipliers.Ent
public import CFSG.Certificates.Kernel.Bounds.L34Alt.Data.C_Sel
public import CFSG.Certificates.Kernel.Bounds.L34Alt.Checks.C_H
public import CFSG.Certificates.Kernel.Bounds.L34Alt.Checks.C_W
public import CFSG.Certificates.Kernel.Bounds.L34Alt.Checks.C_L
public import CFSG.LieType.Multipliers.L34UpperData
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

set_option exponentiation.threshold 2048
set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelL34H

open CFSG.KC CFSG.KC.LceS CFSG.Certificates.LCE CFSG.Certificates.LabZ CFSG.LieType.Multipliers
  CFSG.LieType.Multipliers.L34 CFSG.LieType.Multipliers.L34Upper CFSG.CosetTable
  CertificateChecks.KernelMult

#kc_join_range Cfacts CertificateChecks.KernelCo2.runFacts_append CFSG.KD.L34C "sW" 0 2
#kc_join_range Clab CertificateChecks.KernelU43.runLabZ_append CFSG.KD.L34C "sL" 0 2
#kc_join_range Cids CertificateChecks.KernelU43.runIds_append CFSG.KD.L34C "sI" 0 2

@[expose] noncomputable def z (k : ℕ) : PG 2 hopfWs := PresentedGroup.mk _ (FreeGroup.mk (rels.getD k []))

noncomputable abbrev gen : ℕ → PG 2 hopfWs := CFSG.KC.MiscCoset.pgGen hopfWs

theorem bval_rel {e : ℕ} (w : List (Fin 2 × Bool)) (h : e = ent w) (hlen : w.length < 1024) :
    bval gen (wWord e) (wLen e) = PresentedGroup.mk _ (FreeGroup.mk w) :=
  bval_ent (by norm_num) hopfWs w h hlen

theorem mem_comm : ∀ i : Fin 2, ∀ k < 7, commWord [(i, true)] (rels.getD k []) ∈ hopfWs := by
  decide +kernel

theorem z_central {k : ℕ} (hk : k < 7) : z k ∈ Subgroup.center (PG 2 hopfWs) := by
  rw [← Subgroup.centralizer_univ, ← Subgroup.coe_top, ← PresentedGroup.closure_range_of,
    Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro _ ⟨i, rfl⟩
  have h : PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ hopfWs.map FreeGroup.mk}
      (FreeGroup.mk (commWord [(i, true)] (rels.getD k []))) = 1 :=
    PresentedGroup.one_of_mem (List.mem_map_of_mem (mem_comm i k hk))
  rw [mk_commWord, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

noncomputable def gg (d : ℕ) : PG 2 hopfWs :=
  if d < 9 then bval gen (wWord (CFSG.KC.L34Alt.rel d)) (wLen (CFSG.KC.L34Alt.rel d))
  else if d = 9 then bval gen (wWord (CFSG.KC.L34Alt.sub 0)) (wLen (CFSG.KC.L34Alt.sub 0)) else 1

theorem rel_ent : ∀ k < 7, CFSG.KC.L34Alt.rel k = ent (rels.getD k []) := by
  decide +kernel

theorem cover_ent : ∀ i < 2, ∃ w ∈ hopfWs, CFSG.KC.L34Alt.rel (7 + i) = ent w ∧ w.length < 1024 := by
  decide +kernel

theorem gg_rel {k : ℕ} (hk : k < 7) : gg k = z k := by
  have h9 : k < 9 := by omega
  have hl : ∀ k < 7, (rels.getD k []).length < 1024 := by decide +kernel
  simp only [gg, h9, ↓reduceIte]
  rw [bval_rel _ (rel_ent k hk) (hl k hk)]
  rfl

theorem gg_cover {i : ℕ} (hi : i < 2) : gg (7 + i) = 1 := by
  obtain ⟨w, hw, he, hl⟩ := cover_ent i hi
  have h9 : 7 + i < 9 := by omega
  simp only [gg, h9, ↓reduceIte]
  rw [bval_rel _ he hl]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)

theorem gg_central {r : ℕ} (hr : r < 9) : gg r ∈ Subgroup.center (PG 2 hopfWs) := by
  rcases Nat.lt_or_ge r 7 with h | h
  · exact gg_rel h ▸ z_central h
  · have e : r = 7 + (r - 7) := by omega
    rw [e, gg_cover (by omega)]
    exact Subgroup.one_mem _

theorem gg_center_or (d : ℕ) : gg d ∈ Subgroup.center (PG 2 hopfWs) ∨ gg d = gg 9 := by
  rcases Nat.lt_or_ge d 9 with h | h
  · exact Or.inl (gg_central h)
  · rcases Nat.lt_or_ge d 10 with h' | h'
    · exact Or.inr (by rw [show d = 9 by omega])
    · left
      simp only [gg, show ¬ (d < 9) from by omega, show ¬ (d = 9) from by omega, ↓reduceIte]
      exact Subgroup.one_mem _

theorem gg_comm (i j : ℕ) : Commute (gg i) (gg j) := by
  rcases gg_center_or i with hi | hi
  · exact (Subgroup.mem_center_iff.mp hi (gg j)).symm
  rcases gg_center_or j with hj | hj
  · exact Subgroup.mem_center_iff.mp hj (gg i)
  rw [hi, hj]

theorem hRT : ∀ r < 9, wWord (CFSG.KD.L34C.selRT r) < 2 ^ (8 * wLen (CFSG.KD.L34C.selRT r)) ∧
    bval gen (wWord (CFSG.KD.L34C.selRT r)) (wLen (CFSG.KD.L34C.selRT r)) = gg r ∧
      ∀ c, Commute (letV gen c) (gg r) := by
  have hcl : ∀ r < 9, wWord (CFSG.KD.L34C.selRT r) < 2 ^ (8 * wLen (CFSG.KD.L34C.selRT r)) := by
    decide +kernel
  intro r hr
  refine ⟨hcl r hr, ?_, fun c => Subgroup.mem_center_iff.mp (gg_central hr) _⟩
  simp only [gg, hr, ↓reduceIte]
  rfl

theorem hST : ∀ j < 1, bval gen (wWord (CFSG.KD.L34C.selST j)) (wLen (CFSG.KD.L34C.selST j)) =
    gg (9 + j) := by
  intro j hj
  have : j = 0 := by omega
  subst this
  simp only [gg, show ¬ (9 + 0 < 9) from by omega, show 9 + 0 = 9 from rfl, ↓reduceIte]
  rfl

theorem cyc_of {c wid R V : ℕ} (hc : c < 2 ^ 20) (hwid : wid < 64)
    (h : LabZ.cycZ CFSG.KD.L34C.blk CFSG.KD.L34C.selWT CFSG.KD.L34C.LB CFSG.KD.L34C.BIAS 0x14a6 c wid R V
      = true) :
    zprod gg 10 (decZ V) = zprod gg 10 (decZ (CFSG.KD.L34C.TG wid)) :=
  cyc_sound gen gg gg_comm
    (KernelU43.coneOk_intro CFSG.KD.L34C.sH0 CFSG.KD.L34C.sH1 (by rfl) (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) CFSG.KD.L34C.sH6 Cids CFSG.KD.L34C.sH7 CFSG.KD.L34C.sH8 Cfacts Clab)
    hRT hST rfl hc hwid h

theorem rel_of {c wid R V : ℕ} (ρ : List ℤ) (hc : c < 2 ^ 20) (hwid : wid < 64)
    (h : LabZ.cycZ CFSG.KD.L34C.blk CFSG.KD.L34C.selWT CFSG.KD.L34C.LB CFSG.KD.L34C.BIAS 0x14a6 c wid R V
      = true)
    (hρ : ∀ d < 10, decZ V d - decZ (CFSG.KD.L34C.TG wid) d = ρ.getD d 0) :
    zprod gg 10 (fun d => ρ.getD d 0) = 1 := by
  rw [← zprod_congr gg hρ]
  change zprod gg 10 (decZ V - decZ (CFSG.KD.L34C.TG wid)) = 1
  rw [zprod_sub gg_comm, cyc_of hc hwid h, mul_inv_cancel]

end CertificateChecks.KernelL34H

end
