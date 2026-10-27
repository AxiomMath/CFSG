module

public import Certificates.Kernel.Multipliers.U43Cone
public import Certificates.Kernel.Multipliers.ZProd
public import Certificates.Kernel.Multipliers.Ent
public import CFSG.Certificates.Kernel.Bounds.U42Alt.Data.C_Sel
public import CFSG.Certificates.Kernel.Bounds.U42Alt.Checks.C_H
public import CFSG.Certificates.Kernel.Bounds.U42Alt.Checks.C_W
public import CFSG.Certificates.Kernel.Bounds.U42Alt.Checks.C_L
public import CFSG.LieType.Multipliers.U42Data
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

set_option exponentiation.threshold 2048
set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelU42

open CFSG.KC CFSG.KC.LceS CFSG.Certificates.LCE CFSG.Certificates.LabZ CFSG.LieType.Multipliers
  CFSG.LieType.Multipliers.U42 CFSG.CosetTable CertificateChecks.KernelMult

#kc_join_range Cfacts CertificateChecks.KernelCo2.runFacts_append CFSG.KD.U42C "sW" 0 0
#kc_join_range Clab CertificateChecks.KernelU43.runLabZ_append CFSG.KD.U42C "sL" 0 0
#kc_join_range Cids CertificateChecks.KernelU43.runIds_append CFSG.KD.U42C "sI" 0 0

abbrev coverWs : List (List (Fin 2 × Bool)) := coverWords rels fun i => commWords (coverPairs i)

@[expose] noncomputable def z (k : ℕ) : PG 2 coverWs := PresentedGroup.mk _ (FreeGroup.mk (rels.getD k []))

noncomputable abbrev gen : ℕ → PG 2 coverWs := CFSG.KC.MiscCoset.pgGen coverWs

theorem bval_rel {e : ℕ} (w : List (Fin 2 × Bool)) (h : e = ent w) (hlen : w.length < 1024) :
    bval gen (wWord e) (wLen e) = PresentedGroup.mk _ (FreeGroup.mk w) :=
  bval_ent (by norm_num) coverWs w h hlen

theorem mem_comm : ∀ i : Fin 2, ∀ k < 5, commWord [(i, true)] (rels.getD k []) ∈ coverWs := by
  decide

theorem z_central {k : ℕ} (hk : k < 5) : z k ∈ Subgroup.center (PG 2 coverWs) := by
  rw [← Subgroup.centralizer_univ, ← Subgroup.coe_top, ← PresentedGroup.closure_range_of,
    Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro _ ⟨i, rfl⟩
  have h : PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk}
      (FreeGroup.mk (commWord [(i, true)] (rels.getD k []))) = 1 :=
    PresentedGroup.one_of_mem (List.mem_map_of_mem (mem_comm i k hk))
  rw [mk_commWord, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

noncomputable def gg (d : ℕ) : PG 2 coverWs :=
  if d < 7 then bval gen (wWord (CFSG.KC.U42Alt.rel d)) (wLen (CFSG.KC.U42Alt.rel d))
  else if d = 7 then bval gen (wWord (CFSG.KC.U42Alt.sub 0)) (wLen (CFSG.KC.U42Alt.sub 0)) else 1

theorem rel_ent : ∀ k < 5, CFSG.KC.U42Alt.rel k = ent (rels.getD k []) := by
  decide

theorem cover_ent : ∀ i < 2, ∃ w ∈ coverWs, CFSG.KC.U42Alt.rel (5 + i) = ent w ∧ w.length < 1024 := by
  decide

theorem gg_rel {k : ℕ} (hk : k < 5) : gg k = z k := by
  have h7 : k < 7 := by omega
  have hl : ∀ k < 5, (rels.getD k []).length < 1024 := by decide
  simp only [gg, h7, ↓reduceIte]
  rw [bval_rel _ (rel_ent k hk) (hl k hk)]
  rfl

theorem gg_cover {i : ℕ} (hi : i < 2) : gg (5 + i) = 1 := by
  obtain ⟨w, hw, he, hl⟩ := cover_ent i hi
  have h7 : 5 + i < 7 := by omega
  simp only [gg, h7, ↓reduceIte]
  rw [bval_rel _ he hl]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)

theorem gg_central {r : ℕ} (hr : r < 7) : gg r ∈ Subgroup.center (PG 2 coverWs) := by
  rcases Nat.lt_or_ge r 5 with h | h
  · exact gg_rel h ▸ z_central h
  · have e : r = 5 + (r - 5) := by omega
    rw [e, gg_cover (by omega)]
    exact Subgroup.one_mem _

theorem gg_center_or (d : ℕ) : gg d ∈ Subgroup.center (PG 2 coverWs) ∨ gg d = gg 7 := by
  rcases Nat.lt_or_ge d 7 with h | h
  · exact Or.inl (gg_central h)
  · rcases Nat.lt_or_ge d 8 with h' | h'
    · exact Or.inr (by rw [show d = 7 by omega])
    · left
      simp only [gg, show ¬ (d < 7) from by omega, show ¬ (d = 7) from by omega, ↓reduceIte]
      exact Subgroup.one_mem _

theorem gg_comm (i j : ℕ) : Commute (gg i) (gg j) := by
  rcases gg_center_or i with hi | hi
  · exact (Subgroup.mem_center_iff.mp hi (gg j)).symm
  rcases gg_center_or j with hj | hj
  · exact Subgroup.mem_center_iff.mp hj (gg i)
  rw [hi, hj]

theorem hRT : ∀ r < 7, wWord (CFSG.KD.U42C.selRT r) < 2 ^ (8 * wLen (CFSG.KD.U42C.selRT r)) ∧
    bval gen (wWord (CFSG.KD.U42C.selRT r)) (wLen (CFSG.KD.U42C.selRT r)) = gg r ∧
      ∀ c, Commute (letV gen c) (gg r) := by
  have hcl : ∀ r < 7, wWord (CFSG.KD.U42C.selRT r) < 2 ^ (8 * wLen (CFSG.KD.U42C.selRT r)) := by
    decide
  intro r hr
  refine ⟨hcl r hr, ?_, fun c => Subgroup.mem_center_iff.mp (gg_central hr) _⟩
  simp only [gg, hr, ↓reduceIte]
  rfl

theorem hST : ∀ j < 1, bval gen (wWord (CFSG.KD.U42C.selST j)) (wLen (CFSG.KD.U42C.selST j)) =
    gg (7 + j) := by
  intro j hj
  have : j = 0 := by omega
  subst this
  simp only [gg, show ¬ (7 + 0 < 7) from by omega, show 7 + 0 = 7 from rfl, ↓reduceIte]
  rfl

theorem cyc_of {c wid R V : ℕ} (hc : c < 2 ^ 20) (hwid : wid < 32)
    (h : LabZ.cycZ CFSG.KD.U42C.blk CFSG.KD.U42C.selWT CFSG.KD.U42C.LB CFSG.KD.U42C.BIAS 0x1cc c wid R V
      = true) :
    zprod gg 8 (decZ V) = zprod gg 8 (decZ (CFSG.KD.U42C.TG wid)) :=
  cyc_sound gen gg gg_comm
    (KernelU43.coneOk_intro CFSG.KD.U42C.sH0 CFSG.KD.U42C.sH1 (by rfl) (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) CFSG.KD.U42C.sH6 Cids CFSG.KD.U42C.sH7 CFSG.KD.U42C.sH8 Cfacts Clab)
    hRT hST rfl hc hwid h

theorem rel_of {c wid R V : ℕ} (ρ : List ℤ) (hc : c < 2 ^ 20) (hwid : wid < 32)
    (h : LabZ.cycZ CFSG.KD.U42C.blk CFSG.KD.U42C.selWT CFSG.KD.U42C.LB CFSG.KD.U42C.BIAS 0x1cc c wid R V
      = true)
    (hρ : ∀ d < 8, decZ V d - decZ (CFSG.KD.U42C.TG wid) d = ρ.getD d 0) :
    zprod gg 8 (fun d => ρ.getD d 0) = 1 := by
  rw [← zprod_congr gg hρ]
  change zprod gg 8 (decZ V - decZ (CFSG.KD.U42C.TG wid)) = 1
  rw [zprod_sub gg_comm, cyc_of hc hwid h, mul_inv_cancel]

end CertificateChecks.KernelU42

end
