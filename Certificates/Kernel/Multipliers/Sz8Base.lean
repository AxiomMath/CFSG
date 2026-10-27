module

public import Certificates.Kernel.Multipliers.U43Cone
public import Certificates.Kernel.Multipliers.ZProd
public import Certificates.Kernel.Multipliers.Ent
public import CFSG.Certificates.Kernel.Bounds.Sz8Alt.Data.C_Sel
public import CFSG.Certificates.Kernel.Bounds.Sz8Alt.Checks.C_H
public import CFSG.Certificates.Kernel.Bounds.Sz8Alt.Checks.C_W
public import CFSG.Certificates.Kernel.Bounds.Sz8Alt.Checks.C_L
public import CFSG.LieType.Multipliers.Sz8Inputs
import all CFSG.LieType.Multipliers.Sz8BridgeInputs
import all CFSG.LieType.Multipliers.Sz8Inputs
import all CFSG.LieType.Multipliers.CoverWords

set_option exponentiation.threshold 2048
set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelSz8

open CFSG.KC CFSG.KC.LceS CFSG.Certificates.LCE CFSG.Certificates.LabZ CFSG.LieType.Multipliers
  CFSG.LieType.Multipliers.Sz8 CFSG.CosetTable CertificateChecks.KernelMult

#kc_join_range Cfacts CertificateChecks.KernelCo2.runFacts_append CFSG.KD.Sz8C "sW" 0 0
#kc_join_range Clab CertificateChecks.KernelU43.runLabZ_append CFSG.KD.Sz8C "sL" 0 0
#kc_join_range Cids CertificateChecks.KernelU43.runIds_append CFSG.KD.Sz8C "sI" 0 0

abbrev coverWs : List (List (Fin 2 × Bool)) := coverWords rels wWord

@[expose] noncomputable def z (k : ℕ) : PG 2 coverWs := PresentedGroup.mk _ (FreeGroup.mk (rels.getD k []))

noncomputable abbrev gen : ℕ → PG 2 coverWs := CFSG.KC.MiscCoset.pgGen coverWs

theorem bval_rel {e : ℕ} (w : List (Fin 2 × Bool)) (h : e = ent w) (hlen : w.length < 1024) :
    bval gen (wWord e) (wLen e) = PresentedGroup.mk _ (FreeGroup.mk w) :=
  bval_ent (by norm_num) coverWs w h hlen

theorem mem_comm : ∀ i : Fin 2, ∀ k < 6, commWord [(i, true)] (rels.getD k []) ∈ coverWs := by
  decide +kernel

theorem z_central {k : ℕ} (hk : k < 6) : z k ∈ Subgroup.center (PG 2 coverWs) := by
  rw [← Subgroup.centralizer_univ, ← Subgroup.coe_top, ← PresentedGroup.closure_range_of,
    Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro _ ⟨i, rfl⟩
  have h : PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk}
      (FreeGroup.mk (commWord [(i, true)] (rels.getD k []))) = 1 :=
    PresentedGroup.one_of_mem (List.mem_map_of_mem (mem_comm i k hk))
  rw [mk_commWord, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

noncomputable def gg (d : ℕ) : PG 2 coverWs :=
  if d < 8 then bval gen (wWord (CFSG.KC.Sz8Alt.rel d)) (wLen (CFSG.KC.Sz8Alt.rel d))
  else if d = 8 then bval gen (wWord (CFSG.KC.Sz8Alt.sub 0)) (wLen (CFSG.KC.Sz8Alt.sub 0)) else 1

theorem rel_ent : ∀ k < 6, CFSG.KC.Sz8Alt.rel k = ent (rels.getD k []) := by
  decide +kernel

theorem cover_ent : ∀ i < 2, ∃ w ∈ coverWs, CFSG.KC.Sz8Alt.rel (6 + i) = ent w ∧ w.length < 1024 := by
  decide +kernel

theorem gg_rel {k : ℕ} (hk : k < 6) : gg k = z k := by
  have h8 : k < 8 := by omega
  have hl : ∀ k < 6, (rels.getD k []).length < 1024 := by decide +kernel
  simp only [gg, h8, ↓reduceIte]
  rw [bval_rel _ (rel_ent k hk) (hl k hk)]
  rfl

theorem gg_cover {i : ℕ} (hi : i < 2) : gg (6 + i) = 1 := by
  obtain ⟨w, hw, he, hl⟩ := cover_ent i hi
  have h8 : 6 + i < 8 := by omega
  simp only [gg, h8, ↓reduceIte]
  rw [bval_rel _ he hl]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)

theorem gg_central {r : ℕ} (hr : r < 8) : gg r ∈ Subgroup.center (PG 2 coverWs) := by
  rcases Nat.lt_or_ge r 6 with h | h
  · exact gg_rel h ▸ z_central h
  · have e : r = 6 + (r - 6) := by omega
    rw [e, gg_cover (by omega)]
    exact Subgroup.one_mem _

theorem gg_center_or (d : ℕ) : gg d ∈ Subgroup.center (PG 2 coverWs) ∨ gg d = gg 8 := by
  rcases Nat.lt_or_ge d 8 with h | h
  · exact Or.inl (gg_central h)
  · rcases Nat.lt_or_ge d 9 with h' | h'
    · exact Or.inr (by rw [show d = 8 by omega])
    · left
      simp only [gg, show ¬ (d < 8) from by omega, show ¬ (d = 8) from by omega, ↓reduceIte]
      exact Subgroup.one_mem _

theorem gg_comm (i j : ℕ) : Commute (gg i) (gg j) := by
  rcases gg_center_or i with hi | hi
  · exact (Subgroup.mem_center_iff.mp hi (gg j)).symm
  rcases gg_center_or j with hj | hj
  · exact Subgroup.mem_center_iff.mp hj (gg i)
  rw [hi, hj]

theorem hRT : ∀ r < 8, wWord (CFSG.KD.Sz8C.selRT r) < 2 ^ (8 * wLen (CFSG.KD.Sz8C.selRT r)) ∧
    bval gen (wWord (CFSG.KD.Sz8C.selRT r)) (wLen (CFSG.KD.Sz8C.selRT r)) = gg r ∧
      ∀ c, Commute (letV gen c) (gg r) := by
  have hcl : ∀ r < 8, wWord (CFSG.KD.Sz8C.selRT r) < 2 ^ (8 * wLen (CFSG.KD.Sz8C.selRT r)) := by
    decide
  intro r hr
  refine ⟨hcl r hr, ?_, fun c => Subgroup.mem_center_iff.mp (gg_central hr) _⟩
  simp only [gg, hr, ↓reduceIte]
  rfl

theorem hST : ∀ j < 1, bval gen (wWord (CFSG.KD.Sz8C.selST j)) (wLen (CFSG.KD.Sz8C.selST j)) =
    gg (8 + j) := by
  intro j hj
  have : j = 0 := by omega
  subst this
  simp only [gg, show ¬ (8 + 0 < 8) from by omega, show 8 + 0 = 8 from rfl, ↓reduceIte]
  rfl

theorem cyc_of {c wid R V : ℕ} (hc : c < 2 ^ 20) (hwid : wid < 64)
    (h : LabZ.cycZ CFSG.KD.Sz8C.blk CFSG.KD.Sz8C.selWT CFSG.KD.Sz8C.LB CFSG.KD.Sz8C.BIAS 0x56b c wid R V
      = true) :
    zprod gg 9 (decZ V) = zprod gg 9 (decZ (CFSG.KD.Sz8C.TG wid)) :=
  cyc_sound gen gg gg_comm
    (KernelU43.coneOk_intro CFSG.KD.Sz8C.sH0 CFSG.KD.Sz8C.sH1 (by rfl) (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) CFSG.KD.Sz8C.sH6 Cids CFSG.KD.Sz8C.sH7 CFSG.KD.Sz8C.sH8 Cfacts Clab)
    hRT hST rfl hc hwid h

theorem rel_of {c wid R V : ℕ} (ρ : List ℤ) (hc : c < 2 ^ 20) (hwid : wid < 64)
    (h : LabZ.cycZ CFSG.KD.Sz8C.blk CFSG.KD.Sz8C.selWT CFSG.KD.Sz8C.LB CFSG.KD.Sz8C.BIAS 0x56b c wid R V
      = true)
    (hρ : ∀ d < 9, decZ V d - decZ (CFSG.KD.Sz8C.TG wid) d = ρ.getD d 0) :
    zprod gg 9 (fun d => ρ.getD d 0) = 1 := by
  rw [← zprod_congr gg hρ]
  change zprod gg 9 (decZ V - decZ (CFSG.KD.Sz8C.TG wid)) = 1
  rw [zprod_sub gg_comm, cyc_of hc hwid h, mul_inv_cancel]

end CertificateChecks.KernelSz8

end
