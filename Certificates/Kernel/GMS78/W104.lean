module

public import Certificates.Kernel.GMS78.W104Chk

public section

namespace CertificateChecks.KernelGMS78.W

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.GMSW CFSG.Sporadic.SmallF2 CFSG.Sporadic.Bridge
  CFSG.Sporadic.Bridge.VecSurj CFSG.ComponentClassification.GMS78.RuPi7
  CFSG.ComponentClassification.GMS78.RuCz

local notation "Dt" => CFSG.Sporadic.Ru.Native.ruData

local notation "MUL" => CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28)
  (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM

theorem wordProd_nat (v : List (ℕ × Bool)) :
    wordProd (img pi7RuSpec (seedG Dt)) v = wordProd phi (v.map fun l => (l.1 + 2, l.2)) := by
  induction v with
  | nil => rfl
  | cons l v ih =>
    simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, phi_img]

theorem nat_rel {R : List (List (Nat × Bool))} {n : Nat} {rs : List (List (ℕ × Bool))}
    (hb : relsBounded R 9 = true) (hok : ∀ j < n, relOK RG MUL R 9 CFSG.KD.OrdRu.ONE j = true)
    (hn : Nat.beq (lenRels R) n = true) (hR : relsEqK R (mkNatK rs) = true) :
    ∀ v ∈ rs, (∀ l ∈ v, l.1 < 7) ∧ wordProd (img pi7RuSpec (seedG Dt)) v = 1 := by
  intro v hv
  have hmem : v.map natLetK ∈ R := by
    rw [relsEqK_eq hR, mkNatK_eq]
    exact List.mem_map_of_mem hv
  have hne : ∀ l ∈ v, natLetK l ≠ badLet := fun l hl => ne_bad hb hmem (List.mem_map_of_mem hl)
  have he : v.map natLetK = v.map fun l => (l.1 + 2, l.2) :=
    List.map_congr_left fun l hl => (natLetK_of_ne (hne l hl)).2
  refine ⟨fun l hl => (natLetK_of_ne (hne l hl)).1, ?_⟩
  rw [wordProd_nat, ← he]
  exact wordProd_phi_eq_one hb (relsAll_of_forall hok) hn hmem

theorem czJRel_hold :
    ∀ v ∈ czJRelRels, (∀ l ∈ v, l.1 < 7) ∧ wordProd (img pi7RuSpec (seedG Dt)) v = 1 :=
  nat_rel RJ1_bd (CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) RJ1_blk.all)
    RJ1_len RJ1_bind

theorem c2Ru_hold :
    ∀ v ∈ c2RuRels, (∀ l ∈ v, l.1 < 7) ∧ wordProd (img pi7RuSpec (seedG Dt)) v = 1 :=
  nat_rel RC2_bd (CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) RC2_blk.all)
    RC2_len RC2_bind

theorem czRu_hold :
    ∀ v ∈ czRuRels, (∀ l ∈ v, l.1 < 7) ∧ wordProd (img pi7RuSpec (seedG Dt)) v = 1 :=
  nat_rel RZ4_bd (CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) RZ4_blk.all)
    RZ4_len RZ4_bind

end CertificateChecks.KernelGMS78.W

end
