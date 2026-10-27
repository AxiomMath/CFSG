module

public import Certificates.Kernel.Misc.Perm.Fuse.Checks
public import Certificates.Kernel.Misc.Perm.SylCent.Facts
public import CFSG.Certificates.Kernel.Misc.PermFuseSound
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourCertificate

public section

namespace CertificateChecks.KernelMisc.Fuse

open Equiv CFSG.KC.Ord CFSG.KS CFSG.KC.Misc.Clos CFSG.KC.Misc.ClosW CFSG.KC.Misc.Fuse
open CFSG.KC.LQT.P (allN impB letB)
open CFSG.KC.Enum (pcomp pidn)
open CFSG.ComponentClassification.PSL3Four
open CertificateChecks.KernelMisc.SylCent (GC hGC hw hn enc S_eq)

theorem hGS : ∀ j < [g₁, g₂, g₃].length, GC j = wcode 6 ([g₁, g₂, g₃].getD j 1) :=
  CertificateChecks.KernelMisc.SylCent.hGS

theorem s_elt {W : ℕ → List ℕ} {C : ℕ → ℕ} {j : ℕ} (h : wWordAt 42 6 GC 3 W C j = true) :
    ∃ s ∈ S, wcode 6 s = C j := by
  obtain ⟨h1, h2⟩ := andB_eq_true h
  obtain ⟨p, hp, hpc⟩ := wword_mem hw hn [g₁, g₂, g₃] hGS h1
  exact ⟨p, S_eq ▸ hp, hpc.trans (Nat.eq_of_beq_eq_true h2)⟩

theorem fuse_of (hS : Nat.card S = 20160) (r : Perm (Fin 42)) {R0 M N : ℕ} (hR : wcode 6 r = R0)
    {KG E PA SG CT O OP OS SC : ℕ → ℕ} {KW SW : ℕ → List ℕ} (hMN : N * M = 20160)
    (hkw : allN 2 (wWordAt 42 6 GC 3 KW KG) = true)
    (hkc : allN 2 (fun j => commK 42 6 (KG j) R0) = true)
    (htree : allN M (treeAt (pcomp 42 6 (mask 6)) (pidn 42 6) KG 2 E PA) = true)
    (hsort : allN M (sortAt M E SG) = true)
    (hcl : allN M (closedAt (pcomp 42 6 (mask 6)) KG 2 M E CT) = true)
    (hot : allN N (treeAt (conjM 42 6) R0 GC 3 O OP) = true)
    (hos : allN N (sortAt N O OS) = true)
    (hf : allN M (fuseAt 42 6 R0 E GC 3 SW SC) = true) :
    ∀ c ∈ S, c * r = r * c → c * c = 1 → ∃ s ∈ S, s * r = r * c * s := by
  classical
  have hk : ∀ j < 2, ∃ k ∈ S, wcode 6 k = KG j := fun j hj => s_elt ((allN_iff _ _).1 hkw j hj)
  choose! kE hkS hkC using hk
  have hkr : ∀ j < 2, kE j * r = r * kE j := fun j hj => by
    apply enc.inj
    rw [enc.enc_mul, enc.enc_mul, hkC j hj, hR]
    exact Nat.eq_of_beq_eq_true ((allN_iff _ _).1 hkc j hj)
  set K : Subgroup (Perm (Fin 42)) := Subgroup.closure {g | g ∈ [kE 0, kE 1]} with hKdef
  have hKG : ∀ j < [kE 0, kE 1].length, KG j = wcode 6 ([kE 0, kE 1].getD j 1) := by
    intro j hj
    have hj2 : j < 2 := hj
    interval_cases j
    · exact (hkC 0 (by norm_num)).symm
    · exact (hkC 1 (by norm_num)).symm
  have hM : 0 < M := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hMN
  have hN : 0 < N := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hMN
  have hclos := clos_card enc [kE 0, kE 1] hKG hM ((allN_iff _ _).1 htree) ((allN_iff _ _).1 hsort)
  obtain ⟨hcardK, hcomplete⟩ := hclos.2.2 ((allN_iff _ _).1 hcl)
  have hKC : K ≤ S ⊓ Subgroup.centralizer {r} := by
    rw [hKdef, Subgroup.closure_le]
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
    rcases hg with rfl | rfl
    · exact ⟨hkS 0 (by norm_num), Subgroup.mem_centralizer_singleton_iff.2 (hkr 0 (by norm_num))⟩
    · exact ⟨hkS 1 (by norm_num), Subgroup.mem_centralizer_singleton_iff.2 (hkr 1 (by norm_num))⟩
  have hot' := orb_tree CertificateChecks.KernelMisc.SylCent.hw' (by norm_num) [g₁, g₂, g₃] r hGS (hR ▸ (allN_iff _ _).1 hot)
  choose! tE htS htC using hot'
  have hdist := sort_distinct ((allN_iff _ _).1 hos)
  have hle := card_mul_cent_le S r N tE (fun k hk => S_eq ▸ htS k hk) fun i hi j hj h => by
    refine hdist i hi j hj ?_
    rw [← htC i hi, ← htC j hj, h]
  rw [hS, ← hMN] at hle
  have hCK : K = S ⊓ Subgroup.centralizer {r} := by
    refine Subgroup.eq_of_le_of_card_ge hKC ?_
    rw [hcardK]
    exact Nat.le_of_mul_le_mul_left hle hN
  intro c hcS hcr hc2
  by_cases hc1 : c = 1
  · exact ⟨1, S.one_mem, by rw [hc1]; group⟩
  have hcK : c ∈ K := by
    rw [hCK]
    exact ⟨hcS, Subgroup.mem_centralizer_singleton_iff.2 hcr⟩
  obtain ⟨k, hkM, hck⟩ := hcomplete c hcK
  have hfk := (allN_iff _ _).1 hf k hkM
  rw [fuseAt, letB_eq] at hfk
  have hinv : CFSG.KC.Ord.andB (Nat.beq (pcomp 42 6 (mask 6) (E k) (E k)) (pidn 42 6))
      (notB (Nat.beq (E k) (pidn 42 6))) = true := by
    rw [← hck, ← enc.enc_mul, hc2, enc.enc_one, Nat.beq_refl]
    have : Nat.beq (wcode 6 c) (pidn 42 6) = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hc1 (enc.inj ((Nat.eq_of_beq_eq_true h).trans enc.enc_one.symm))
    rw [this]
    rfl
  obtain ⟨hw', he⟩ := andB_eq_true (impB_eq_true hfk hinv)
  obtain ⟨s, hsS, hsc⟩ := s_elt hw'
  refine ⟨s, hsS, enc.inj ?_⟩
  rw [enc.enc_mul, enc.enc_mul, enc.enc_mul, hsc, hR, hck]
  exact Nat.eq_of_beq_eq_true he

theorem hr₂ : wcode 6 r₂ = GC 4 := (hGC 4 (by norm_num)).symm
theorem hr₃ : wcode 6 r₃ = GC 5 := (hGC 5 (by norm_num)).symm
theorem hr₄ : wcode 6 r₄ = pcomp 42 6 (mask 6) (GC 4) (GC 5) := by
  rw [r₄, enc.enc_mul, ← hr₂, ← hr₃]
  rfl

open Certificates in
open CFSG.ComponentClassification.PSL3Four in
theorem facts : Nat.card S = 20160 → ∀ r ∈ [r₂, r₃, r₄], ∀ c ∈ S, c * r = r * c → c * c = 1 →
    ∃ s ∈ S, s * r = r * c * s := by
  refine fun hS r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact fuse_of hS r₂ hr₂ (by norm_num) kw2 kc2 tree2 sort2 cl2 ot2 os2 f2
  · exact fuse_of hS r₃ hr₃ (by norm_num) kw3 kc3 tree3 sort3 cl3 ot3 os3 f3
  · exact fuse_of hS r₄ hr₄ (by norm_num) kw4 kc4 tree4 sort4 cl4 ot4 os4 f4

end CertificateChecks.KernelMisc.Fuse

end
