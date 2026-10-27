
module

public import Certificates.Kernel.J4Count.ChecksFive
public import CFSG.Certificates.Kernel.J4FiveSound
public import Certificates.Kernel.J4Count.StarsBase
public import CFSG.Sporadic.J4.QT2LocFiveProofBase

@[expose] public section

namespace CertificateChecks.KernelJ4Count.Five

open CFSG.KC.J4Five CFSG.KC.J4Q CFSG.KC.J4Count CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
open CFSG.Sporadic.J4.QT2 CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs Equiv Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev G24 : Subgroup (Perm (Fin 24)) := Subgroup.closure {tauOf 0, tauOf 1, tauOf 2}

theorem hinvGB : ∀ m < 2 ^ GB.length, decode GP (combo GB m) = m := fun m hm =>
  invOK_spec gold_inv m (by simpa [GB] using hm)

section Stars

theorem pf_tau {k : ℕ} (hk : k < 3) : ∀ i < 24, pf (tauOf k) i = getN 0 (starPermOf k) i := by
  intro i hi
  rw [getN_getD, ← (tau_facts k hk).1 ⟨i, hi⟩]
  exact pf_fin (tauOf k) ⟨i, hi⟩

theorem tau_val {k : ℕ} (hk : k < 3) (j : Fin 24) : getN 0 (starPermOf k) j = (tauOf k j : ℕ) := by
  rw [← pf_tau hk j j.isLt, pf_fin]

theorem gen_tau0 : genOK GB GP (pf (tauOf 0)) = true := by
  rw [genOK_congr (pf_tau (k := 0) (by norm_num))]
  exact gold_gen0

theorem gen_tau1 : genOK GB GP (pf (tauOf 1)) = true := by
  rw [genOK_congr (pf_tau (k := 1) (by norm_num))]
  exact gold_gen1

theorem gen_tau2 : genOK GB GP (pf (tauOf 2)) = true := by
  rw [genOK_congr (pf_tau (k := 2) (by norm_num))]
  exact gold_gen2

theorem gen_G24 : ∀ g ∈ G24, genOK GB GP (pf g) = true := by
  have hS : ∀ x ∈ ({tauOf 0, tauOf 1, tauOf 2} : Set (Perm (Fin 24))), genOK GB GP (pf x) = true := by
    rintro _ (rfl | rfl | rfl)
    · exact gen_tau0
    · exact gen_tau1
    · exact gen_tau2
  have hlen : GP.length = GB.length := rfl
  exact genOK_closure hlen hinvGB gold_id hS

theorem y_val (i : Fin 24) : ((tauOf 0 * tauOf 1 * (tauOf 2)⁻¹) i : ℕ) = getN 0 YT i := by
  have t0 : ∀ j : Fin 24, getN 0 starPerm0 j = (tauOf 0 j : ℕ) := tau_val (k := 0) (by norm_num)
  have t1 : ∀ j : Fin 24, getN 0 starPerm1 j = (tauOf 1 j : ℕ) := tau_val (k := 1) (by norm_num)
  have t2 : ∀ j : Fin 24, getN 0 starPerm2 j = (tauOf 2 j : ℕ) := tau_val (k := 2) (by norm_num)
  have h := (sqOK_spec gold_sq ((tauOf 2)⁻¹ i) ((tauOf 2)⁻¹ i).isLt).1
  have e2 : getN 0 starPerm2 ((tauOf 2)⁻¹ i) = i := by
    rw [t2, Perm.eq_inv_iff_eq.1 rfl]
  rw [e2, t1, t0] at h
  rw [h, Perm.mul_apply, Perm.mul_apply]

end Stars

section Hom

theorem range_eq : Stars.starHom.range = G24 := Stars.range_starHom

theorem mem_cent_iff' {G : Type*} [Group G] {x y : G} :
    x ∈ centralizer ({y} : Set G) ↔ x * y = y * x := Subgroup.mem_centralizer_singleton_iff

theorem coe_comm' {G : Type*} [Group G] {K : Subgroup G} {a b : K} (h : a * b = b * a) :
    (a : G) * b = b * a := congrArg Subtype.val h

theorem centJ_iff {x y : J} : x ∈ centralizer ({y} : Set J) ↔ y * x = x * y :=
  ⟨fun h => mem_centralizer_iff.1 h y (Set.mem_singleton _), fun h =>
    mem_centralizer_iff.2 fun g hg => by rw [Set.mem_singleton_iff.1 hg]; exact h⟩

noncomputable abbrev xiBar : Perm (Fin 24) := Stars.starHom ⟨fiveElt, fiveElt_mem_Hj⟩

theorem fiveElt_eq : fiveElt = xJ 0 * xJ 1 * (xJ 2)⁻¹ * (xJ 0 * xJ 1 * (xJ 2)⁻¹) := by
  simp [fiveElt, wordProd, fiveWord, mul_assoc]

theorem xiBar_eq : xiBar = tauOf 0 * tauOf 1 * (tauOf 2)⁻¹ * (tauOf 0 * tauOf 1 * (tauOf 2)⁻¹) := by
  have e : (⟨fiveElt, fiveElt_mem_Hj⟩ : Hj) =
      ⟨xJ 0, xJ_mem (by norm_num)⟩ * ⟨xJ 1, xJ_mem (by norm_num)⟩ * ⟨xJ 2, xJ_mem (by norm_num)⟩⁻¹ *
        (⟨xJ 0, xJ_mem (by norm_num)⟩ * ⟨xJ 1, xJ_mem (by norm_num)⟩ *
          ⟨xJ 2, xJ_mem (by norm_num)⟩⁻¹) :=
    Subtype.ext fiveElt_eq
  rw [xiBar, e]
  simp only [map_mul, map_inv]
  rw [Stars.starHom_xJ (by norm_num), Stars.starHom_xJ (by norm_num), Stars.starHom_xJ (by norm_num)]

theorem pf_xiBar : ∀ i < 24, pf xiBar i = getN 0 XI i := by
  intro i hi
  have h := (sqOK_spec gold_sq i hi).2
  rw [pf_fin' xiBar hi, xiBar_eq, Perm.mul_apply, y_val, y_val]
  exact h.symm

theorem xiBar_mem : xiBar ∈ G24 := by
  rw [← range_eq]
  exact ⟨_, rfl⟩

theorem card_cent_xiBar :
    Nat.card ↥(G24 ⊓ Subgroup.centralizer ({xiBar} : Set (Perm (Fin 24)))) ≤ 60 :=
  card_cent_le G24 (B := GB) (P := GP) (z := XI) (crd := CRD) (Fl := FL) (Tl := TL) (n := 12)
    rfl rfl gold_inv gen_G24 xiBar_mem pf_xiBar gold_fix gold_oct0
    (Nat.eq_of_beq_eq_true gold_pc) gold_oct gold_crd (Nat.eq_of_beq_eq_true gold_cand) rfl rfl
    gold_dist (by decide)

end Hom

end CertificateChecks.KernelJ4Count.Five

end
