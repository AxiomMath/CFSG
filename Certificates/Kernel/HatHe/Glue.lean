module

public import Certificates.Kernel.HatHe.Checks
public import CFSG.Certificates.Kernel.HatHeKSound
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213HatHGroups
public import Certificates.Kernel.SporSch.HeT.B2114
public import CFSG.Sporadic.HeldB.BaseTests

public section

namespace CertificateChecks.KernelHatHe

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.HatHe
open CFSG.Monster.B.Co2 CFSG.Sporadic.HeldB CFSG.KS.SporSch
open CFSG.Quasithin.H13.Ch4
open CertificateChecks.KernelSporSch.HeB14

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem with9_eq (F : Nat → Nat) (f : (Nat → Nat) → Bool) :
    with9 F f = f (sel9 (F 0) (F 1) (F 2) (F 3) (F 4) (F 5) (F 6) (F 7) (F 8)) := by
  simp only [with9, strictB_eq]

theorem sel9_eq (F : Nat → Nat) {j : Nat} (hj : j < 9) :
    sel9 (F 0) (F 1) (F 2) (F 3) (F 4) (F 5) (F 6) (F 7) (F 8) j = F j := by
  interval_cases j <;> rfl

theorem repF_of_rep {P : Nat} {g : Equiv.Perm (Fin 8330)} (h : Rep 8330 (unpack 8330 14 P) g) :
    RepF 8330 (ap P) g := by
  intro x hx
  have h1 := h ⟨x, hx⟩
  rw [unpack, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn] at h1
  exact h1

theorem rep_C0 {j : Nat}
    (hj : j < 9) : Rep 8330 (unpack 8330 14 (C0 j)) (heInnerCP0 j) :=
  (C0_word hj).1 ▸ rep_heInnerC0 hj

theorem rep_C1 {j : Nat}
    (hj : j < 9) : Rep 8330 (unpack 8330 14 (C1 j)) (heInnerCP1 j) :=
  (C1_word hj).1 ▸ rep_heInnerC1 hj

theorem repF_C0 :
    ∀ j < 9, RepF 8330 (ap (sel9 (C0 0) (C0 1) (C0 2) (C0 3) (C0 4) (C0 5) (C0 6) (C0 7) (C0 8) j))
      (heInnerCP0 j) := fun j hj => by
  rw [sel9_eq C0 hj]
  exact repF_of_rep (rep_C0 hj)

theorem repF_C0I :
    ∀ j < 9, RepF 8330
      (ap (sel9 (C0I 0) (C0I 1) (C0I 2) (C0I 3) (C0I 4) (C0I 5) (C0I 6) (C0I 7) (C0I 8) j))
      (heInnerCP0 j)⁻¹ := fun j hj => by
  rw [sel9_eq C0I hj]
  exact repF_of_rep (rep_inv_of_isInvA (rep_C0 hj) (invEqK_sound (c0_parts hj).1).2)

theorem repF_C1 :
    ∀ j < 9, RepF 8330 (ap (sel9 (C1 0) (C1 1) (C1 2) (C1 3) (C1 4) (C1 5) (C1 6) (C1 7) (C1 8) j))
      (heInnerCP1 j) := fun j hj => by
  rw [sel9_eq C1 hj]
  exact repF_of_rep (rep_C1 hj)

theorem repF_C1I :
    ∀ j < 9, RepF 8330
      (ap (sel9 (C1I 0) (C1I 1) (C1I 2) (C1I 3) (C1I 4) (C1I 5) (C1I 6) (C1I 7) (C1I 8) j))
      (heInnerCP1 j)⁻¹ := fun j hj => by
  rw [sel9_eq C1I hj]
  exact repF_of_rep (rep_inv_of_isInvA (rep_C1 hj) (invEqK_sound (c1_parts hj).1).2)

theorem gens0_eq : (List.range 3).map (fun j => ((W0 j).map heInnerCP0).prod) = HatH.heP0Gens :=
  rfl

theorem gens1_eq : (List.range 4).map (fun j => ((W1 j).map heInnerCP1).prod) = HatH.heP1Gens :=
  rfl

theorem d0_eq : (dW0.map heInnerCP0).prod = HatH.heD0 := rfl

theorem d1_eq : (dW1.map heInnerCP1).prod = HatH.heD1 := rfl

theorem cl0_len : CFSG.KD.HatHe.CL0.length ≤ 63 := by decide

theorem cl1_len : CFSG.KD.HatHe.CL1.length ≤ 63 := by decide

theorem facts0 :
    Nat.card HatH.heP0 = 2 ^ 9 ∧
      ∀ A : Subgroup (Equiv.Perm (Fin 8330)), A ≤ HatH.heP0 →
        A ≤ HatH.heP0.map (MulAut.conj HatH.heD0).toMonoidHom →
        (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A ≤ 63 := by
  have h := k7167p0
  simp only [with9_eq] at h
  have key := grpK_sound (K := heP) (c := heInnerCP0) (W := W0) (nG := 3) (N := 512)
    (dW := dW0) (dR := dR0) (E := E0) (Z := Z0) (PA := PA0) (SG := SG0) (CT := CT0) (MB := MB0)
    (CL := CFSG.KD.HatHe.CL0) (f := 11) heP_baseFaithful (fun j _ => heInnerCP0_mem j) repF_C0
    repF_C0I (by decide) (by decide) rfl (by norm_num) h
  rw [gens0_eq, d0_eq] at key
  obtain ⟨hc, hcov⟩ := key
  exact ⟨hc.trans (by norm_num), fun A h1 h2 h3 => (hcov A h1 h2 h3).trans cl0_len⟩

theorem facts1 :
    Nat.card HatH.heP1 = 2 ^ 10 ∧
      ∀ A : Subgroup (Equiv.Perm (Fin 8330)), A ≤ HatH.heP1 →
        A ≤ HatH.heP1.map (MulAut.conj HatH.heD1).toMonoidHom →
        (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A ≤ 63 := by
  have h := k7167p1
  simp only [with9_eq] at h
  have key := grpK_sound (K := heP) (c := heInnerCP1) (W := W1) (nG := 4) (N := 1024)
    (dW := dW1) (dR := dR1) (E := E1) (Z := Z1) (PA := PA1) (SG := SG1) (CT := CT1) (MB := MB1)
    (CL := CFSG.KD.HatHe.CL1) (f := 9) heP_baseFaithful (fun j _ => heInnerCP1_mem j) repF_C1
    repF_C1I (by decide) (by decide) rfl (by norm_num) h
  rw [gens1_eq, d1_eq] at key
  obtain ⟨hc, hcov⟩ := key
  exact ⟨hc.trans (by norm_num), fun A h1 h2 h3 => (hcov A h1 h2 h3).trans cl1_len⟩

end CertificateChecks.KernelHatHe

end
