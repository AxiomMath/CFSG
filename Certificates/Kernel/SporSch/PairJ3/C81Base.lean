module

public import Certificates.Kernel.SporSch.PairJ3.C81Fns
public import Certificates.Kernel.SporSch.PairJ3.C81Group
public import Certificates.Kernel.SporSch.PairJ3.C81BindA
public import Certificates.Kernel.SporSch.PairJ3.C81BindB
public import Certificates.Kernel.SporSch.PairJ3.C81Misc
public import Certificates.Kernel.SporSch.PairJ3.Check2238
public import Certificates.Kernel.Sporadic.OddCore.J3Cent
public import CFSG.Certificates.Kernel.SporSch.NfInvSound
public import CFSG.Certificates.Kernel.Spor.JoinProof
public import CFSG.Sporadic.SmallOddCore.J3CentFacts
import CFSG.Certificates.Kernel.HeFixKFix
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic
public import CFSG.Certificates.Kernel.Misc.HexFlatSound

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 100000

#kss_b2all CertificateChecks.KernelSporSch.PJ3C81 CertificateChecks.KernelSporSch.PJ3C81.bindB 20 6
#kss_b2all CertificateChecks.KernelSporSch.PJ3C81 CertificateChecks.KernelSporSch.PJ3C81.sB 2 2

namespace CertificateChecks.KernelSporSch.PJ3C81

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier CFSG.KS.Prim
open CFSG.Sporadic.Schreier.PairNative CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.PJ3Count CFSG.Sporadic.SmallOddCore Subgroup

@[expose] noncomputable def Tb (k : Nat) : Equiv.Perm (Fin 6156) := tp 6156 (j3CentTbl k)

@[expose] noncomputable def U : Equiv.Perm (Fin 6156) := Tb 0

theorem P_eq : allN 31 (fun k => bAnd(Nat.beq (C81T.P k) (KernelSpor.J3CentP k),
    Nat.beq (C81T.I k) (KernelSpor.J3CentI k))) = true := by
  quickRfl

theorem repF_of_rep {P : Nat} {g : Equiv.Perm (Fin 6156)}
    (h : CFSG.Monster.B.Co2.Rep 6156 (unpack 6156 13 P) g) : RepF 6156 (pg 13 (mask 13) P) g := by
  intro x hx
  rw [← CFSG.KC.HeFixK.unpack_getElem! hx]
  exact h ⟨x, hx⟩

theorem rep_T {k : Nat} (hk : k < 31) : RepF 6156 (cP k) (Tb k) ∧ RepF 6156 (cI k) (Tb k)⁻¹ := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec P_eq k hk)
  have hr := CFSG.Monster.B.Co2.rep_permOfArr (invEqK_sound (KernelSpor.OddCore.j3_perm hk)).2
  have ht : CFSG.Sporadic.SmallOddCore.Native.natArr (j3CentTbl k) =
      unpack 6156 13 (KernelSpor.J3CentP k) := by
    have h := CFSG.KS.Join.hexT_join_proved (d := 4) (n₀ := 513) (w := 13) (c := 12) (N := 31)
      KernelSpor.J3CentT.all KernelSpor.OddCore.j3_join (by norm_num) (by norm_num) (by norm_num) k hk
    rw [← KernelSpor.J3CentT.eq] at h
    exact h
  have e : Tb k = permOfArr 6156 (unpack 6156 13 (KernelSpor.J3CentP k)) := by
    change permOfArr 6156 (CFSG.Sporadic.SmallOddCore.Native.natArr (j3CentTbl k)) = _
    rw [ht]
  refine ⟨?_, ?_⟩
  · have := repF_of_rep hr.1
    unfold cP
    rw [Nat.eq_of_beq_eq_true h1, e]
    exact this
  · have := repF_of_rep hr.2
    unfold cI
    rw [Nat.eq_of_beq_eq_true h2, e]
    exact this

theorem rep0 : RepF 6156 (cP 0) U := (rep_T (by norm_num)).1

theorem nfp_rep {F : Nat} (hF : nfValidK 4 PJ3.LR F = true) : RepF 6156 (nfp F) (E F) := E_rep hF

theorem nfi_rep {F : Nat} (hF : nfValidK 4 PJ3.LR F = true) : RepF 6156 (nfi F) (E F)⁻¹ :=
  nfInv4_sound tc hF

theorem bNot {a b : Nat} (h : bIf(Nat.beq a b, false, true) = true) : a ≠ b := fun e => by
  rw [e, Nat.beq_refl] at h
  exact Bool.noConfusion h

theorem ptF {x : Nat} (hx : x < 6156) : cP 0 (cP 0 x) = x ∧ cP 21 (cP 21 x) = x ∧ cP 0 x ≠ x ∧
    cP 21 x ≠ x ∧ stAt x = true := by
  have h := allN_spec pt_all x hx
  unfold ptAt at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, bNot h3, bNot h4, h5⟩

theorem smF : allN 20 (fun g => nfValidK 4 PJ3.LR (bNF g)) = true ∧
    List.rec (motive := fun _ => Bool) true
      (fun F _ ih => bAnd(nfValidK 4 PJ3.LR F, bAnd(Nat.beq (nfp F 0) 0, ih))) stNFs = true ∧
    Nat.beq (PJ3Cn.tP 107) 107 = true ∧ ordPL bs (cP 9) 2 = true ∧
    allN 5 (fun j => commR 0 (cP (Nat.add 10 j))) = true ∧
    allN 3 (fun j => commR 1 (cP (Nat.add 22 j))) = true ∧
    Nat.beq (w1 1) 1 = true ∧ bIf(Nat.beq (w1 3) 3, false, true) = true ∧
    Nat.beq (w2 1) 1 = true ∧ bIf(Nat.beq (w2 0) 0, false, true) = true ∧ oddB = true := by
  have h := small
  unfold smallB at h
  simpa only [bAnd_iff] using h

theorem bnd {g : Nat} (hg : g < 20) : RepF 6156 (bMap g) (E (bNF g)) := by
  have hv : nfValidK 4 PJ3.LR (bNF g) = true := allN_spec smF.1 g hg
  intro x hx
  have h0 : allBlk (Nat.mul (x / 1026) 1026) (fun y => Nat.beq (bMap g y) (nfp (bNF g) y)) 1026 =
      true := bindB_all g hg (x / 1026) (by omega : x / 1026 < 6)
  have h : Nat.beq (bMap g (Nat.add (Nat.mul (x / 1026) 1026) (x % 1026)))
      (nfp (bNF g) (Nat.add (Nat.mul (x / 1026) 1026) (x % 1026))) = true :=
    allBlk_spec h0 (x % 1026) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (x / 1026) 1026) (x % 1026) = x := by
    change x / 1026 * 1026 + x % 1026 = x
    omega
  rw [e] at h
  rw [Nat.eq_of_beq_eq_true h]
  exact nfp_rep hv x hx

theorem bvalid {g : Nat} (hg : g < 20) : nfValidK 4 PJ3.LR (bNF g) = true := allN_spec smF.1 g hg

section J3


theorem bmem {g : Nat} (hg : g < 20) : E (bNF g) ∈ P3 := E_mem (bvalid hg)

theorem mem_of_bnd {g : Nat} (hg : g < 20) {f : Nat → Nat} {x : Equiv.Perm (Fin 6156)}
    (hf : RepF 6156 f x) (e : ∀ y, bMap g y = f y) : x ∈ P3 := by
  have h := bnd hg
  have h' : RepF 6156 f (E (bNF g)) := fun y hy => by rw [← e y]; exact h y hy
  rw [hf.unique h']
  exact bmem hg

theorem U2 : U * U = 1 := by
  refine (rep0.comp rep0).unique ?_
  intro x hx
  exact (ptF hx).1

theorem Uinv : U⁻¹ = U := inv_eq_of_mul_eq_one_right U2

theorem Usq : U ^ 2 = 1 := by rw [sq, U2]

theorem T21_2 : Tb 21 * Tb 21 = 1 := by
  refine ((rep_T (k := 21) (by norm_num)).1.comp (rep_T (k := 21) (by norm_num)).1).unique ?_
  intro x hx
  exact (ptF hx).2.1

theorem not_mem_of_fpf {g : Equiv.Perm (Fin 6156)} (h2 : g * g = 1) (h1 : g ≠ 1)
    (hfp : ∀ x : Fin 6156, g x ≠ x) : g ∉ P3 := by
  intro hg
  have ho : orderOf g = 2 := orderOf_eq_prime (by rw [sq, h2]) h1
  obtain ⟨c, hc⟩ := isConj_iff.1 (invol_conj (x := ⟨g, hg⟩) (by rw [Subgroup.orderOf_mk]; exact ho))
  have he : (c : Equiv.Perm (Fin 6156)) * tE * (c : Equiv.Perm (Fin 6156))⁻¹ = g :=
    congrArg Subtype.val hc
  have hfix : tE ⟨107, by norm_num⟩ = ⟨107, by norm_num⟩ :=
    Fin.ext ((tRep 107 (by norm_num)).symm.trans (Nat.eq_of_beq_eq_true smF.2.2.1))
  apply hfp ((c : Equiv.Perm (Fin 6156)) ⟨107, by norm_num⟩)
  have hci : (c : Equiv.Perm (Fin 6156))⁻¹ ((c : Equiv.Perm (Fin 6156)) ⟨107, by norm_num⟩) =
      ⟨107, by norm_num⟩ := by
    rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
  rw [← he, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hci, hfix]

theorem U_ne : U ≠ 1 := by
  intro h
  have := (ptF (x := 0) (by norm_num)).2.2.1
  rw [rep0 0 (by norm_num), h] at this
  exact this rfl

theorem fpf_of {k : Nat} (hk : k < 31) (h : ∀ x < 6156, cP k x ≠ x) :
    ∀ x : Fin 6156, Tb k x ≠ x := fun ⟨v, hv⟩ e =>
  h v hv (((rep_T hk).1 v hv).trans (congrArg Fin.val e))

theorem fpfU : ∀ x : Fin 6156, U x ≠ x := fun ⟨v, hv⟩ e =>
  (ptF hv).2.2.1 ((rep0 v hv).trans (congrArg Fin.val e))

theorem U_not : U ∉ P3 := not_mem_of_fpf U2 U_ne fpfU

theorem T21_ne : Tb 21 ≠ 1 := by
  intro h
  have h0 := (ptF (x := 0) (by norm_num)).2.2.2.1
  have h1 := (rep_T (k := 21) (by norm_num)).1 0 (by norm_num)
  rw [h1, h] at h0
  exact h0 rfl

theorem T21_not : Tb 21 ∉ P3 :=
  not_mem_of_fpf T21_2 T21_ne (fpf_of (k := 21) (by norm_num) fun x hx => (ptF hx).2.2.2.1)

theorem gen_rep {k : Nat} (hk : k < 2) : RepF 6156 (sP k) (j3Gen k) := by
  have h := (PJ3Check.rep_g k (by omega)).1
  have e : j3Gen k = PJ3Check.g k := by
    unfold j3Gen j3StrongPerm PJ3Check.g
    rw [PJ3Check.arr_eq k (by omega)]
  rw [e]
  exact repF_of_rep h

theorem P_eq3 : j3P = P3 := j3P_eq_original

theorem conj_gen {k : Nat} (hk : k < 2) : U * j3Gen k * U⁻¹ ∈ P3 := by
  rw [Uinv]
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact mem_of_bnd (g := 10) (by norm_num) ((rep0.comp (gen_rep (by norm_num))).comp rep0)
      fun _ => rfl
  · exact mem_of_bnd (g := 11) (by norm_num) ((rep0.comp (gen_rep (by norm_num))).comp rep0)
      fun _ => rfl

theorem Un : ∀ p ∈ j3P, U * p * U⁻¹ ∈ j3P := by
  have hle : j3P ≤ j3P.comap (MulAut.conj U).toMonoidHom := by
    conv_lhs => rw [j3P]
    rw [closure_le]
    rintro x hx
    rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, P_eq3]
    rcases hx with rfl | rfl
    · exact conj_gen (by norm_num)
    · exact conj_gen (by norm_num)
  intro p hp
  have := hle hp
  rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem map_eq : j3P.map (MulAut.conj U).toMonoidHom = j3P := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨p, hp, rfl⟩
    exact Un p hp
  · rw [Subgroup.card_map_of_injective (MulAut.conj U).injective]

theorem R_mem (x : Equiv.Perm (Fin 6156)) : x ∈ j3P ⊔ zpowers U ↔ x ∈ j3P ∨ x * U ∈ j3P :=
  mem_sup_zpowers_iff Usq Un

theorem U_notP : U ∉ j3P := by
  rw [P_eq3]
  exact U_not

theorem card_R : Nat.card ↥(j3P ⊔ zpowers U) = 2 * 50232960 := by
  rw [card_sup_zpowers Usq Un U_notP, card_j3P]

theorem uP_rep {b : Nat} (hb : b < 2) : RepF 6156 (uP b) (U ^ b) := by
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
  · exact RepF.one
  · rw [pow_one]
    exact rep0

theorem Upow2 {b : Nat} (hb : b < 2) : U ^ b * U ^ b = 1 := by
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
  · simp
  · rw [pow_one, U2]

theorem conjU_mem {p : Equiv.Perm (Fin 6156)} (hp : p ∈ P3) : U * p * U ∈ P3 := by
  have := Un p (by rw [P_eq3]; exact hp)
  rwa [Uinv, P_eq3] at this

end J3

end CertificateChecks.KernelSporSch.PJ3C81

end
