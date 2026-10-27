module

public import Certificates.Kernel.Fi22.Model
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.C_Sel
public import CFSG.Certificates.Kernel.Fi22.Bound.Data.Cov
public import Mathlib.GroupTheory.Subgroup.Center
import Certificates.Kernel.Fi22.Facts
import CFSG.Certificates.Kernel.Fi22.Bound2.Checks.C_H_0
import CFSG.Certificates.Kernel.Fi22.Bound2.Checks.C_L
import CFSG.Certificates.Kernel.Fi22.Bound2.Checks.M
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelFi22

open CFSG.KC CFSG.KC.LceS CFSG.KC.HOrb CFSG.KC.Fi22K CFSG.KC.Fi22B.Cov CFSG.Certificates
  CFSG.Certificates.LCE CFSG.Certificates.Fi22Kill CertificateChecks.KernelCo2

theorem coneOk_intro {blk WT RT ST LB LETs : Nat → Nat}
    {INV INV8 L nC nf m Hs K S0 S1 T0 T1 : Nat} {Cs : List Nat}
    (h1 : wordsOK WT RT ST INV INV8 m Hs = true) (h2 : invOK INV INV8 L = true)
    (h3 : Nat.ble nC (nat_lit 1048576) = true) (h4 : Nat.blt nf (nat_lit 4294967296) = true)
    (h5 : Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)) = true) (h6 : Nat.beq S1 (mkS nf nC) = true)
    (h7 : Nat.beq T0 (nat_lit 1) = true) (h8 : Nat.beq T1 (Nat.succ nf) = true)
    (h9 : CFSG.KC.Fi22K.hintsLt WT m K Hs = true)
    (h10 : Nat.beq (CFSG.KC.LceSR.runIds WT m Cs (nat_lit 1)) (nat_lit 1) = true)
    (h11 : Nat.beq (runFacts blk WT INV nC L Cs S0) S1 = true)
    (h12 : Nat.beq (CFSG.KC.Fi22K.runLab WT LB LETs Hs Cs T0) T1 = true) :
    coneOk blk WT RT ST LB LETs INV INV8 L nC nf m Hs K S0 S1 T0 T1 Cs = true := by
  unfold coneOk
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  rfl

noncomputable abbrev evg (k : ℕ) : PG := if _h : k < 6 then ev k else 1

theorem bval2 {G : Type*} [Group G] (gen : ℕ → G) {e c : ℕ} (hW : wWord e = c + 256 * c) (hl : wLen e = 2)
    (hc : c < 256) : bval gen (wWord e) (wLen e) = letV gen c * letV gen c := by
  have h2 : (c + 256 * c) / 256 = c := by omega
  rw [hl, hW, bval_succ, bval_succ, h2, show bval gen (c / 256) 0 = 1 from rfl, mul_one, wLet_eq, wLet_eq]
  simp only [Nat.mul_zero, pow_zero, Nat.div_one]
  rw [show (c + 256 * c) % 256 = c by omega, Nat.mod_eq_of_lt hc]

theorem ev_sq {g : ℕ} (hg : g < 6) : ev g * ev g = 1 := by
  have key : ∀ (r c : ℕ), r < 27 → wWord (CFSG.KD.Fi22KM.XRs r) = c + 256 * c →
      wLen (CFSG.KD.Fi22KM.XRs r) = 2 → c = 2 * g → ev g * ev g = 1 := by
    intro r c hr hW hl hc
    have h := pi_rel r hr
    rw [bval2 _ hW hl (by omega), hc] at h
    have e2 : letV (fun k => bval tg (wWord (eAB (k + 1))) (wLen (eAB (k + 1)))) (2 * g) = ev g := by
      unfold letV
      simp only [show ¬ 2 * g = 255 by omega, show 2 * g % 2 = 0 by omega, show 2 * g / 2 = g by omega,
        ↓reduceIte, eAB_ev, hg, dite_true]
    rwa [e2] at h
  interval_cases g
  · exact key 0 0 (by norm_num) (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) rfl
  · exact key 1 2 (by norm_num) (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) rfl
  · exact key 2 4 (by norm_num) (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) rfl
  · exact key 3 6 (by norm_num) (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) rfl
  · exact key 20 8 (by norm_num) (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) rfl
  · exact key 13 10 (by norm_num) (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) rfl

theorem letV_evg {c : ℕ} (hc : c < 12) : ev (c / 2) * letV evg c = 1 := by
  have h6 : c / 2 < 6 := by omega
  unfold letV
  simp only [show ¬ c = 255 by omega, ↓reduceIte, evg, h6, dite_true]
  split_ifs
  · exact ev_sq h6
  · exact mul_inv_cancel _

theorem byte_succ (W k : ℕ) : byte W (k + 1) = byte (W / 256) k := by
  change wLet W (k + 1) = wLet (W / 256) k
  rw [wLet_eq, wLet_eq, Nat.div_div_eq_div_mul, Nat.mul_add, pow_add]
  ring_nf

@[expose] noncomputable def revW (Wd n k : ℕ) : PG :=
  ((List.range k).map fun q => ev (Nat.shiftRight (byte Wd (n - 1 - q)) 1)).prod

theorem revE_eq (W n k : ℕ) : revE W n k = revW (wWord W) n k := rfl

theorem revW_succ (Wd n k : ℕ) : revW Wd n (k + 1) = revW Wd n k * ev (Nat.shiftRight (byte Wd (n - 1 - k)) 1) := by
  simp [revW, List.range_succ]

theorem revW_mul : ∀ (n Wd : ℕ), (∀ q < n, wLet Wd q < 12) → revW Wd n n * bval evg Wd n = 1 := by
  intro n
  induction n with
  | zero => intro W _; simp [revW, bval]
  | succ n ih =>
    intro W hW
    have e1 : revW W (n + 1) n = revW (W / 256) n n := by
      unfold revW
      congr 1
      apply List.map_congr_left
      intro q hq
      have hq' := List.mem_range.mp hq
      rw [show n + 1 - 1 - q = (n - 1 - q) + 1 by omega, byte_succ]
    have e2 : Nat.shiftRight (byte W (n + 1 - 1 - n)) 1 = wLet W 0 / 2 := by
      rw [show n + 1 - 1 - n = 0 by omega]
      exact Nat.shiftRight_eq_div_pow _ 1
    rw [revW_succ, e1, e2, bval_succ, mul_assoc, ← mul_assoc (ev _), letV_evg (hW 0 (by omega)), one_mul]
    apply ih
    intro q hq
    have := hW (q + 1) (by omega)
    rwa [show wLet W (q + 1) = wLet (W / 256) q from byte_succ W q] at this

abbrev LG : Type := XT × Multiplicative (Fin 7 → ℤ)

@[expose] noncomputable def cz (q : Fin 7) : Subgroup.center PG :=
  ⟨revE (CFSG.KD.Fi22KM.WJs q) (wLen (CFSG.KD.Fi22KM.WJs q)) (wLen (CFSG.KD.Fi22KM.WJs q)) *
    bval tg (wWord (CFSG.KC.Fi22B.sub q)) (wLen (CFSG.KC.Fi22B.sub q)), fix_center q q.isLt⟩

noncomputable instance centerComm : CommGroup (Subgroup.center PG) :=
  { (inferInstance : Group (Subgroup.center PG)) with
    mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a) }

@[expose] noncomputable def czPow : Multiplicative (Fin 7 → ℤ) →* Subgroup.center PG where
  toFun n := ∏ q, cz q ^ (Multiplicative.toAdd n q)
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

@[expose] noncomputable def piL : LG →* PG where
  toFun p := piX p.1 * (czPow p.2 : PG)
  map_one' := by simp
  map_mul' a b := by
    have hc : (czPow a.2 : PG) * piX b.1 = piX b.1 * (czPow a.2 : PG) :=
      (Subgroup.mem_center_iff.mp (czPow a.2).2 (piX b.1)).symm
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Subgroup.coe_mul]
    rw [show piX a.1 * (czPow a.2 : PG) * (piX b.1 * (czPow b.2 : PG)) =
      piX a.1 * ((czPow a.2 : PG) * piX b.1) * (czPow b.2 : PG) by group, hc]
    group

@[expose] noncomputable def psiL : LG →* GL4 := psiX.comp (MonoidHom.fst _ _)
@[expose] noncomputable def parL : LG →* Multiplicative (ZMod 2) := parX.comp (MonoidHom.fst _ _)
@[expose] noncomputable def nvL : LG →* Multiplicative (Fin 7 → ℤ) := MonoidHom.snd _ _

theorem czPow_single (q : Fin 7) : czPow (Multiplicative.ofAdd (Pi.single q 1)) = cz q := by
  simp only [czPow, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  rw [Finset.prod_eq_single q]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp

theorem czPow_zero : czPow 1 = 1 := map_one _

noncomputable abbrev xw (j : ℕ) : XT :=
  bval gX (wWord (CFSG.KD.Fi22KM.WJs j)) (wLen (CFSG.KD.Fi22KM.WJs j))

theorem piX_xw (j : ℕ) : piX (xw j) = bval evg (wWord (CFSG.KD.Fi22KM.WJs j)) (wLen (CFSG.KD.Fi22KM.WJs j)) := by
  rw [bval_map]
  apply bval_congr
  intro k
  by_cases hk : k < 6
  · rw [piX_gX hk]
    simp [evg, hk]
  · rw [show gX k = 1 by simp [gX, pgen, hk], map_one]
    simp [evg, hk]

theorem wj_ok : ∀ j < 7, HO.entOK (CFSG.KD.Fi22KM.WJs j) (nat_lit 12) (nat_lit 1023) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem piL_wj {j : ℕ} (hj : j < 7) :
    piL (xw j, Multiplicative.ofAdd (Pi.single ⟨j, hj⟩ 1)) =
      bval tg (wWord (CFSG.KC.Fi22B.sub j)) (wLen (CFSG.KC.Fi22B.sub j)) := by
  have hr := revW_mul (wLen (CFSG.KD.Fi22KM.WJs j)) (wWord (CFSG.KD.Fi22KM.WJs j))
    (fun q _ => letters_all (wj_ok j hj) (by norm_num) q)
  change piX (xw j) * (czPow (Multiplicative.ofAdd (Pi.single ⟨j, hj⟩ 1)) : PG) = _
  rw [czPow_single]
  change piX (xw j) * (revE (CFSG.KD.Fi22KM.WJs j) (wLen (CFSG.KD.Fi22KM.WJs j)) (wLen (CFSG.KD.Fi22KM.WJs j)) *
    bval tg (wWord (CFSG.KC.Fi22B.sub j)) (wLen (CFSG.KC.Fi22B.sub j))) = _
  rw [revE_eq, piX_xw, ← mul_assoc, mul_eq_one_comm.mp hr, one_mul]

end CertificateChecks.KernelFi22

end
