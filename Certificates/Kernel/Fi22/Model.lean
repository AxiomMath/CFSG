module

public import Certificates.Kernel.Fi22.Chain
public import Certificates.Kernel.Fi22.Pair
public import CFSG.Certificates.Kernel.Fi22KillSound
import CFSG.Certificates.Kernel.Fi22.Bound2.Checks.M
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelFi22

open CFSG.KC CFSG.KC.LceS CFSG.KC.HOrb CFSG.KC.Fi22K CFSG.KC.Fi22B.Cov CFSG.Certificates
  CFSG.Certificates.LCE CFSG.Certificates.Fi22Kill CertificateChecks.KernelCo2

abbrev GL4 : Type := (Matrix (Fin 27) (Fin 27) F4)ˣ

theorem dec4_eq_one {X : ℕ}
    (hlo : ∀ i j : Fin 27, Nat.land (Nat.shiftRight X (27 * i.val + j.val)) 1 = if i = j then 1 else 0)
    (hhi : ∀ i j : Fin 27, Nat.land (Nat.shiftRight X (729 + 27 * i.val + j.val)) 1 = 0) : dec4 X = 1 := by
  ext i j
  simp only [dec4, bit4, hlo, hhi, Matrix.one_apply]
  split_ifs <;> simp

theorem dec4_one : dec4 one4 = 1 := dec4_eq_one (by decide +kernel) (by decide +kernel)

theorem wf4_one : wf4 one4 = true := by quickRfl

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem evalE_dec (FS : ℕ → ℕ) (w : ℕ)
    (hFS : ∀ q < wLen w, wf4 (FS (Nat.shiftRight (byte (wWord w) q) 1)) = true) :
    wf4 (evalE FS w) = true ∧ dec4 (evalE FS w) =
      ((List.range (wLen w)).map fun q => dec4 (FS (Nat.shiftRight (byte (wWord w) q) 1))).prod := by
  have key : ∀ n ≤ wLen w,
      wf4 (Nat.rec (motive := fun _ => Nat) one4
        (fun q acc => CFSG.KC.Loop.strictN acc (fun x => mul4 x (FS (Nat.shiftRight (byte (wWord w) q) 1))))
        n) = true ∧
      dec4 (Nat.rec (motive := fun _ => Nat) one4
        (fun q acc => CFSG.KC.Loop.strictN acc (fun x => mul4 x (FS (Nat.shiftRight (byte (wWord w) q) 1))))
        n) = ((List.range n).map fun q => dec4 (FS (Nat.shiftRight (byte (wWord w) q) 1))).prod := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨wf4_one, dec4_one⟩
    | succ n ih =>
      intro hn
      obtain ⟨h1, h2⟩ := ih (by omega)
      change wf4 (CFSG.KC.Loop.strictN _ _) = true ∧ dec4 (CFSG.KC.Loop.strictN _ _) = _
      rw [strictN_eq']
      obtain ⟨m1, m2⟩ := mul4_sound h1 (hFS n (by omega))
      refine ⟨m1, ?_⟩
      rw [m2, h2, List.range_succ, List.map_append, List.prod_append]
      simp
  exact key _ le_rfl

@[expose] noncomputable def unit4 (X : ℕ) (hw : wf4 X = true) (h : Nat.beq (mul4 X X) one4 = true) : GL4 :=
  have hm : dec4 X * dec4 X = 1 := by
    rw [← (mul4_sound hw hw).2, Nat.eq_of_beq_eq_true h, dec4_one]
  ⟨dec4 X, dec4 X, hm, hm⟩

theorem fi_ok : ∀ t : Fin 6, wf4 (CFSG.KD.Fi22KM.FIs t) = true ∧
    Nat.beq (mul4 (CFSG.KD.Fi22KM.FIs t) (CFSG.KD.Fi22KM.FIs t)) one4 = true := by
  intro t
  fin_cases t <;> exact ⟨by quickRfl, by quickRfl⟩

@[expose] noncomputable def uG (t : Fin 6) : GL4 := unit4 (CFSG.KD.Fi22KM.FIs t) (fi_ok t).1 (fi_ok t).2

theorem uG_inv (t : Fin 6) : (uG t)⁻¹ = uG t := Units.ext rfl

theorem uG_val (t : Fin 6) : ((uG t : GL4) : Matrix (Fin 27) (Fin 27) F4) = dec4 (CFSG.KD.Fi22KM.FIs t) := rfl

theorem lift_gF {G : Type*} [Group G] (f : Fin 6 → G) (k : ℕ) :
    FreeGroup.lift f (gF k) = if h : k < 6 then f ⟨k, h⟩ else 1 := by
  unfold gF
  split_ifs <;> simp [FreeGroup.lift_apply_of]

theorem psi_rel {r : ℕ} (hr : r < 27) :
    bval (fun k => if h : k < 6 then uG ⟨k, h⟩ else 1) (wWord (CFSG.KD.Fi22KM.XRs r))
      (wLen (CFSG.KD.Fi22KM.XRs r)) = 1 := by
  have hlet : ∀ q < wLen (CFSG.KD.Fi22KM.XRs r), wLet (wWord (CFSG.KD.Fi22KM.XRs r)) q < 12 :=
    fun q _ => letters_all (xr_ok r hr) (by norm_num) q
  have hhom : Nat.beq (evalE CFSG.KD.Fi22KM.FIs (CFSG.KD.Fi22KM.XRs r)) one4 = true := by
    interval_cases r
    exacts [CFSG.KD.Fi22KM.hom0, CFSG.KD.Fi22KM.hom1, CFSG.KD.Fi22KM.hom2, CFSG.KD.Fi22KM.hom3,
      CFSG.KD.Fi22KM.hom4, CFSG.KD.Fi22KM.hom5, CFSG.KD.Fi22KM.hom6, CFSG.KD.Fi22KM.hom7,
      CFSG.KD.Fi22KM.hom8, CFSG.KD.Fi22KM.hom9, CFSG.KD.Fi22KM.hom10, CFSG.KD.Fi22KM.hom11,
      CFSG.KD.Fi22KM.hom12, CFSG.KD.Fi22KM.hom13, CFSG.KD.Fi22KM.hom14, CFSG.KD.Fi22KM.hom15,
      CFSG.KD.Fi22KM.hom16, CFSG.KD.Fi22KM.hom17, CFSG.KD.Fi22KM.hom18, CFSG.KD.Fi22KM.hom19,
      CFSG.KD.Fi22KM.hom20, CFSG.KD.Fi22KM.hom21, CFSG.KD.Fi22KM.hom22, CFSG.KD.Fi22KM.hom23,
      CFSG.KD.Fi22KM.hom24, CFSG.KD.Fi22KM.hom25, CFSG.KD.Fi22KM.hom26]
  have hidx : ∀ q < wLen (CFSG.KD.Fi22KM.XRs r),
      Nat.shiftRight (byte (wWord (CFSG.KD.Fi22KM.XRs r)) q) 1 = wLet (wWord (CFSG.KD.Fi22KM.XRs r)) q / 2 :=
    fun q _ => Nat.shiftRight_eq_div_pow _ 1
  have hwf : ∀ q < wLen (CFSG.KD.Fi22KM.XRs r),
      wf4 (CFSG.KD.Fi22KM.FIs (Nat.shiftRight (byte (wWord (CFSG.KD.Fi22KM.XRs r)) q) 1)) = true := by
    intro q hq
    rw [hidx q hq]
    have := hlet q hq
    exact (fi_ok ⟨_, by omega⟩).1
  obtain ⟨-, hd⟩ := evalE_dec CFSG.KD.Fi22KM.FIs (CFSG.KD.Fi22KM.XRs r) hwf
  rw [Nat.eq_of_beq_eq_true hhom, dec4_one] at hd
  apply Units.ext
  rw [Units.val_one, hd.trans rfl]
  unfold bval
  rw [← Units.coeHom_apply, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q hq
  have hq' := List.mem_range.mp hq
  have hc := hlet q hq'
  simp only [Function.comp_apply, Units.coeHom_apply]
  rw [hidx q hq']
  unfold letV
  have h255 : ¬ wLet (wWord (CFSG.KD.Fi22KM.XRs r)) q = 255 := by omega
  have h6 : wLet (wWord (CFSG.KD.Fi22KM.XRs r)) q / 2 < 6 := by omega
  simp only [h255, h6, ↓reduceIte, dite_true]
  split_ifs
  · exact uG_val _
  · rw [uG_inv]
    exact uG_val _

noncomputable def psiX : XT →* GL4 :=
  PresentedGroup.toGroup (f := uG) (by
    rintro _ ⟨⟨r, hr⟩, rfl⟩
    rw [bval_map]
    rw [bval_congr (gen' := fun k => if h : k < 6 then uG ⟨k, h⟩ else 1) fun k => lift_gF uG k]
    exact psi_rel hr)

theorem psiX_gX {k : ℕ} (hk : k < 6) : psiX (gX k) = uG ⟨k, hk⟩ := by
  rw [show gX k = PresentedGroup.of ⟨k, hk⟩ from pgen_lt relsX hk]
  exact PresentedGroup.toGroup.of _

noncomputable abbrev one2 : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

theorem one2_inv : one2⁻¹ = one2 := by decide

theorem bval_par (W n : ℕ) (h : ∀ q < n, wLet W q < 12) :
    bval (fun k => if _h : k < 6 then one2 else 1) W n = one2 ^ n := by
  unfold bval
  rw [show one2 ^ n = ((List.range n).map fun _ => one2).prod by simp]
  congr 1
  apply List.map_congr_left
  intro q hq
  have hc := h q (List.mem_range.mp hq)
  unfold letV
  have h255 : ¬ wLet W q = 255 := by omega
  have h6 : wLet W q / 2 < 6 := by omega
  simp only [h255, h6, ↓reduceIte, dite_true]
  split_ifs
  · rfl
  · exact one2_inv

noncomputable def parX : XT →* Multiplicative (ZMod 2) :=
  PresentedGroup.toGroup (f := fun _ : Fin 6 => one2) (by
    rintro _ ⟨⟨r, hr⟩, rfl⟩
    rw [bval_map]
    rw [bval_congr (gen' := fun k => if _h : k < 6 then one2 else 1) fun k => lift_gF _ k]
    rw [bval_par _ _ fun q _ => letters_all (xr_ok r hr) (by norm_num) q]
    have he : wLen (CFSG.KD.Fi22KM.XRs r) % 2 = 0 := by
      interval_cases r <;> exact Nat.eq_of_beq_eq_true (by quickRfl)
    obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero he
    rw [hm, pow_mul, show one2 ^ 2 = 1 by decide, one_pow])

theorem parX_gX {k : ℕ} (hk : k < 6) : parX (gX k) = one2 := by
  rw [show gX k = PresentedGroup.of ⟨k, hk⟩ from pgen_lt relsX hk]
  exact PresentedGroup.toGroup.of _

theorem subY_ge {j : ℕ} (h : 13 ≤ j) : subY j = 0 := by
  have hb : ∀ i < 13, Nat.beq j i = false := fun i hi =>
    Bool.eq_false_iff.mpr fun h' => by
      have := Nat.eq_of_beq_eq_true h'
      omega
  have hlt : Nat.blt j 7 = false := Bool.eq_false_iff.mpr fun h' => by
    simp only [Nat.blt_eq] at h'
    omega
  simp only [subY, hb 7 (by norm_num), hb 8 (by norm_num), hb 9 (by norm_num), hb 10 (by norm_num),
    hb 11 (by norm_num), hb 12 (by norm_num), hlt]

theorem eAB_ev (k : ℕ) : bval tg (wWord (eAB (k + 1))) (wLen (eAB (k + 1))) = if h : k < 6 then ev k else 1 := by
  have e : eAB (k + 1) = subY (7 + k) := by
    unfold eAB
    congr 1
    simp only [Nat.add_eq]
    omega
  rw [e]
  split_ifs with h
  · rfl
  · rw [subY_ge (by omega)]
    rfl

noncomputable def piX : XT →* PG :=
  PresentedGroup.toGroup (f := fun t : Fin 6 => ev t) (by
    rintro _ ⟨⟨r, hr⟩, rfl⟩
    rw [bval_map]
    rw [bval_congr (gen' := fun k => bval tg (wWord (eAB (k + 1))) (wLen (eAB (k + 1)))) fun k => by
      rw [lift_gF, eAB_ev]]
    exact pi_rel r hr)

theorem piX_gX {k : ℕ} (hk : k < 6) : piX (gX k) = ev k := by
  rw [show gX k = PresentedGroup.of ⟨k, hk⟩ from pgen_lt relsX hk]
  exact PresentedGroup.toGroup.of _

end CertificateChecks.KernelFi22

end
