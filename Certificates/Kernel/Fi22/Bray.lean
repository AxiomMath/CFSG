module

public import Certificates.Kernel.Fi22.Rels
public import Certificates.Kernel.Fi22.Facts
public import CFSG.Certificates.Kernel.HOrbSound
public import CFSG.Certificates.Kernel.McLLabSound
public import CFSG.Certificates.Kernel.LceSTabSound
public import CFSG.Certificates.Kernel.Fi22.Bound.Checks.P_H_0
public import CFSG.Certificates.Kernel.Fi22.Bound.Checks.A
public import CFSG.Certificates.Kernel.Fi22.Bound.Data.A
public import CFSG.Certificates.Kernel.Common.LceSRange
import Certificates.Kernel.Co2.Intro
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelFi22

open CFSG.KC CFSG.KC.LceS CFSG.KC.HOrb CFSG.Certificates CFSG.Certificates.LCE CertificateChecks.KernelCo2

noncomputable abbrev HB : Subgroup PG :=
  Subgroup.closure ((fun j => bval tg (wWord (CFSG.KD.Fi22BP.selST j)) (wLen (CFSG.KD.Fi22BP.selST j))) ''
    {j | j < nat_lit 7})

theorem bray_index : HB.relIndex ⊤ ≠ 0 ∧ HB.relIndex ⊤ ≤ 3510 := by
  have h := lceOk_intro (nR := nat_lit 13) (nS := nat_lit 7) CFSG.KD.Fi22BP.sH1 CFSG.KD.Fi22BP.sH0
    (by quickRfl) CFSG.KD.Fi22BP.sH2 CFSG.KD.Fi22BP.sH3 (by quickRfl) (by quickRfl) (by quickRfl)
    (by quickRfl) (by quickRfl) (by quickRfl) BPfacts (by quickRfl) (by quickRfl) BPcover (by quickRfl)
  have s := lceOk_sound h tg (fun r hr => rel_val r hr)
  rw [closure_tg] at s
  exact ⟨s.1, s.2.trans (by decide)⟩

theorem bray_walk : ∃ rep : ℕ → PG, rep 0 = 1 ∧
    ∀ w x R y, x < 2 ^ 20 → walkTo CFSG.KD.Fi22BP.blk (nat_lit 82571) w x R y = true →
      rep x * bval tg (wWord w) (wLen w) * (rep y)⁻¹ ∈ HB := by
  have h := factsOk_intro (nR := nat_lit 13) (nS := nat_lit 7) (nf := nat_lit 82571)
    CFSG.KD.Fi22BP.sH1 CFSG.KD.Fi22BP.sH0 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) BPfacts
  exact HO.walkTo_sound tg HB h (fun r hr => rel_val r hr)
    (fun j hj => Subgroup.subset_closure ⟨j, hj, rfl⟩)

theorem loop2_spec (f : ℕ → Bool)
    (h : Nat.rec (motive := fun _ => Bool) true (fun h ih => andB
      (Nat.rec (motive := fun _ => Bool) true
        (fun l ih2 => andB (f (Nat.add (Nat.shiftLeft h (nat_lit 8)) l)) ih2)
        (nat_lit 256)) ih) (nat_lit 256) = true) : ∀ k < 65536, f k = true := by
  have inner : ∀ (g : ℕ → Bool) (n : ℕ),
      Nat.rec (motive := fun _ => Bool) true (fun l ih2 => andB (g l) ih2) n = true → ∀ l < n, g l = true := by
    intro g n
    induction n with
    | zero => intro _ l hl; omega
    | succ n ih =>
      intro hn l hl
      obtain ⟨h1, h2⟩ := KB.andB_true hn
      rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
      · exact ih h2 l hl
      · exact h1
  have outer := inner (fun h => Nat.rec (motive := fun _ => Bool) true
    (fun l ih2 => andB (f (Nat.add (Nat.shiftLeft h (nat_lit 8)) l)) ih2) (nat_lit 256)) (nat_lit 256) h
  intro k hk
  have e : k = Nat.add (Nat.shiftLeft (k / 256) (nat_lit 8)) (k % 256) := by
    rw [show Nat.shiftLeft (k / 256) (nat_lit 8) = k / 256 * 2 ^ 8 from Nat.shiftLeft_eq _ _]
    simp only [Nat.add_eq]
    omega
  rw [e]
  exact inner (fun l => f (Nat.add (Nat.shiftLeft (k / 256) (nat_lit 8)) l)) (nat_lit 256)
    (outer (k / 256) (by change k / 256 < 256; omega)) (k % 256) (by change k % 256 < 256; omega)

set_option maxRecDepth 20000 in
theorem wtPer0_spec {WT : ℕ → ℕ} {m P : ℕ} (h : CFSG.KC.LceSR.wtPer0 WT m P = true) :
    ∀ k < 65536, WT k = 0 ∨ ∃ k' < m, WT k = WT k' := by
  intro k hk
  have h' : orB (Nat.beq (WT k) (nat_lit 0))
      (andB (Nat.blt (Nat.mod k P) m) (Nat.beq (WT k) (WT (Nat.mod k P)))) = true :=
    loop2_spec (fun k => orB (Nat.beq (WT k) (nat_lit 0))
      (andB (Nat.blt (Nat.mod k P) m) (Nat.beq (WT k) (WT (Nat.mod k P))))) h k hk
  cases h0 : Nat.beq (WT k) (nat_lit 0)
  · rw [h0] at h'
    have h1 : andB (Nat.blt (Nat.mod k P) m) (Nat.beq (WT k) (WT (Nat.mod k P))) = true := h'
    obtain ⟨h2, h3⟩ := KB.andB_true h1
    exact Or.inr ⟨k % P, Nat.le_of_ble_eq_true h2, Nat.eq_of_beq_eq_true h3⟩
  · exact Or.inl (Nat.eq_of_beq_eq_true h0)

theorem a_cent : HB ≤ Subgroup.centralizer {tg 0} := by
  have hA := McLLab.targets_sound tg (hwords := CFSG.KD.Fi22BA.wd) (hinv := CFSG.KD.Fi22BA.inv)
    (hanc := CFSG.KD.Fi22BA.anc) (hfacts := CFSG.KD.Fi22BA.f0) (htg := CFSG.KD.Fi22BA.tg)
    (by intro r _; exact rel_all r) (wtPer0_spec (P := 8) (by quickRfl))
    ⟨by decide, by decide, by decide⟩ (by decide) (Nat.eq_of_beq_eq_true CFSG.KD.Fi22BA.one)
    ⟨by decide, by decide⟩ (by decide) (by rfl) (by rfl) (by decide) (by rfl) (by rfl) (by rfl)
  have hnT : CFSG.KD.Fi22BA.nT = 7 := Nat.eq_of_beq_eq_true CFSG.KD.Fi22BA.nt
  have hc : ∀ k < 7, bval tg (wWord (Fi22B.sub k)) (wLen (Fi22B.sub k)) * tg 0 =
      tg 0 * bval tg (wWord (Fi22B.sub k)) (wLen (Fi22B.sub k)) := by
    intro k hk
    have hb : andB (Nat.beq (CFSG.KD.Fi22BA.TW k) (commEnt (Fi22B.sub k)))
        (Nat.beq (CFSG.KD.Fi22BA.TL k) (CFSG.KC.McL.pid CFSG.KD.Fi22BA.d)) = true := by
      interval_cases k
      exacts [CFSG.KD.Fi22BA.bind0, CFSG.KD.Fi22BA.bind1, CFSG.KD.Fi22BA.bind2, CFSG.KD.Fi22BA.bind3,
        CFSG.KD.Fi22BA.bind4, CFSG.KD.Fi22BA.bind5, CFSG.KD.Fi22BA.bind6]
    obtain ⟨h1, h2⟩ := KB.andB_true hb
    have hv := hA k (by rw [hnT]; exact hk) (Nat.eq_of_beq_eq_true h2)
    rw [Nat.eq_of_beq_eq_true h1] at hv
    have he : HO.entOK (Fi22B.sub k) (nat_lit 254) (nat_lit 510) = true := by
      interval_cases k <;> quickRfl
    rw [HO.bval_commEnt tg he] at hv
    set s := bval tg (wWord (Fi22B.sub k)) (wLen (Fi22B.sub k))
    have : (tg 0)⁻¹ * s⁻¹ * tg 0 * s = (s * tg 0)⁻¹ * (tg 0 * s) := by group
    rw [this] at hv
    exact (inv_mul_eq_one.mp hv)
  rw [Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  rintro _ rfl
  exact (hc j hj).symm

end CertificateChecks.KernelFi22

end
