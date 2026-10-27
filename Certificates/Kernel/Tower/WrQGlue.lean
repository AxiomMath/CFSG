module

public import CFSG.Certificates.Kernel.Tower.L3QSound
public import Certificates.Kernel.Tower.L3OGlue
public import Certificates.Kernel.Tower.WrEGlue
public import Certificates.Kernel.Tower.WrQChecks

public section

namespace Certificates.KernelTower

open Certificates.KernelTower CFSG.OddStandard.AltStdSmall4.Tower Subgroup

variable {e : Nat}

theorem beq_of_eq {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  rw [h]
  exact Nat.beq_refl b

theorem ch36408_eq_all (he : e < 12) : ch36408_eq e = true := by
  interval_cases e
  exacts [ch36408_eq0, ch36408_eq1, ch36408_eq2, ch36408_eq3, ch36408_eq4, ch36408_eq5,
    ch36408_eq6, ch36408_eq7, ch36408_eq8, ch36408_eq9, ch36408_eq10, ch36408_eq11]

theorem wrQ_parts (he : e < 12) : icB (wrED e 0) (wrED e 2) (wrED e 3) (wrEP e 2) = true ∧
    ∀ k < wrEP e 10, (∀ j < 16, sqB (l3M (Nat.add (wrEP e 9) k)) (l3bc (Nat.add (wrEP e 9) k) j)
        (l3G (Nat.add (wrEP e 9) k)) (l3Im (Nat.add (wrEP e 9) k) j)
        (l3g2 (Nat.add (wrEP e 9) k) j) (wrX e) = true) ∧
      cenB (l3M (Nat.add (wrEP e 9) k)) (l3bc (Nat.add (wrEP e 9) k)) (l3G (Nat.add (wrEP e 9) k))
        (wrED e 4) (l3Im (Nat.add (wrEP e 9) k)) (l3g2 (Nat.add (wrEP e 9) k)) 16 = true := by
  have h := ch36408_eq_all he
  rw [ch36408_eq, Bool.and_eq_true] at h
  refine ⟨h.1, fun k hk => ?_⟩
  have h2 := allB_eq_true.1 h.2 k hk
  rw [Bool.and_eq_true] at h2
  exact ⟨allB_eq_true.1 h2.1, h2.2⟩

variable (D : ExtData (Grp wrS)) {f : Nat}

theorem l3bc_lt (hf : f < 28)
    (hFA : ∀ c < 8192, l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c < 8192 ∧
      D.α (subModel_wr.decW c) = subModel_wr.decW (l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c))
    (hdg : subModel_wr.decW (l16 (l3P f) 1) = D.g) {j : Nat} (hj : j < 16)
    (β : CycExt D →* CycExt D)
    (hβ : ∀ i < 4, β (dec2 D subModel_wr.decW (l16 (l3G f) i)) =
      dec2 D subModel_wr.decW (l16 (l3Im f j) i)) :
    ∀ k < 16384, l3bc f j k < 16384 := by
  have M := l3_model D hf hFA hdg
  obtain ⟨hIM, hb, -⟩ := famB_parts (ch36408_l3_all hf)
  have hz : ∀ k < 16384, l3M f 2 k = k ^^^ 2 := fun _ hk => l3M_two hk
  have hzc := l3_center D hf hFA
  have hX : ∀ a < 16384, ∀ b < 16384,
      xbit (l3X f j) (l3M f a b) = xbit (l3X f j) a ^^^ xbit (l3X f j) b :=
    fun _ ha _ hb' => l3_chi D hf hFA hj ha hb'
  have hz2 : dec2 D subModel_wr.decW 2 * dec2 D subModel_wr.decW 2 = 1 := by
    rw [← M.dec_mul 2 (by omega) 2 (by omega), hz 2 (by omega)]
    exact M.dec_zero
  obtain ⟨h1, -⟩ := tgt_beta0 M hz hzc hX ((l3_parts hf).2 j hj) hIM hb β hβ hz2
  have hT := famB_table M ch36408_tree (fun _ _ _ _ => l3M_even) (ch36408_l3_all hf) _ h1
  intro k hk
  have e1 : Nat.shiftRight k 1 = k / 2 := shr1 k
  have e3 : Nat.land k 1 = k % 2 := Nat.and_one_is_mod k
  have hF := (hT (k / 2) (by omega)).1
  have hlt : Bool.rec (motive := fun _ => Nat)
      (l16 (wrL3 (Nat.add (Nat.mul 34 f) 1)) (Nat.shiftRight k 1))
      (l3M f (l16 (wrL3 (Nat.add (Nat.mul 34 f) 1)) (Nat.shiftRight k 1)) (l16 (l3P f) 2))
      (Nat.beq (Nat.land k 1) 1) < 16384 := by
    rw [e1, e3]
    cases Nat.beq (k % 2) 1
    · exact hF
    · exact M.mul_lt _ hF _ hb
  exact Nat.xor_lt_two_pow (n := 14) hlt (by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (xbit_le (l3X f j) k) with h | h <;> rw [h] <;>
      norm_num)

theorem l3_sq (hf : f < 28)
    (hFA : ∀ c < 8192, l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c < 8192 ∧
      D.α (subModel_wr.decW c) = subModel_wr.decW (l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c))
    (hdg : subModel_wr.decW (l16 (l3P f) 1) = D.g) {j : Nat} (hj : j < 16)
    {HL XT : Nat} (hH : hOK16 16384 (l3M f) 128 HL = true)
    (hsq : ∀ j < 16, sqB (l3M f) (l3bc f j) (l3G f) (l3Im f j) (l3g2 f j) XT = true)
    (hcen : cenB (l3M f) (l3bc f) (l3G f) HL (l3Im f) (l3g2 f) 16 = true)
    (D' : ExtData (CycExt D))
    (hβ : ∀ i < 4, D'.α (dec2 D subModel_wr.decW (l16 (l3G f) i)) =
      dec2 D subModel_wr.decW (l16 (l3Im f j) i)) :
    ∃ j' < 16, l3Im f j' = l3Im f j ∧ D'.g = dec2 D subModel_wr.decW (l3g2 f j') := by
  have M := l3_model D hf hFA hdg
  obtain ⟨hGU, -, -, -, -, hg2, -⟩ := tgtOK_parts ((l3_parts hf).2 j hj)
  have hbc := l3_bc D hf hFA hdg hj D'.α.toMonoidHom hβ
  have hbl := l3bc_lt D hf hFA hdg hj D'.α.toMonoidHom hβ
  set dc := dec2 D subModel_wr.decW with hdc
  have hs := hsq j hj
  simp only [sqB, Bool.and_eq_true, allB_eq_true] at hs
  obtain ⟨⟨hfix, -⟩, hgen⟩ := hs
  set g2 := l3g2 f j with hg2_def
  have hα2 : ∀ i < 4, D'.α (D'.α (dc (l16 (l3G f) i))) * dc g2 = dc g2 * dc (l16 (l3G f) i) := by
    intro i hi
    have hU := (hGU i hi).2
    have h1 := Nat.eq_of_beq_eq_true (hgen i hi).1
    have h2 : D'.α (D'.α (dc (l16 (l3G f) i))) = dc (l3bc f j (l16 (l3Im f j) i)) := by
      rw [hβ i hi]
      exact hbc _ hU
    rw [h2, ← M.dec_mul _ (hbl _ hU) _ hg2, h1, M.dec_mul _ hg2 _ (hGU i hi).1]
  set z := (dc g2)⁻¹ * D'.g with hz_def
  have hzg : ∀ i < 4, z * dc (l16 (l3G f) i) = dc (l16 (l3G f) i) * z := by
    intro i hi
    have h1 := D'.hα2 (dc (l16 (l3G f) i))
    have h2 := hα2 i hi
    rw [h1] at h2
    rw [hz_def]
    calc (dc g2)⁻¹ * D'.g * dc (l16 (l3G f) i)
        = (dc g2)⁻¹ * (D'.g * dc (l16 (l3G f) i) * D'.g⁻¹ * dc g2) * ((dc g2)⁻¹ * D'.g) := by
          group
      _ = (dc g2)⁻¹ * (dc g2 * dc (l16 (l3G f) i)) * ((dc g2)⁻¹ * D'.g) := by rw [h2]
      _ = dc (l16 (l3G f) i) * ((dc g2)⁻¹ * D'.g) := by group
  have hzc : ∀ y : CycExt D, z * y = y * z := by
    intro y
    have hy := l3_gen D hf hFA hdg y
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact hzg i hi
    | one => rw [mul_one, one_mul]
    | mul a b _ _ ha hb => rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]
    | inv a _ ha =>
      calc z * a⁻¹ = a⁻¹ * (a * z) * a⁻¹ := by group
        _ = a⁻¹ * (z * a) * a⁻¹ := by rw [ha]
        _ = a⁻¹ * z := by group
  obtain ⟨m, hm, hmz⟩ := hOK16_mem M hH z (hzc _)
  have hHL : l16 HL m < 16384 := by
    simp only [hOK16, Bool.and_eq_true, allB_eq_true] at hH
    exact Nat.le_of_ble_eq_true (hH.1.1.2 m hm).1
  have hcz : cenZ (l3M f) (l3G f) HL m = true := by
    refine allB_eq_true.2 fun i hi => ?_
    refine beq_of_eq (M.inj _ (M.mul_lt _ hHL _ (hGU i hi).1) _ (M.mul_lt _ (hGU i hi).1 _ hHL) ?_)
    rw [M.dec_mul _ hHL _ (hGU i hi).1, M.dec_mul _ (hGU i hi).1 _ hHL, hmz]
    exact hzg i hi
  have hgz : D'.g = dc (l3M f (l16 HL m) g2) := by
    rw [M.dec_mul _ hHL _ hg2, hmz, hzc (dc g2), hz_def]
    group
  rw [cenB] at hcen
  have hc := allB_eq_true.1 hcen m hm
  rw [hcz, Bool.not_true, Bool.false_or] at hc
  have hc2 := allB_eq_true.1 hc j hj
  have hlt : l3M f (l16 HL m) g2 < 16384 := M.mul_lt _ hHL _ hg2
  have hfx : Nat.beq (l3bc f j (l3M f (l16 HL m) g2)) (l3M f (l16 HL m) g2) = true := by
    refine beq_of_eq (M.inj _ (hbl _ hlt) _ hlt ?_)
    rw [← hbc _ hlt, ← hgz]
    exact D'.hαg
  rw [hfx, Bool.not_true, Bool.false_or] at hc2
  by_contra hno
  have hall : allB 16 (fun j' => !(Nat.beq (l3Im f j') (l3Im f j) &&
      Nat.beq (l3g2 f j') (l3M f (l16 HL m) g2))) = true := by
    refine allB_eq_true.2 fun j' hj' => ?_
    cases hq : (Nat.beq (l3Im f j') (l3Im f j) && Nat.beq (l3g2 f j') (l3M f (l16 HL m) g2))
    · rfl
    · rw [Bool.and_eq_true] at hq
      have h3 : D'.g = dc (l3g2 f j') := by rw [hgz, Nat.eq_of_beq_eq_true hq.2]
      exact absurd ⟨j', hj', Nat.eq_of_beq_eq_true hq.1, h3⟩ hno
  rw [hasT, hall] at hc2
  exact absurd hc2 (by decide)

theorem l3Facts_tgt (he : e < 12) {k : Nat} (hk : k < wrEP e 10) {j : Nat} (hj : j < 16)
    (hFA : ∀ c < 8192, l16 (wrA (Nat.add (wrEP e 0) 2)) c < 8192 ∧
      D.α (subModel_wr.decW c) = subModel_wr.decW (l16 (wrA (Nat.add (wrEP e 0) 2)) c))
    (hg : subModel_wr.decW (wrEP e 1) = D.g) (D' : ExtData (CycExt D))
    (hβ : ∀ i < 4, D'.α (dec2 D subModel_wr.decW (l16 (wrED e 5) i)) =
      dec2 D subModel_wr.decW (l16 (l3Im (Nat.add (wrEP e 9) k) j) i))
    (hx : D'.α (dec2 D subModel_wr.decW (l16 (wrED e 5) 0)) = dec2 D subModel_wr.decW 128) :
    L3Facts (CycExt D') (CycExt.incl D' (dec2 D subModel_wr.decW 128)) := by
  obtain ⟨hf, hP0, hP1, hG⟩ := wrE_fam he hk
  obtain ⟨hic, hq⟩ := wrQ_parts he
  obtain ⟨hsq, hcen⟩ := hq k hk
  generalize hfk : Nat.add (wrEP e 9) k = f at hsq hcen hβ
  have hfk' : wrEP e 9 + k = f := hfk
  rw [hfk'] at hf hP0 hP1 hG
  have hadd : Nat.add 2 (l16 (l3P f) 0) = Nat.add (wrEP e 0) 2 := by
    rw [hP0]
    exact Nat.add_comm _ _
  have hFA' : ∀ c < 8192, l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c < 8192 ∧
      D.α (subModel_wr.decW c) = subModel_wr.decW (l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c) := by
    rw [hadd]
    exact hFA
  have hdg' : subModel_wr.decW (l16 (l3P f) 1) = D.g := by
    rw [hP1]
    exact hg
  have hβ' : ∀ i < 4, D'.α (dec2 D subModel_wr.decW (l16 (l3G f) i)) =
      dec2 D subModel_wr.decW (l16 (l3Im f j) i) := fun i hi => by
    rw [hG i hi]
    exact hβ i hi
  have hMe : l3M f = wrEM e := by
    unfold l3M wrEM wrEm
    rw [hadd, hP1]
  have hh := ch36408_eh_all he
  have hl := ch36408_elab_all he
  simp only [ch36408_elab, ch36408_eh, Bool.and_eq_true] at hl hh
  have hH : hOK16 16384 (l3M f) 128 (wrED e 4) = true := by
    rw [hMe]
    exact hh.1.1
  obtain ⟨j', hj', hIm, hg'⟩ := l3_sq D hf hFA' hdg' hj hH hsq hcen D' hβ'
  have hβ'' : ∀ i < 4, D'.α (dec2 D subModel_wr.decW (l16 (l3G f) i)) =
      dec2 D subModel_wr.decW (l16 (l3Im f j') i) := by
    rw [hIm]
    exact hβ'
  have hout := l3_out D hf hFA' hdg' hj' D' hβ'' hg'
  have Me : IsModel (⊤ : Subgroup (CycExt D)) 16384 (wrEM e) (dec2 D subModel_wr.decW) :=
    tm_model wr_model D hFA (wrE_g_lt he) hg
  have hT : treeB 16384 4 (wrEM e) (wrED e 5) (wrED e 7) = true := hh.1.2
  have hx0 : l16 (wrED e 5) 0 < 16384 := treeB_gen hT (by norm_num)
  have hchi := ch36408_echi_all he
  have hs' := hsq j' hj'
  simp only [sqB, Bool.and_eq_true, allB_eq_true] at hs'
  obtain ⟨⟨-, hχg⟩, hgen⟩ := hs'
  obtain ⟨hGU, -, -, -, -, hg2, -⟩ := tgtOK_parts ((l3_parts hf).2 j' hj')
  have hinv : ∀ x : CycExt D, bit (wrX e) (Me.code x⁻¹) = bit (wrX e) (Me.code x) := by
    intro x
    have h1 := bit_mul Me hT hchi x⁻¹ x
    rw [inv_mul_cancel, Me.code_one, (chiB_parts hchi).1] at h1
    rcases bit_cases (wrX e) (Me.code x⁻¹) with ha | ha <;>
      rcases bit_cases (wrX e) (Me.code x) with hb | hb <;> rw [ha, hb] at h1 <;> rw [ha, hb] <;>
      first | rfl | exact absurd h1 (by decide)
  have hχα : ∀ x : CycExt D, bit (wrX e) (Me.code (D'.α x)) = bit (wrX e) (Me.code x) := by
    intro x
    have hy := l3_gen D hf hFA' hdg' x
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      rw [hβ'' i hi, Me.code_dec (hGU i hi).2, Me.code_dec (hGU i hi).1]
      exact Nat.eq_of_beq_eq_true (hgen i hi).2
    | one => rw [map_one]
    | mul a b _ _ ha hb => rw [map_mul, bit_mul Me hT hchi, bit_mul Me hT hchi, ha, hb]
    | inv a _ ha => rw [map_inv, hinv, hinv, ha]
  have hgχ : bit (wrX e) (Me.code D'.g) = 0 := by
    rw [hg', Me.code_dec hg2]
    exact Nat.eq_of_beq_eq_true hχg
  have htχ : bit (wrX e) (Me.code (dec2 D subModel_wr.decW 128)) = 1 := by
    rw [Me.code_dec (by norm_num)]
    exact (chiB_parts hchi).2.1
  exact l3Facts_of_parts hx (fun x => bit (wrX e) (Me.code x)) (fun x => bit_cases _ _)
    (bit_mul Me hT hchi) hχα hgχ htχ
    (pcB_sound Me rfl hT (by norm_num) hx0 (ch36408_eord_all he) hl.1 hl.2 (ch36408_epc_all he))
    (icB_sound Me rfl hT (ch36408_eord_all he) hl.1 hl.2 hic) hout

end Certificates.KernelTower
