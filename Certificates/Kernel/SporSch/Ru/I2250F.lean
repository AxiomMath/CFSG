module

public import Certificates.Kernel.SporSch.Ru.I2250C0
public import Certificates.Kernel.SporSch.Ru.I2250C1
public import Certificates.Kernel.SporSch.Ru.I2250C2
public import Certificates.Kernel.SporSch.Ru.I2250C3
public import Certificates.Kernel.SporSch.Ru.I2250C4
public import Certificates.Kernel.SporSch.Ru.I2250C5
public import Certificates.Kernel.SporSch.Ru.I2250A0
public import Certificates.Kernel.SporSch.Ru.I2250A1
public import Certificates.Kernel.SporSch.Ru.I2250A2
public import Certificates.Kernel.SporSch.Ru.I2250A3
public import Certificates.Kernel.SporSch.Ru.I2250A4
public import Certificates.Kernel.SporSch.Ru.I2250A5
public import Certificates.Kernel.SporSch.Ru.I2250A6
public import Certificates.Kernel.SporSch.Ru.I2250A7
public import Certificates.Kernel.SporSch.Ru.SFacts
public import CFSG.Certificates.Kernel.SporSch.Ru2250Sound
public import CFSG.Certificates.Kernel.SporSch.RuZWitSound
import CFSG.Certificates.Kernel.SporSch.MathieuBTSplit
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuI

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.Ru2250
  CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG Finset

theorem beq_nat (x y : Nat) : (x == y) = Nat.beq x y := by
  cases e : Nat.beq x y
  · simp only [beq_eq_false_iff_ne]
    exact fun h => absurd (Nat.beq_eq.mpr h) (by simp [e])
  · exact beq_iff_eq.mpr (Nat.eq_of_beq_eq_true e)

theorem and_bAnd (a b : Bool) : (a && b) = Bool.rec (motive := fun _ => Bool) false b a := by
  cases a <;> rfl

theorem invsS : ruSGensA.map ruInv = rawInvs 4060 ruSGensA := rfl

theorem lev_eq : ruLevS = rawLevels 4060 (ruField4060 4) (ruBaseArr 4060 ruS4060ChainBase) := rfl

theorem c0 : rcnt (RuSS.LR 0) = 2048 := Nat.eq_of_beq_eq_true cnt0
theorem c1 : rcnt (RuSS.LR 1) = 8 := Nat.eq_of_beq_eq_true cnt1

theorem lt0 {a : Nat} (ha : a < 2048) : a < rcnt (RuSS.LR 0) := by
  rw [c0]
  exact ha

theorem lt1 {b : Nat} (hb : b < 8) : b < rcnt (RuSS.LR 1) := by
  rw [c1]
  exact hb

theorem un0 {a : Nat} (ha : a < rcnt (RuSS.LR 0)) : a < 2048 := by
  rw [c0] at ha
  exact ha

theorem un1 {b : Nat} (hb : b < rcnt (RuSS.LR 1)) : b < 8 := by
  rw [c1] at hb
  exact hb

theorem r0 {a : Nat} (ha : a < 2048) :
    ∀ x < 4060, pg 12 (mask 12) (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 0)) a)) x < 4060 :=
  tr_lt RuSS.hl (i := 0) (by norm_num) (lt0 ha)

theorem r1 {b : Nat} (hb : b < 8) :
    ∀ x < 4060, pg 12 (mask 12) (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 1)) b)) x < 4060 :=
  tr_lt RuSS.hl (i := 1) (by norm_num) (lt1 hb)

theorem rng_of_canon {P : Nat} (h : canonK 4060 12 (mask 12) (4060 * 12) P = true) :
    ∀ x < 4060, pg 12 (mask 12) P x < 4060 := fun x hx =>
  Nat.blt_eq.mp (allN_spec (range_of_canonK h) x hx)

theorem rng_of_prep {P : Nat} {g : Equiv.Perm (Fin 4060)} (h : Orb.PRep 4060 12 P g) :
    ∀ x < 4060, pg 12 (mask 12) P x < 4060 := fun x hx => by
  rw [h ⟨x, hx⟩]
  exact Fin.is_lt _

theorem prep_of {a : Array Nat} {P : Nat} {g : Equiv.Perm (Fin 4060)} (ha : a = unpack 4060 12 P)
    (h : Rep 4060 a g) : Orb.PRep 4060 12 P g := fun x => by
  rw [← Orb.unpack_get x.2, ← ha]
  exact h x

theorem tr_prep {i k : Nat} (hi : i < 2) (hk : k < rcnt (RuSS.LR i)) :
    ∃ g, Orb.PRep 4060 12 (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR i)) k)) g := by
  have hp := (Orb.head_facts RuSS.head).1
  have hbl := Orb.base_lt_of_levels RuSF2.bindsS RuSS.hl
  exact ⟨_, ((Orb.agree_levelK RuSF2.bindsS hp hbl hi (RuSS.hl i hi)).2 k hk).1⟩

theorem x_eq {i : Nat} (hi : i < 3) : ruFusXA (i + 1) = unpack 4060 12 (X i) := by
  have hw : xW i = true := by
    rcases i with _ | _ | _ | i
    exacts [xW0, xW1, xW2, absurd hi (by omega)]
  have hS : ruSGensA.size = 4 ∧ ∀ j < 4, ruSGensA[j]! = unpack 4060 12 (SG j) :=
    ⟨by simp [ruSGensA, ruSWords], fun j hj => sg_eq hj⟩
  rw [ruFusXA, invsS]
  exact (wordEqK_sound hS pSG hw).1

theorem x_rng {i : Nat} (hi : i < 3) : ∀ x < 4060, pg 12 (mask 12) (X i) x < 4060 :=
  rng_of_canon (allN_spec xC i hi)

theorem mem3 {i : Nat} (hi : i ∈ [1, 2, 3]) : ∃ k < 3, i = k + 1 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  exacts [⟨0, by omega, rfl⟩, ⟨1, by omega, rfl⟩, ⟨2, by omega, rfl⟩]

theorem h_facts {i : Nat} (hi : i < 3) : ruFusHA (i + 1) = unpack 4060 12 (H i) ∧
    compA 4060 (unpack 4060 12 (H i)) ruA0A = unpack 4060 12 (HA i) ∧
    compA 4060 (unpack 4060 12 (X i)) (unpack 4060 12 (H i)) = unpack 4060 12 (HA i) := by
  have hw : hW i = true := by
    rcases i with _ | _ | _ | i
    exacts [hW0, hW1, hW2, absurd hi (by omega)]
  unfold hW at hw
  simp only [bAnd_iff] at hw
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hw
  refine ⟨?_, by rw [a0_eq, compEqK_sound e6], compEqK_sound e7⟩
  rw [ruFusHA, (inv_of (RuW.fg_eq hi) (RuW.fgi hi)).1, RuW.fg_eq hi, a0_eq, x_eq hi,
    compEqK_sound e1, compEqK_sound e2, compEqK_sound e3, powEqRK_sound e4, compEqK_sound e5]

theorem hPL : ∀ j, 1 ≤ j → j < 593775 →
    ruTreePar[j]! = RuTree.plK j / 16 ∧ ruTreeLab[j]! = RuTree.plK j % 16 := fun j h1 h2 => by
  rw [treePar_get h1 h2, treeLab_get h1 h2]
  exact RuTree.pl_spec h1 h2

theorem zw {T0 T1 j : Nat} {g0 g1 : Equiv.Perm (Fin 4060)} (p0 : Orb.PRep 4060 12 T0 g0)
    (p1 : Orb.PRep 4060 12 T1 g1)
    (h : zwK 4060 12 (mask 12) 593775 RuTree.plK A0 A1 Z T0 T1 j = true) :
    ruZWit (compA 4060 (unpack 4060 12 T0) (unpack 4060 12 T1)) = true :=
  zwK_sound hPL (prep_of a0_eq rep_ruA0) (prep_of a1_eq rep_ruA1) (prep_of z_eq rep_ruZ)
    (fun _ hx => comp_get (rng_of_prep p1) hx)
    (rep_compA (Orb.rep_unpack p0) (Orb.rep_unpack p1)) h

theorem tot_eq (f : Nat) : tot f = ∑ k ∈ range 32, cnt k f := by
  unfold tot
  rw [CFSG.KS.SporSch.MBT.foldN_add' (f := fun k s => Nat.add s (cnt k f)) (g := fun k => cnt k f)
    (fun k s => rfl), Nat.zero_add]

theorem count_of {p : Array Nat → Bool} {P : Nat → Nat → Nat → Nat → Bool} {f : Nat}
    (hP : ∀ a < 2048, ∀ b < 8,
      p (compA 4060 (unpack 4060 12 (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 0)) a)))
        (unpack 4060 12 (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 1)) b)))) =
      P a b (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 0)) a))
        (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 1)) b)))
    (hc : ∀ k < 32, cntOK P f k = true) : count2 4060 ruLevS p = tot f := by
  have e : (2048 : Nat) = 64 * 32 := rfl
  rw [lev_eq, count2_eq RuSF2.bindsS RuSS.head RuSS.hl (le_refl 2)
    (fun a ha b hb => hP a (un0 ha) b (un1 hb)), c0, c1, e, cntK_blocks, tot_eq]
  refine sum_congr rfl fun k hk => ?_
  have h := hc k (mem_range.mp hk)
  unfold cntOK at h
  rw [PackFld.strictB_eqP, PackFld.strictB_eqP] at h
  exact Nat.eq_of_beq_eq_true h

theorem pAll_all : ∀ a < 2048, ∀ b < 8,
    pAll a b (RuSS.TR (roff 4060 (4060 * 12) (RuSS.LR 0) + a))
      (RuSS.TR (roff 4060 (4060 * 12) (RuSS.LR 1) + b)) = true := by
  have hm : ∀ m < 8, ∀ i < 512, allOKm m i = true := by
    intro m hm
    rcases m with _ | _ | _ | _ | _ | _ | _ | _ | m
    exacts [A0.all, A1.all, A2.all, A3.all, A4.all, A5.all, A6.all, A7.all,
      absurd hm (by omega)]
  have h : ∀ k < 2 * 2048, rowK RuSS.TR (roff 4060 (4060 * 12) (RuSS.LR 0))
      (roff 4060 (4060 * 12) (RuSS.LR 1)) pAll (k / 2) (4 * (k % 2)) 4 = true := by
    intro k hk
    have e : Nat.add (Nat.mul 512 (k / 512)) (k % 512) = k := Nat.div_add_mod k 512
    have h1 := hm (k / 512) (by omega) (k % 512) (Nat.mod_lt k (by norm_num))
    unfold allOKm at h1
    rw [e] at h1
    unfold allOK at h1
    rw [PackFld.strictB_eqP, PackFld.strictB_eqP] at h1
    have e1 : Nat.shiftRight k 1 = k / 2 := Nat.shiftRight_eq_div_pow k 1
    have e2 : Nat.land k 1 = k % 2 := Nat.and_one_is_mod k
    rw [e1, e2] at h1
    exact h1
  exact rowK_halves h

theorem invol (a b : Nat) (ha : a < 2048) (hb : b < 8) :
    ruIsInvolA (compA 4060 (unpack 4060 12 (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 0)) a)))
      (unpack 4060 12 (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 1)) b)))) =
    pInv a b (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 0)) a))
      (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 1)) b)) :=
  invol_eq (r0 ha) (r1 hb)

theorem fixc (a b : Nat) (hb : b < 8) :
    ruFixCount (compA 4060 (unpack 4060 12 (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 0)) a)))
      (unpack 4060 12 (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 1)) b)))) =
    fixK 4060 12 (mask 12) (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 0)) a))
      (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 1)) b)) :=
  fixedList_length (r1 hb)

theorem f92 (a b : Nat) (ha : a < 2048) (hb : b < 8) :
    (ruIsInvolA (compA 4060 (unpack 4060 12 (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 0)) a)))
      (unpack 4060 12 (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 1)) b)))) &&
      ruFixCount (compA 4060
        (unpack 4060 12 (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 0)) a)))
        (unpack 4060 12 (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 1)) b)))) == 92) =
    pF92 a b (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 0)) a))
      (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 1)) b)) := by
  rw [invol a b ha hb, fixc a b hb, beq_nat, and_bAnd]
  rfl

theorem f0 (a b : Nat) (ha : a < 2048) (hb : b < 8) :
    (ruIsInvolA (compA 4060 (unpack 4060 12 (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 0)) a)))
      (unpack 4060 12 (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 1)) b)))) &&
      ruFixCount (compA 4060
        (unpack 4060 12 (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 0)) a)))
        (unpack 4060 12 (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 1)) b)))) == 0) =
    pF0 a b (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 0)) a))
      (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 1)) b)) := by
  rw [invol a b ha hb, fixc a b hb, beq_nat, and_bAnd]
  rfl

theorem tot_of {f v : Nat} (h : Nat.beq (tot f) v = true) : tot f = v := Nat.eq_of_beq_eq_true h

theorem tots : tot 0 = 687 ∧ tot 1 = 495 ∧ tot 2 = 192 ∧ tot 3 = 256 ∧ tot 4 = 256 ∧
    tot 5 = 256 := by
  have T := totOK
  simp only [bAnd_iff] at T
  obtain ⟨t0, t1, t2, t3, t4, t5⟩ := T
  exact ⟨tot_of t0, tot_of t1, tot_of t2, tot_of t3, tot_of t4, tot_of t5⟩

theorem hall : ∀ a < rcnt (RuSS.LR 0), ∀ b < rcnt (RuSS.LR 1),
    pAll a b (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 0)) a))
      (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 1)) b)) = true :=
  fun a ha b hb => pAll_all a (un0 ha) b (un1 hb)

theorem pAll_parts {a b T0 T1 : Nat} (h : pAll a b T0 T1 = true) :
    prK 4060 12 (mask 12) T0 T1 (X 0) (X 1) = true ∧ prK 4060 12 (mask 12) T0 T1 (X 0) (X 2) = true ∧
      prK 4060 12 (mask 12) T0 T1 (X 1) (X 2) = true ∧
      Bool.rec (motive := fun _ => Bool) true
        (zwK 4060 12 (mask 12) 593775 RuTree.plK A0 A1 Z T0 T1
          (fld(ZJ, Nat.mul 20 (Nat.add (Nat.mul 8 a) b), 1048575))) (pF92 a b T0 T1) = true := by
  unfold pAll at h
  simp only [bAnd_iff] at h
  exact h

theorem cInv : count2 4060 ruLevS ruIsInvolA = 687 := by
  rw [count_of (p := ruIsInvolA) (P := pInv) (f := 0) (fun a ha b hb => invol a b ha hb) C0.all]
  exact tots.1

theorem cF92 : count2 4060 ruLevS (fun t => ruIsInvolA t && ruFixCount t == 92) = 495 := by
  rw [count_of (p := fun t => ruIsInvolA t && ruFixCount t == 92) (P := pF92) (f := 1)
    (fun a ha b hb => f92 a b ha hb) C1.all]
  exact tots.2.1

theorem cF0 : count2 4060 ruLevS (fun t => ruIsInvolA t && ruFixCount t == 0) = 192 := by
  rw [count_of (p := fun t => ruIsInvolA t && ruFixCount t == 0) (P := pF0) (f := 2)
    (fun a ha b hb => f0 a b ha hb) C2.all]
  exact tots.2.2.1

theorem aZ : all2 4060 ruLevS (fun t => !(ruIsInvolA t && ruFixCount t == 92) || ruZWit t) =
    true := by
  rw [lev_eq]
  refine all2_of_forall RuSF2.bindsS RuSS.head RuSS.hl (le_refl 2) fun a ha b hb => ?_
  obtain ⟨-, -, -, h⟩ := pAll_parts (hall a ha b hb)
  rw [f92 a b (un0 ha) (un1 hb)]
  cases e : pF92 a b (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 0)) a))
    (RuSS.TR (Nat.add (roff 4060 (4060 * 12) (RuSS.LR 1)) b))
  · rfl
  · rw [e] at h
    obtain ⟨g0, p0⟩ := tr_prep (i := 0) (by norm_num) ha
    obtain ⟨g1, p1⟩ := tr_prep (i := 1) (by norm_num) hb
    rw [zw p0 p1 h]
    rfl

theorem cX : ∀ i ∈ [1, 2, 3], count2 4060 ruLevS
    (fun s => eqA 4060 (compA 4060 s (ruFusXA i)) (compA 4060 (ruFusXA i) s)) = 256 := by
  have hT : ∀ i < 3, tot (3 + i) = 256 := fun i hi => by
    rcases i with _ | _ | _ | i
    exacts [tots.2.2.2.1, tots.2.2.2.2.1, tots.2.2.2.2.2, absurd hi (by omega)]
  have hC : ∀ i < 3, ∀ k < 32, cntOK (pCm i) (3 + i) k = true := fun i hi => by
    rcases i with _ | _ | _ | i
    exacts [C3.all, C4.all, C5.all, absurd hi (by omega)]
  intro i hi
  obtain ⟨k, hk, rfl⟩ := mem3 hi
  rw [x_eq hk, count_of (p := fun s => eqA 4060 (compA 4060 s (unpack 4060 12 (X k)))
    (compA 4060 (unpack 4060 12 (X k)) s)) (P := pCm k) (f := 3 + k)
    (fun a ha b hb => comm_eq (r0 ha) (r1 hb) (x_rng hk)) (hC k hk)]
  exact hT k hk

theorem aP : ∀ i ∈ [1, 2, 3], ∀ j ∈ [1, 2, 3], i < j → all2 4060 ruLevS
    (fun s => !eqA 4060 (compA 4060 s (ruFusXA i)) (compA 4060 (ruFusXA j) s)) = true := by
  intro i hi j hj hij
  obtain ⟨k, hk, rfl⟩ := mem3 hi
  obtain ⟨l, hl, rfl⟩ := mem3 hj
  rw [x_eq hk, x_eq hl, lev_eq]
  refine all2_of_forall RuSF2.bindsS RuSS.head RuSS.hl (le_refl 2) fun a ha b hb => ?_
  obtain ⟨h01, h02, h12, -⟩ := pAll_parts (hall a ha b hb)
  rw [pair_eq (r0 (un0 ha)) (r1 (un1 hb)) (x_rng hk)]
  have hkl : (k = 0 ∧ l = 1) ∨ (k = 0 ∧ l = 2) ∨ (k = 1 ∧ l = 2) := by omega
  rcases hkl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [h01, h02, h12]

theorem hH : ∀ i ∈ [1, 2, 3],
    eqA 4060 (compA 4060 (ruFusHA i) ruA0A) (compA 4060 (ruFusXA i) (ruFusHA i)) = true := by
  intro i hi
  obtain ⟨k, hk, rfl⟩ := mem3 hi
  rw [(h_facts hk).1, x_eq hk, (h_facts hk).2.1, (h_facts hk).2.2]
  exact CFSG.KS.Raw.eqA_self _

theorem fix0 : ruFixCount ruA0A = 0 := by
  rw [ruFixCount, a0_eq, fixedK_sound fixA0]
  rfl

theorem zA1 : ruZWit (compA 4060 ruA1A ruA1A) = true := by
  rw [a1_eq]
  exact zw (prep_of a1_eq rep_ruA1) (prep_of a1_eq rep_ruA1) zwA1

theorem q123 : powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) A1 4 (pidn 4060 12) = true ∧
    powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) A1 2 R2 = true ∧
    neIdK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) R2 = true := by
  have h := pwA1
  simp only [bAnd_iff] at h
  exact h

theorem uAB2 : compEqK 4060 12 (mask 12) (4060 * 12) A0 R2 AB2 = true ∧
    powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) AB2 14 (pidn 4060 12) = true ∧
    powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) AB2 7 R7 = true ∧
    neIdK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) R7 = true ∧
    powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) AB2 2 R2B = true ∧
    neIdK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) R2B = true := by
  have h := pAB2
  simp only [bAnd_iff] at h
  exact h

theorem s12 : compEqK 4060 12 (mask 12) (4060 * 12) A0 A1 P01 = true ∧
    powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) P01 13 (pidn 4060 12) = true := by
  have h := p13
  simp only [bAnd_iff] at h
  exact h

theorem v123 : compEqK 4060 12 (mask 12) (4060 * 12) P01 A0 P010 = true ∧
    compEqK 4060 12 (mask 12) (4060 * 12) P010 R2 Q29 = true ∧
    powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) Q29 29 (pidn 4060 12) = true := by
  have h := p29
  simp only [bAnd_iff] at h
  exact h

theorem w12 : compEqK 4060 12 (mask 12) (4060 * 12) A1 A0 P10 = true ∧
    neK 4060 12 (mask 12) (4060 * 12) P01 P10 = true := by
  have h := pNC
  simp only [bAnd_iff] at h
  exact h

theorem hab2 : ruAB2A = unpack 4060 12 AB2 := by
  rw [ruAB2A, a0_eq, a1_eq, powEqRK_sound q123.2.1, compEqK_sound uAB2.1]

theorem ord1 : eqA 4060 (compA 4060 ruA0A ruA0A) (idA 4060) = true := by
  rw [a0_eq]
  exact sqIdK_sound sqA0

theorem ord2 : eqA 4060 ruA0A (idA 4060) = false := by
  rw [a0_eq]
  exact neIdK_sound neA0

theorem ord3 : eqA 4060 (powA 4060 ruA1A 4) (idA 4060) = true := by
  rw [a1_eq, powEqRK_sound q123.1, idK_sound idOK]
  exact CFSG.KS.Raw.eqA_self _

theorem ord4 : eqA 4060 (powA 4060 ruA1A 2) (idA 4060) = false := by
  rw [a1_eq, powEqRK_sound q123.2.1]
  exact neIdK_sound q123.2.2

theorem ord5 : eqA 4060 (powA 4060 (compA 4060 ruA0A ruA1A) 13) (idA 4060) = true := by
  rw [a0_eq, a1_eq, compEqK_sound s12.1, powEqRK_sound s12.2, idK_sound idOK]
  exact CFSG.KS.Raw.eqA_self _

theorem ord6 : eqA 4060 (powA 4060 ruAB2A 14) (idA 4060) = true := by
  rw [hab2, powEqRK_sound uAB2.2.1, idK_sound idOK]
  exact CFSG.KS.Raw.eqA_self _

theorem ord7 : eqA 4060 (powA 4060 ruAB2A 7) (idA 4060) = false := by
  rw [hab2, powEqRK_sound uAB2.2.2.1]
  exact neIdK_sound uAB2.2.2.2.1

theorem ord8 : eqA 4060 (powA 4060 ruAB2A 2) (idA 4060) = false := by
  rw [hab2, powEqRK_sound uAB2.2.2.2.2.1]
  exact neIdK_sound uAB2.2.2.2.2.2

theorem ord9 : eqA 4060 (powA 4060 (compA 4060 (compA 4060 (compA 4060 ruA0A ruA1A) ruA0A)
    (powA 4060 ruA1A 2)) 29) (idA 4060) = true := by
  rw [a0_eq, a1_eq, compEqK_sound s12.1, compEqK_sound v123.1, powEqRK_sound q123.2.1,
    compEqK_sound v123.2.1, powEqRK_sound v123.2.2, idK_sound idOK]
  exact CFSG.KS.Raw.eqA_self _

theorem ord10 : eqA 4060 (compA 4060 ruA0A ruA1A) (compA 4060 ruA1A ruA0A) = false := by
  rw [a0_eq, a1_eq, compEqK_sound s12.1, compEqK_sound w12.1]
  exact neK_sound w12.2

theorem facts : count2 4060 ruLevS ruIsInvolA = 687 ∧
    count2 4060 ruLevS (fun t => ruIsInvolA t && ruFixCount t == 92) = 495 ∧
    count2 4060 ruLevS (fun t => ruIsInvolA t && ruFixCount t == 0) = 192 ∧
    all2 4060 ruLevS (fun t => !(ruIsInvolA t && ruFixCount t == 92) || ruZWit t) = true ∧
    (∀ i ∈ [1, 2, 3], count2 4060 ruLevS
      (fun s => eqA 4060 (compA 4060 s (ruFusXA i)) (compA 4060 (ruFusXA i) s)) = 256) ∧
    (∀ i ∈ [1, 2, 3], ∀ j ∈ [1, 2, 3], i < j → all2 4060 ruLevS
      (fun s => !eqA 4060 (compA 4060 s (ruFusXA i)) (compA 4060 (ruFusXA j) s)) = true) ∧
    (∀ i ∈ [1, 2, 3],
      eqA 4060 (compA 4060 (ruFusHA i) ruA0A) (compA 4060 (ruFusXA i) (ruFusHA i)) = true) ∧
    ruFixCount ruA0A = 0 ∧ ruZWit (compA 4060 ruA1A ruA1A) = true ∧
    eqA 4060 (compA 4060 ruA0A ruA0A) (idA 4060) = true ∧ eqA 4060 ruA0A (idA 4060) = false ∧
    eqA 4060 (powA 4060 ruA1A 4) (idA 4060) = true ∧
    eqA 4060 (powA 4060 ruA1A 2) (idA 4060) = false ∧
    eqA 4060 (powA 4060 (compA 4060 ruA0A ruA1A) 13) (idA 4060) = true ∧
    eqA 4060 (powA 4060 ruAB2A 14) (idA 4060) = true ∧
    eqA 4060 (powA 4060 ruAB2A 7) (idA 4060) = false ∧
    eqA 4060 (powA 4060 ruAB2A 2) (idA 4060) = false ∧
    eqA 4060 (powA 4060 (compA 4060 (compA 4060 (compA 4060 ruA0A ruA1A) ruA0A)
      (powA 4060 ruA1A 2)) 29) (idA 4060) = true ∧
    eqA 4060 (compA 4060 ruA0A ruA1A) (compA 4060 ruA1A ruA0A) = false :=
  ⟨cInv, cF92, cF0, aZ, cX, aP, hH, fix0, zA1, ord1, ord2, ord3, ord4, ord5, ord6, ord7, ord8,
    ord9, ord10⟩

end CertificateChecks.KernelSporSch.RuI

end
